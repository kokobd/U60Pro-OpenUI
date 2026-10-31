//! AP readiness and one bounded recovery of the Qualcomm CSA/key-install stall.
//!
//! Callers must hold the shared radio-operation lock. Recovery can temporarily
//! pin a mismatched AP's runtime channel; UCI, credentials and channel geometry
//! are unchanged. A healthy upstream does not prove hotspot clients can associate.
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

const STABLE_MISMATCH: Duration = Duration::from_secs(15);
const POST_CHANGE_WINDOW: Duration = Duration::from_secs(120);
const SAMPLE_TIMEOUT: Duration = Duration::from_secs(12);
const RECOVERY_TIMEOUT: Duration = Duration::from_secs(30);
const CHANNEL_RESTORE_TIMEOUT: Duration = Duration::from_secs(15);
const COMMAND_TIMEOUT: Duration = Duration::from_secs(2);
const POLL: Duration = Duration::from_millis(300);
const LIMIT: usize = 2 * 1024 * 1024;
const CTRL: &str = "/data/vendor/wifi/hostapd";

#[derive(Clone, Debug, PartialEq, Eq)]
struct Ap {
    iface: String,
    intended: bool,
    state: String,
    host_frequency: Option<u32>,
    driver_frequency: Option<u32>,
    // Keep SSIDs out of observations and diagnostic messages.
    ssid_matches: Option<bool>,
}

impl Ap {
    fn ready(&self) -> bool {
        if self.intended {
            self.state == "ENABLED"
                && self.ssid_matches == Some(true)
                && self.host_frequency.is_some()
                && self.host_frequency == self.driver_frequency
        } else {
            matches!(self.state.as_str(), "DISABLED" | "MISSING")
        }
    }

    fn observed_transition(&self) -> bool {
        !self.ready()
            && (matches!(
                self.state.as_str(),
                "DISABLED" | "MISSING" | "ACS" | "DFS" | "COUNTRY_UPDATE" | "UNINITIALIZED"
            ) || (self.state == "ENABLED"
                && (!self.intended
                    || self.ssid_matches == Some(false)
                    || (self.host_frequency.is_some()
                        && self.driver_frequency.is_some()
                        && self.host_frequency != self.driver_frequency))))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Sample {
    idle: bool,
    stock_known: bool,
    // Both main APs, including those intentionally disabled.
    aps: Vec<Ap>,
}

impl Sample {
    fn ready(&self) -> bool {
        self.stock_known && self.idle && self.aps.iter().all(Ap::ready)
    }

    fn mismatched(&self) -> bool {
        self.stock_known
            && self.idle
            && self.aps.iter().any(|ap| ap.intended)
            && self.aps.iter().all(|ap| {
                if ap.intended {
                    ap.state == "ENABLED"
                        && ap.host_frequency.is_some()
                        && ap.driver_frequency.is_some()
                } else {
                    matches!(ap.state.as_str(), "DISABLED" | "MISSING")
                }
            })
            && self
                .aps
                .iter()
                .any(|ap| ap.intended && ap.host_frequency != ap.driver_frequency)
    }
}

struct CsaEvidence {
    uptime_us: u64,
    log_watermark_us: u64,
    newest_event_us: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RuntimeIdentity {
    iface: String,
    // Device, inode and modification time identify socket replacement.
    socket: Option<(u64, u64, i64, i64)>,
    ifindex: Option<u32>,
}

type Generation = Vec<RuntimeIdentity>;

struct Pending {
    since: Instant,
    sample: Sample,
    fresh_error: bool,
}

struct PostChange {
    until: Instant,
    interfaces: Vec<String>,
    fingerprint: [u8; 32],
}

struct ChannelPlan {
    iface: String,
    target: u16,
    original: u16,
}

/// One monitor belongs to one supervisor lifetime. Replacing it explicitly after
/// a coordinated settings operation also establishes a new kernel-log baseline.
/// Outside the verified post-change window, a new CSA error is also required.
/// Historical errors and unreadable samples never authorize a restart.
#[derive(Default)]
pub struct Monitor {
    watermark_us: Option<u64>,
    last_uptime_us: Option<u64>,
    pending: Option<Pending>,
    post_change: Option<PostChange>,
    attempted: bool,
    failure: Option<String>,
    diagnostic_once: u8,
    candidate_diagnostics: u8,
}

impl Monitor {
    fn revoke_window(&mut self, reason: &'static str) {
        if self.post_change.take().is_some() {
            eprintln!("wifi-radio: window-revoked reason={reason}");
        }
    }

    fn window_diagnostic_once(&mut self, bit: u8, event: &'static str) {
        if self.post_change.is_some() && self.diagnostic_once & bit == 0 {
            self.diagnostic_once |= bit;
            eprintln!("wifi-radio: {event}");
        }
    }

    fn candidate_diagnostic(&mut self, event: &'static str, sample: Option<&Sample>) {
        if self.post_change.is_none() || self.candidate_diagnostics >= 8 {
            return;
        }
        self.candidate_diagnostics += 1;
        if let Some(sample) = sample {
            let aps: Vec<_> = sample
                .aps
                .iter()
                .enumerate()
                .map(|(index, ap)| {
                    format!(
                        "ap{index}:intended={},enabled={},host={:?},driver={:?},ssid_match={:?}",
                        ap.intended,
                        ap.state == "ENABLED",
                        ap.host_frequency,
                        ap.driver_frequency,
                        ap.ssid_matches
                    )
                })
                .collect();
            eprintln!(
                "wifi-radio: mismatch-candidate {event} stock_known={} idle={} {}",
                sample.stock_known,
                sample.idle,
                aps.join(" ")
            );
        } else {
            eprintln!("wifi-radio: mismatch-candidate {event}");
        }
        if self.candidate_diagnostics == 8 {
            eprintln!("wifi-radio: mismatch-candidate diagnostics capped for this window");
        }
    }

    /// Call under the radio-operation lock after a settings hold is released and
    /// before the first resumed relay step. A verified ready configuration gets
    /// a short settling window; this does not reset the recovery/error latch.
    pub fn after_hotspot_change(&mut self) -> Result<(), String> {
        self.after_hotspot_change_with(&mut Native)
    }

    fn after_hotspot_change_with(&mut self, backend: &mut impl Backend) -> Result<(), String> {
        self.revoke_window("rearmed");
        self.pending = None;
        self.diagnostic_once = 0;
        self.candidate_diagnostics = 0;
        if let Some(error) = &self.failure {
            return Err(error.clone());
        }
        let deadline = backend.now() + SAMPLE_TIMEOUT;
        let sample = backend.sample(deadline)?;
        if !sample.ready() {
            return Err("Hotspot readiness was not verified before resuming Wi-Fi relay".into());
        }
        let interfaces: Vec<_> = sample
            .aps
            .iter()
            .filter(|ap| ap.intended)
            .map(|ap| ap.iface.clone())
            .collect();
        let fingerprint = backend.fingerprint(&interfaces, deadline)?;
        if backend.sample(deadline)? != sample {
            return Err("Hotspot state changed before resuming Wi-Fi relay".into());
        }
        self.post_change = Some(PostChange {
            until: backend.now() + POST_CHANGE_WINDOW,
            interfaces,
            fingerprint,
        });
        eprintln!(
            "wifi-radio: window-armed seconds=120 intended_aps={}",
            self.post_change
                .as_ref()
                .map_or(0, |window| window.interfaces.len())
        );
        Ok(())
    }

    fn post_change_matches(&mut self, backend: &mut impl Backend, deadline: Instant) -> bool {
        let Some(window) = &self.post_change else {
            return false;
        };
        let reason = if backend.now() >= window.until {
            Some("expired")
        } else {
            match backend.fingerprint(&window.interfaces, deadline) {
                Err(_) => Some("fingerprint-read-failed"),
                Ok(current) if current != window.fingerprint => Some("fingerprint-changed"),
                Ok(_) if backend.now() >= window.until => Some("expired"),
                Ok(_) => None,
            }
        };
        if let Some(reason) = reason {
            self.revoke_window(reason);
            return false;
        }
        true
    }

    /// Establish a read-only baseline before a coordinated operation can emit
    /// CSA errors. A failed read makes the next successful check baseline only.
    /// This does not reset a spent recovery allowance or a latched error.
    pub fn baseline(&mut self) {
        self.baseline_with(&mut Native);
    }

    fn baseline_with(&mut self, backend: &mut impl Backend) {
        if self.pending.is_some() {
            self.candidate_diagnostic("reset-baseline", None);
        }
        self.pending = None;
        match backend.evidence(backend.now() + SAMPLE_TIMEOUT) {
            Ok(evidence) => {
                self.watermark_us = Some(evidence.log_watermark_us);
                self.last_uptime_us = Some(evidence.uptime_us);
            }
            Err(_) => {
                self.watermark_us = None;
                self.last_uptime_us = None;
            }
        }
    }

    /// Called under the radio-operation lock. A notice means recovery completed;
    /// an error is latched after an attempted recovery fails or the fault recurs.
    /// Transient/busy/unreadable observations return `Ok(None)` and break the
    /// stable-mismatch window. They never spend the recovery allowance.
    pub fn check(&mut self) -> Result<Option<String>, String> {
        self.check_with(&mut Native)
    }

    fn check_with(&mut self, backend: &mut impl Backend) -> Result<Option<String>, String> {
        if let Some(error) = &self.failure {
            return Err(error.clone());
        }
        let deadline = backend.now() + SAMPLE_TIMEOUT;
        let post_change = self.post_change_matches(backend, deadline);
        let evidence = match backend.evidence(deadline) {
            Ok(value) => value,
            Err(_) => {
                self.window_diagnostic_once(1, "evidence-read-failed during-window");
                if self.pending.is_some() {
                    self.candidate_diagnostic("reset-evidence-read-failed", None);
                }
                self.pending = None;
                return Ok(None);
            }
        };
        let rebooted = self
            .last_uptime_us
            .is_some_and(|previous| evidence.uptime_us < previous);
        let log_restarted = self
            .watermark_us
            .is_some_and(|previous| evidence.log_watermark_us < previous);
        let fresh = !rebooted
            && !log_restarted
            && self.watermark_us.is_some_and(|previous| {
                evidence
                    .newest_event_us
                    .is_some_and(|event| event > previous)
            });
        if rebooted || log_restarted {
            self.window_diagnostic_once(4, "evidence-clock-restarted during-window");
            if self.pending.is_some() {
                self.candidate_diagnostic("reset-evidence-clock", None);
            }
            self.pending = None;
        }
        // Kernel printk timestamps and uptime can treat suspend differently.
        // Compare log events only with the previous log's own timestamp clock.
        self.watermark_us = Some(evidence.log_watermark_us);
        self.last_uptime_us = Some(evidence.uptime_us);
        let sample = match backend.sample(deadline) {
            Ok(value) if value.mismatched() => value,
            Ok(value) => {
                if !value.stock_known {
                    self.window_diagnostic_once(16, "stock-status-unreadable during-window");
                } else if !value.idle {
                    self.window_diagnostic_once(32, "stock-service-busy during-window");
                } else if !value.ready() {
                    self.window_diagnostic_once(64, "ap-runtime-not-ready during-window");
                }
                if self.pending.is_some() {
                    self.candidate_diagnostic("reset-no-longer-mismatched", Some(&value));
                }
                self.pending = None;
                return Ok(None);
            }
            Err(_) => {
                self.window_diagnostic_once(2, "sample-read-failed during-window");
                if self.pending.is_some() {
                    self.candidate_diagnostic("reset-sample-read-failed", None);
                }
                self.pending = None;
                return Ok(None);
            }
        };
        let now = backend.now();
        if self
            .pending
            .as_ref()
            .is_some_and(|pending| pending.sample == sample)
        {
            self.pending.as_mut().unwrap().fresh_error |= fresh;
        } else {
            self.candidate_diagnostic(
                if self.pending.is_some() {
                    "reset-sample-changed"
                } else {
                    "start"
                },
                Some(&sample),
            );
            self.pending = Some(Pending {
                since: now,
                sample: sample.clone(),
                fresh_error: fresh,
            });
            return Ok(None);
        }
        let pending = self.pending.as_ref().unwrap();
        let fresh_error = pending.fresh_error;
        let stable_since = pending.since;
        if self
            .post_change
            .as_ref()
            .is_some_and(|window| now >= window.until)
        {
            self.revoke_window("expired-during-sample");
        }
        let post_change = post_change
            && self.post_change.is_some()
            && sample
                .aps
                .iter()
                .all(|ap| !ap.intended || ap.ssid_matches == Some(true));
        if now.duration_since(stable_since) < STABLE_MISMATCH || !(fresh_error || post_change) {
            return Ok(None);
        }
        if self.attempted {
            eprintln!("wifi-radio: recovery-recurrence-latched");
            return self.fail("The Wi-Fi channel fault returned after one recovery; automatic recovery is stopped");
        }
        let interfaces: Vec<_> = sample
            .aps
            .iter()
            .filter(|ap| ap.intended)
            .map(|ap| ap.iface.clone())
            .collect();
        let targets: Vec<_> = sample.aps.iter()
            .filter(|ap| ap.intended && ap.host_frequency != ap.driver_frequency)
            .map(|ap| {
                let target = ap.host_frequency.and_then(target_channel)
                    .ok_or_else(|| "Wi-Fi recovery target is outside the supported non-DFS channels; no reset was attempted".to_string())?;
                Ok((ap.iface.clone(), target))
            }).collect::<Result<_, String>>()?;
        let before = match backend.fingerprint(&interfaces, deadline) {
            Ok(value) => value,
            Err(_) => {
                self.window_diagnostic_once(8, "recovery-fingerprint-read-failed during-window");
                self.candidate_diagnostic("reset-preflight-fingerprint", None);
                self.pending = None;
                return Ok(None);
            }
        };
        let channels: Vec<_> = targets
            .into_iter()
            .map(|(iface, target)| {
                let original = backend.configured_channel(&iface, deadline)?;
                if original != 0 && !supported_channel(original) {
                    return Err(
                        "Original Wi-Fi channel policy is unsupported; no reset was attempted"
                            .into(),
                    );
                }
                Ok(ChannelPlan {
                    iface,
                    target,
                    original,
                })
            })
            .collect::<Result<_, String>>()?;
        // The samples above are observations, not a claim on the stock service.
        // Recheck immediately before the first write as it does not share our lock.
        match backend.sample(deadline) {
            Ok(current) if current == sample => {}
            _ => {
                self.candidate_diagnostic("reset-preflight-sample-changed-or-unreadable", None);
                self.pending = None;
                return Ok(None);
            }
        }
        match backend.fingerprint(&interfaces, deadline) {
            Ok(current) if current == before => {}
            result => {
                self.pending = None;
                self.revoke_window(if result.is_err() {
                    "preflight-fingerprint-read-failed"
                } else {
                    "preflight-fingerprint-changed"
                });
                return Ok(None);
            }
        }
        // The settling window grants permission only for the captured settings,
        // including immediately before the first mutation. A fresh CSA error
        // remains an independent background-recovery gate.
        let window_still_matches = self.post_change_matches(backend, deadline)
            && self
                .post_change
                .as_ref()
                .is_some_and(|window| window.fingerprint == before);
        if !fresh_error && !window_still_matches {
            self.candidate_diagnostic("reset-window-no-longer-authorizes", None);
            self.pending = None;
            return Ok(None);
        }
        self.attempted = true;
        self.pending = None;
        eprintln!(
            "wifi-radio: recovery-attempt trigger={} active_aps={} channel_changes={}",
            if fresh_error {
                "fresh-csa"
            } else {
                "post-change-window"
            },
            interfaces.len(),
            channels.len()
        );
        if let Err(error) = recover(backend, &interfaces, &channels, before) {
            eprintln!("wifi-radio: recovery-failed");
            return self.fail(&error);
        }
        eprintln!("wifi-radio: recovery-succeeded");
        Ok(Some(
            "Recovered the Wi-Fi channel-switch stall; saved settings are unchanged".into(),
        ))
    }

    fn fail(&mut self, error: &str) -> Result<Option<String>, String> {
        self.failure = Some(error.into());
        Err(error.into())
    }
}

/// Request a stock reload and verify a runtime transition before accepting two
/// ready samples. An unchanged, already-ready runtime cannot acknowledge reload.
pub fn reload_and_wait(timeout: Duration) -> Result<(), String> {
    let mut backend = Native;
    let deadline = backend.now() + timeout;
    reload_and_wait_with(&mut backend, deadline)
}

fn reload_and_wait_with(backend: &mut impl Backend, deadline: Instant) -> Result<(), String> {
    let initial = backend.sample(deadline)?;
    let interfaces: Vec<_> = initial.aps.iter().map(|ap| ap.iface.clone()).collect();
    let before = backend.generation(&interfaces, deadline)?;
    backend.reload(deadline)?;
    let mut transitioned = vec![false; interfaces.len()];
    let mut global_transition = false;
    let mut previous = None;
    loop {
        remaining(deadline, backend.now())?;
        let sample = backend.sample(deadline)?;
        if sample.aps.iter().map(|ap| &ap.iface).ne(interfaces.iter()) {
            return Err("Hotspot interface mapping changed during reload".into());
        }
        let current = backend.generation(&interfaces, deadline);
        global_transition |= sample.stock_known && !sample.idle;
        for (index, ap) in sample.aps.iter().enumerate() {
            transitioned[index] |= ap.observed_transition()
                || current
                    .as_ref()
                    .is_ok_and(|current| current.get(index) != before.get(index));
        }
        let required: Vec<_> = initial
            .aps
            .iter()
            .enumerate()
            .filter(|(_, ap)| ap.intended || !ap.ready())
            .map(|(index, _)| index)
            .collect();
        let generation_seen = global_transition
            || if required.is_empty() {
                transitioned.iter().any(|changed| *changed)
            } else {
                required.iter().all(|index| transitioned[*index])
            };
        // Missing is a concrete marker value; permission/I/O failures are not.
        if let (true, Ok(current)) = (generation_seen && sample.ready(), current) {
            let ready = (sample, current);
            if previous.as_ref() == Some(&ready) {
                return Ok(());
            }
            previous = Some(ready);
        } else {
            previous = None;
        }
        backend.sleep(POLL.min(remaining(deadline, backend.now())?));
    }
}

// Ready means consistent AP intent, SSID and primary frequency on two samples;
// it does not prove a client has associated.
fn wait_ready_with(backend: &mut impl Backend, deadline: Instant) -> Result<(), String> {
    let mut previous: Option<Sample> = None;
    loop {
        remaining(deadline, backend.now())?;
        let sample = backend.sample(deadline)?;
        if sample.ready() {
            if previous.as_ref() == Some(&sample) {
                return Ok(());
            }
            previous = Some(sample);
        } else {
            previous = None;
        }
        backend.sleep(POLL.min(remaining(deadline, backend.now())?));
    }
}

fn recover(
    backend: &mut impl Backend,
    interfaces: &[String],
    channels: &[ChannelPlan],
    before: [u8; 32],
) -> Result<(), String> {
    let deadline = backend.now() + RECOVERY_TIMEOUT;
    let mut channel_set_attempted = false;
    let result = (|| {
        // CSA completion is shared: never enable the first AP while the second
        // AP is still being stopped. Restore every original active AP on error.
        for iface in interfaces {
            backend.control(iface, "DISABLE", deadline)?;
        }
        loop {
            remaining(deadline, backend.now())?;
            let mut all_disabled = true;
            for iface in interfaces {
                all_disabled &= backend.state(iface, deadline)? == "DISABLED";
            }
            if all_disabled {
                break;
            }
            backend.sleep(POLL.min(remaining(deadline, backend.now())?));
        }
        if backend.fingerprint(interfaces, deadline)? != before {
            return Err("Wi-Fi settings changed during recovery".to_string());
        }
        for channel in channels {
            // Even a rejected SET can mutate hostapd before config validation.
            channel_set_attempted = true;
            backend.set_channel(&channel.iface, channel.target, deadline)?;
        }
        for iface in interfaces {
            backend.control(iface, "ENABLE", deadline)?;
        }
        wait_ready_with(backend, deadline)?;
        if backend.fingerprint(interfaces, deadline)? != before {
            return Err("Wi-Fi settings changed during recovery".to_string());
        }
        Ok(())
    })();
    if result.is_ok() {
        return Ok(());
    }
    if channel_set_attempted {
        let restore_deadline = backend.now() + CHANNEL_RESTORE_TIMEOUT;
        for iface in interfaces {
            let _ = backend.control(iface, "DISABLE", restore_deadline);
        }
        let state_deadline = restore_deadline - COMMAND_TIMEOUT * channels.len() as u32;
        let all_disabled = loop {
            if remaining(state_deadline, backend.now()).is_err() {
                break false;
            }
            let mut stopped = true;
            for iface in interfaces {
                stopped &= backend
                    .state(iface, state_deadline)
                    .is_ok_and(|state| state == "DISABLED");
            }
            if stopped {
                break true;
            }
            let Ok(left) = remaining(state_deadline, backend.now()) else {
                break false;
            };
            backend.sleep(POLL.min(left));
        };
        if all_disabled {
            for channel in channels {
                let _ = backend.set_channel(&channel.iface, channel.original, restore_deadline);
            }
        }
    }
    // A fresh small budget guarantees an enable attempt for every original AP,
    // including when the recovery or channel-policy restoration timed out.
    let enable_deadline = backend.now() + COMMAND_TIMEOUT * (interfaces.len() as u32 + 1);
    for iface in interfaces {
        let _ = backend.control(iface, "ENABLE", enable_deadline);
    }
    Err("Wi-Fi recovery failed; original channel-policy restoration and re-enabling all previously active APs were attempted; automatic recovery is stopped".into())
}

fn target_channel(frequency: u32) -> Option<u16> {
    if let Some(channel) = (1u16..=13).find(|channel| 2407 + u32::from(*channel) * 5 == frequency) {
        return Some(channel);
    }
    [36u16, 40, 44, 48, 149, 153, 157, 161, 165]
        .into_iter()
        .find(|channel| 5000 + u32::from(*channel) * 5 == frequency)
}

fn supported_channel(channel: u16) -> bool {
    (1..=13).contains(&channel) || [36, 40, 44, 48, 149, 153, 157, 161, 165].contains(&channel)
}

trait Backend {
    fn now(&self) -> Instant;
    fn sleep(&mut self, duration: Duration);
    fn evidence(&mut self, deadline: Instant) -> Result<CsaEvidence, String>;
    fn sample(&mut self, deadline: Instant) -> Result<Sample, String>;
    fn generation(
        &mut self,
        interfaces: &[String],
        deadline: Instant,
    ) -> Result<Generation, String>;
    fn reload(&mut self, deadline: Instant) -> Result<(), String>;
    fn fingerprint(&mut self, interfaces: &[String], deadline: Instant)
        -> Result<[u8; 32], String>;
    fn control(&mut self, iface: &str, command: &str, deadline: Instant) -> Result<(), String>;
    fn state(&mut self, iface: &str, deadline: Instant) -> Result<String, String>;
    fn configured_channel(&mut self, iface: &str, deadline: Instant) -> Result<u16, String>;
    fn set_channel(&mut self, iface: &str, channel: u16, deadline: Instant) -> Result<(), String>;
}

fn remaining(deadline: Instant, now: Instant) -> Result<Duration, String> {
    deadline
        .checked_duration_since(now)
        .filter(|duration| !duration.is_zero())
        .ok_or_else(|| "Timed out waiting for Wi-Fi readiness".into())
}

struct Native;

impl Backend for Native {
    fn now(&self) -> Instant {
        Instant::now()
    }

    fn sleep(&mut self, duration: Duration) {
        std::thread::sleep(duration);
    }

    fn evidence(&mut self, deadline: Instant) -> Result<CsaEvidence, String> {
        let uptime = read_small(Path::new("/proc/uptime"), 128)?;
        let uptime_us = std::str::from_utf8(&uptime)
            .ok()
            .and_then(|value| value.split_whitespace().next())
            .and_then(decimal_us)
            .ok_or("Cannot read the Wi-Fi diagnostic clock")?;
        let log = output("dmesg", &[], deadline)?;
        let log = std::str::from_utf8(&log).map_err(|_| "Cannot read Wi-Fi diagnostic events")?;
        let log_watermark_us = log
            .lines()
            .filter_map(kernel_timestamp)
            .max()
            .ok_or("Cannot read the Wi-Fi diagnostic clock")?;
        let newest_event_us = log.lines().filter_map(csa_timestamp).max();
        Ok(CsaEvidence {
            uptime_us,
            log_watermark_us,
            newest_event_us,
        })
    }

    fn sample(&mut self, deadline: Instant) -> Result<Sample, String> {
        let wireless = output("uci", &["-q", "show", "wireless"], deadline)?;
        let wireless =
            std::str::from_utf8(&wireless).map_err(|_| "Cannot read Wi-Fi configuration")?;
        let mbb = match fs::metadata("/etc/config/zte_mbb") {
            Ok(_) => output("uci", &["-q", "show", "zte_mbb"], deadline)?,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Vec::new(),
            Err(_) => return Err("Cannot read Wi-Fi configuration".into()),
        };
        let mbb = std::str::from_utf8(&mbb).map_err(|_| "Cannot read Wi-Fi configuration")?;
        let mut aps = intended_aps(wireless, mbb)?;
        // Runtime objects routinely disappear during a stock reload. Keep their
        // absence distinct from unreadable intent so readiness can wait for them.
        let stock = output(
            "ubus",
            &["-t", "2", "call", "zwrt_wlan", "status", "{}"],
            deadline,
        )
        .ok()
        .and_then(|status| serde_json::from_slice::<Value>(&status).ok())
        .and_then(|status| stock_idle(&status).ok());
        let idle = stock == Some(true);
        let stock_known = stock.is_some();
        if !idle {
            return Ok(Sample {
                idle,
                stock_known,
                aps,
            });
        }
        for (ap, band) in aps.iter_mut().zip(["2g", "5g"]) {
            let status = match hostapd(&ap.iface, "STATUS", deadline) {
                Ok(status) => status,
                Err(_) => {
                    if runtime_absent(&ap.iface) {
                        ap.state = "MISSING".into();
                    }
                    continue;
                }
            };
            ap.state = value(&status, "state").unwrap_or("UNKNOWN").to_string();
            if ap.intended && ap.state == "ENABLED" {
                let expected = expected_ssid(wireless, band)?;
                ap.ssid_matches = raw_value(&status, "ssid[0]")
                    .map(|reported| reported == hostapd_ssid_text(&expected));
                ap.host_frequency = value(&status, "freq")
                    .and_then(|value| value.parse::<u32>().ok())
                    .filter(|value| (2400..=7125).contains(value));
                ap.driver_frequency = output("iw", &["dev", &ap.iface, "info"], deadline)
                    .ok()
                    .and_then(|info| String::from_utf8(info).ok())
                    .and_then(|info| driver_frequency(&info).ok());
            }
        }
        Ok(Sample {
            idle,
            stock_known,
            aps,
        })
    }

    fn generation(
        &mut self,
        interfaces: &[String],
        deadline: Instant,
    ) -> Result<Generation, String> {
        interfaces
            .iter()
            .map(|iface| {
                remaining(deadline, self.now())?;
                if !valid_iface(iface) {
                    return Err("Invalid hotspot interface".into());
                }
                let socket = match fs::symlink_metadata(Path::new(CTRL).join(iface)) {
                    Ok(meta) if meta.file_type().is_socket() => {
                        Some((meta.dev(), meta.ino(), meta.mtime(), meta.mtime_nsec()))
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
                    _ => return Err("Cannot identify hotspot runtime generation".into()),
                };
                let path = Path::new("/sys/class/net").join(iface).join("ifindex");
                let ifindex = match File::open(path) {
                    Ok(file) => {
                        let mut text = String::new();
                        file.take(129)
                            .read_to_string(&mut text)
                            .map_err(|_| "Cannot identify hotspot runtime generation")?;
                        Some(
                            text.trim()
                                .parse::<u32>()
                                .ok()
                                .filter(|value| *value > 0)
                                .filter(|_| text.len() <= 128)
                                .ok_or("Cannot identify hotspot runtime generation")?,
                        )
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
                    Err(_) => return Err("Cannot identify hotspot runtime generation".into()),
                };
                Ok(RuntimeIdentity {
                    iface: iface.clone(),
                    socket,
                    ifindex,
                })
            })
            .collect()
    }

    fn reload(&mut self, deadline: Instant) -> Result<(), String> {
        // The shared ubus helper has a ten-second process bound.
        if remaining(deadline, self.now())? < Duration::from_secs(10) {
            return Err("Insufficient time to request and verify Wi-Fi reload".into());
        }
        crate::ubus::call("zwrt_wlan", "reload", Some("{}"))
            .map(|_| ())
            .map_err(|_| "Cannot request Wi-Fi reload".into())
    }

    fn fingerprint(
        &mut self,
        interfaces: &[String],
        deadline: Instant,
    ) -> Result<[u8; 32], String> {
        let mut hash = Sha256::new();
        let mut paths = vec![PathBuf::from("/etc/config/wireless")];
        match fs::metadata("/etc/config/zte_mbb") {
            Ok(_) => paths.push(PathBuf::from("/etc/config/zte_mbb")),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => return Err("Cannot verify Wi-Fi settings".into()),
        }
        for iface in interfaces {
            if !valid_iface(iface) {
                return Err("Invalid hotspot interface".into());
            }
            paths.push(PathBuf::from(format!(
                "/data/vendor/wifi/hostapd-{iface}.conf"
            )));
        }
        for path in paths {
            remaining(deadline, self.now())?;
            let data = read_small(&path, LIMIT)?;
            hash.update(path.as_os_str().as_encoded_bytes());
            hash.update((data.len() as u64).to_le_bytes());
            hash.update(data);
        }
        Ok(hash.finalize().into())
    }

    fn control(&mut self, iface: &str, command: &str, deadline: Instant) -> Result<(), String> {
        if !matches!(command, "DISABLE" | "ENABLE") {
            return Err("Unsupported hotspot operation".into());
        }
        if hostapd(iface, command, deadline)?.trim() != "OK" {
            return Err("Hotspot rejected the runtime operation".into());
        }
        Ok(())
    }

    fn state(&mut self, iface: &str, deadline: Instant) -> Result<String, String> {
        let status = hostapd(iface, "STATUS", deadline)?;
        value(&status, "state")
            .map(str::to_string)
            .ok_or_else(|| "Cannot read hotspot state".into())
    }

    fn configured_channel(&mut self, iface: &str, deadline: Instant) -> Result<u16, String> {
        remaining(deadline, self.now())?;
        if !valid_iface(iface) {
            return Err("Invalid hotspot interface".into());
        }
        let config = read_small(
            &PathBuf::from(format!("/data/vendor/wifi/hostapd-{iface}.conf")),
            LIMIT,
        )?;
        let config = std::str::from_utf8(&config)
            .map_err(|_| "Cannot read original hotspot channel policy")?;
        configured_channel(config)
    }

    fn set_channel(&mut self, iface: &str, channel: u16, deadline: Instant) -> Result<(), String> {
        if channel != 0 && !supported_channel(channel) {
            return Err("Unsupported hotspot channel policy".into());
        }
        let channel = channel.to_string();
        if hostapd_command(iface, &["set", "channel", &channel], deadline)?.trim() != "OK" {
            return Err("Hotspot rejected the runtime channel policy".into());
        }
        Ok(())
    }
}

fn configured_channel(config: &str) -> Result<u16, String> {
    let mut values = config.lines().filter_map(|line| {
        let (key, value) = line.split_once('=')?;
        (key.trim() == "channel").then_some(value.trim())
    });
    let channel = values
        .next()
        .and_then(|value| value.parse::<u16>().ok())
        .filter(|channel| *channel == 0 || supported_channel(*channel));
    if values.next().is_some() {
        return Err("Original hotspot channel policy is ambiguous".into());
    }
    channel.ok_or_else(|| "Original hotspot channel policy is unsupported or unreadable".into())
}

fn output(program: &str, args: &[&str], deadline: Instant) -> Result<Vec<u8>, String> {
    let timeout = COMMAND_TIMEOUT.min(remaining(deadline, Instant::now())?);
    let result = process_runner::output(Command::new(program).args(args), None, timeout, LIMIT)
        .map_err(|_| "Cannot read Wi-Fi runtime state")?;
    if !result.status.success() {
        return Err("Cannot read Wi-Fi runtime state".into());
    }
    Ok(result.stdout)
}

fn read_small(path: &Path, limit: usize) -> Result<Vec<u8>, String> {
    let file = File::open(path).map_err(|_| "Cannot read Wi-Fi configuration or diagnostics")?;
    let mut data = Vec::new();
    file.take(limit as u64 + 1)
        .read_to_end(&mut data)
        .map_err(|_| "Cannot read Wi-Fi configuration or diagnostics")?;
    if data.len() > limit {
        return Err("Wi-Fi configuration or diagnostics exceeded the read limit".into());
    }
    Ok(data)
}

fn value<'a>(text: &'a str, key: &str) -> Option<&'a str> {
    raw_value(text, key).map(str::trim)
}

fn raw_value<'a>(text: &'a str, key: &str) -> Option<&'a str> {
    text.lines().find_map(|line| {
        let (name, value) = line.split_once('=')?;
        (name == key).then_some(value)
    })
}

fn uci_value(text: &str, key: &str) -> Option<String> {
    value(text, key).map(|value| {
        value
            .strip_prefix('\'')
            .and_then(|value| value.strip_suffix('\''))
            .unwrap_or(value)
            .replace("'\\''", "'")
    })
}

fn switch(text: &str, key: &str) -> Result<bool, String> {
    match uci_value(text, key).as_deref() {
        Some("0") => Ok(false),
        Some("1") => Ok(true),
        _ => Err("Cannot determine intended hotspot state".into()),
    }
}

fn intended_aps(wireless: &str, mbb: &str) -> Result<Vec<Ap>, String> {
    let old = uci_value(wireless, "wireless.zte_mbb.wifi_onoff");
    let new = uci_value(mbb, "zte_mbb.wifi.wifi_onoff");
    if old.is_some() && new.is_some() && old != new {
        return Err("Wi-Fi power settings disagree".into());
    }
    let on = match new.or(old).as_deref() {
        Some("0") => false,
        Some("1") => true,
        _ => return Err("Cannot determine intended Wi-Fi power state".into()),
    };
    let mut aps: Vec<Ap> = Vec::new();
    for (band, radio) in [("2g", "wifi0"), ("5g", "wifi1")] {
        let radio_disabled = switch(wireless, &format!("wireless.{radio}.disabled"))?;
        let ap_disabled = switch(wireless, &format!("wireless.main_{band}.disabled"))?;
        let intended = on && !radio_disabled && !ap_disabled;
        if intended {
            expected_ssid(wireless, band)?;
        }
        let iface = uci_value(wireless, &format!("wireless.main_{band}.ifname"))
            .filter(|iface| valid_iface(iface))
            .ok_or("Cannot determine hotspot interface")?;
        if aps.iter().any(|ap| ap.iface == iface) {
            return Err("Hotspot interface mapping is ambiguous".into());
        }
        aps.push(Ap {
            iface,
            intended,
            state: "UNKNOWN".into(),
            host_frequency: None,
            driver_frequency: None,
            ssid_matches: None,
        });
    }
    Ok(aps)
}

fn expected_ssid(wireless: &str, band: &str) -> Result<String, String> {
    uci_value(wireless, &format!("wireless.main_{band}.ssid"))
        .filter(|ssid| !ssid.is_empty() && ssid.len() <= 32)
        .ok_or_else(|| "Cannot determine intended hotspot identity".into())
}

fn hostapd_ssid_text(ssid: &str) -> String {
    // hostapd STATUS uses wpa_ssid_txt/printf_encode on SSID bytes.
    let mut encoded = String::new();
    for byte in ssid.bytes() {
        match byte {
            b'"' => encoded.push_str("\\\""),
            b'\\' => encoded.push_str("\\\\"),
            b'\n' => encoded.push_str("\\n"),
            b'\r' => encoded.push_str("\\r"),
            b'\t' => encoded.push_str("\\t"),
            27 => encoded.push_str("\\e"),
            32..=126 => encoded.push(char::from(byte)),
            _ => encoded.push_str(&format!("\\x{byte:02x}")),
        }
    }
    encoded
}

fn runtime_absent(iface: &str) -> bool {
    // A failed command or inaccessible socket is not proof an AP is off.
    [
        Path::new(CTRL).join(iface),
        Path::new("/sys/class/net").join(iface),
    ]
    .iter()
    .all(|path| {
        matches!(fs::symlink_metadata(path), Err(error)
            if error.kind() == std::io::ErrorKind::NotFound)
    })
}

fn valid_iface(iface: &str) -> bool {
    !iface.is_empty()
        && iface.len() <= 15
        && iface
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
}

fn stock_idle(status: &Value) -> Result<bool, String> {
    let app = status
        .get("app_status")
        .and_then(Value::as_str)
        .ok_or("Cannot read Wi-Fi service state")?;
    let driver = status
        .get("driver_status")
        .and_then(Value::as_str)
        .ok_or("Cannot read Wi-Fi service state")?;
    let pending = status
        .get("pending")
        .and_then(|value| value.as_u64().or_else(|| value.as_str()?.parse().ok()))
        .ok_or("Cannot read Wi-Fi service state")?;
    Ok(app == "idle" && driver == "idle" && pending == 0)
}

fn driver_frequency(text: &str) -> Result<u32, String> {
    if !text.lines().any(|line| line.trim() == "type AP") {
        return Err("Expected hotspot interface is not an AP".into());
    }
    text.lines()
        .find_map(|line| {
            let line = line.trim().strip_prefix("channel ")?;
            let (_, rest) = line.split_once('(')?;
            rest.strip_suffix(')') // The normal output has width after the parenthesis.
                .unwrap_or(rest)
                .split_once(" MHz")?
                .0
                .parse::<u32>()
                .ok()
        })
        .filter(|value| (2400..=7125).contains(value))
        .ok_or_else(|| "Cannot read driver channel".into())
}

fn decimal_us(text: &str) -> Option<u64> {
    let (seconds, fraction) = text.split_once('.').unwrap_or((text, ""));
    if seconds.is_empty()
        || !seconds.bytes().all(|b| b.is_ascii_digit())
        || !fraction.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    let seconds = seconds.parse::<u64>().ok()?.checked_mul(1_000_000)?;
    let fraction = &fraction[..fraction.len().min(6)];
    let micros = if fraction.is_empty() {
        0
    } else {
        fraction.parse::<u64>().ok()? * 10u64.pow(6 - fraction.len() as u32)
    };
    seconds.checked_add(micros)
}

fn csa_timestamp(line: &str) -> Option<u64> {
    if !line.contains("wlan_hdd_add_key_sap") || !line.contains("wait for csa event failed") {
        return None;
    }
    kernel_timestamp(line)
}

fn kernel_timestamp(line: &str) -> Option<u64> {
    let (_, rest) = line.split_once('[')?;
    let (timestamp, _) = rest.split_once(']')?;
    decimal_us(timestamp.trim())
}

fn hostapd(iface: &str, command: &str, deadline: Instant) -> Result<String, String> {
    let command = match command {
        "STATUS" => "status",
        "DISABLE" => "disable",
        "ENABLE" => "enable",
        _ => return Err("Invalid hotspot control request".into()),
    };
    hostapd_command(iface, &[command], deadline)
}

fn hostapd_command(iface: &str, args: &[&str], deadline: Instant) -> Result<String, String> {
    if !valid_iface(iface) {
        return Err("Invalid hotspot control request".into());
    }
    // The firmware client creates a reply socket accessible to the unprivileged
    // hostapd daemon; a root-only client socket directory prevents its replies.
    let timeout = COMMAND_TIMEOUT.min(remaining(deadline, Instant::now())?);
    let reply = process_runner::output(
        Command::new("hostapd_cli")
            .args(["-p", CTRL, "-i", iface])
            .args(args),
        None,
        timeout,
        16384,
    )
    .map_err(|_| "Hotspot control request failed")?;
    if !reply.status.success() {
        return Err("Hotspot control request failed".into());
    }
    String::from_utf8(reply.stdout).map_err(|_| "Invalid hotspot control reply".into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashMap, HashSet, VecDeque};

    struct Fake {
        now: Instant,
        elapsed: Duration,
        sample: Sample,
        samples: VecDeque<Sample>,
        sample_delay: Duration,
        generation: Generation,
        generations: VecDeque<Result<Generation, String>>,
        reloads: usize,
        event_us: Option<u64>,
        log_base: u64,
        read_error: bool,
        commands: Vec<(String, String)>,
        disabled: HashSet<String>,
        fail_command: Option<(String, String)>,
        changed: bool,
        fingerprint_value: u8,
        fingerprint_error: bool,
        repair: bool,
        configured_channels: HashMap<String, u16>,
        runtime_channels: HashMap<String, u16>,
        acs_reroll: bool,
        restore_state_delay: u32,
        restore_state_errors: bool,
    }

    impl Fake {
        fn new() -> Self {
            Self {
                now: Instant::now(),
                elapsed: Duration::ZERO,
                sample: Sample {
                    idle: true,
                    stock_known: true,
                    aps: vec![
                        Ap {
                            iface: "wlan0".into(),
                            intended: true,
                            state: "ENABLED".into(),
                            host_frequency: Some(2442),
                            driver_frequency: Some(2412),
                            ssid_matches: Some(true),
                        },
                        Ap {
                            iface: "wlan2".into(),
                            intended: true,
                            state: "ENABLED".into(),
                            host_frequency: Some(5200),
                            driver_frequency: Some(5180),
                            ssid_matches: Some(true),
                        },
                    ],
                },
                samples: VecDeque::new(),
                sample_delay: Duration::ZERO,
                generation: ["wlan0", "wlan2"]
                    .into_iter()
                    .enumerate()
                    .map(|(index, iface)| RuntimeIdentity {
                        iface: iface.into(),
                        socket: Some((1, index as u64, 1, 0)),
                        ifindex: Some(index as u32 + 1),
                    })
                    .collect(),
                generations: VecDeque::new(),
                reloads: 0,
                event_us: Some(90_000_000),
                log_base: 100_000_000,
                read_error: false,
                commands: Vec::new(),
                disabled: HashSet::new(),
                fail_command: None,
                changed: false,
                fingerprint_value: 0,
                fingerprint_error: false,
                repair: true,
                configured_channels: [("wlan0".into(), 0), ("wlan2".into(), 0)].into(),
                runtime_channels: [("wlan0".into(), 0), ("wlan2".into(), 0)].into(),
                acs_reroll: false,
                restore_state_delay: 0,
                restore_state_errors: false,
            }
        }
        fn advance(&mut self, seconds: u64) {
            self.sleep(Duration::from_secs(seconds));
        }
        fn fresh(&mut self) {
            self.event_us = Some(self.log_base + self.elapsed.as_micros() as u64);
        }
        fn ready(&mut self) {
            for ap in &mut self.sample.aps {
                ap.driver_frequency = ap.host_frequency;
            }
        }
    }

    impl Backend for Fake {
        fn now(&self) -> Instant {
            self.now + self.elapsed
        }
        fn sleep(&mut self, duration: Duration) {
            self.elapsed += duration;
        }
        fn evidence(&mut self, _: Instant) -> Result<CsaEvidence, String> {
            if self.read_error {
                return Err("unreadable".into());
            }
            Ok(CsaEvidence {
                // Suspend can make uptime and printk clocks differ substantially.
                uptime_us: 10_000_000_000 + self.elapsed.as_micros() as u64,
                log_watermark_us: self.log_base + self.elapsed.as_micros() as u64,
                newest_event_us: self.event_us,
            })
        }
        fn sample(&mut self, _: Instant) -> Result<Sample, String> {
            self.elapsed += self.sample_delay;
            if self.read_error {
                return Err("unreadable".into());
            }
            Ok(self
                .samples
                .pop_front()
                .unwrap_or_else(|| self.sample.clone()))
        }
        fn generation(&mut self, _: &[String], _: Instant) -> Result<Generation, String> {
            self.generations
                .pop_front()
                .unwrap_or_else(|| Ok(self.generation.clone()))
        }
        fn reload(&mut self, _: Instant) -> Result<(), String> {
            self.reloads += 1;
            Ok(())
        }
        fn fingerprint(&mut self, _: &[String], _: Instant) -> Result<[u8; 32], String> {
            if self.fingerprint_error {
                return Err("unreadable".into());
            }
            Ok([self.fingerprint_value + u8::from(self.changed && !self.commands.is_empty()); 32])
        }
        fn control(&mut self, iface: &str, command: &str, _: Instant) -> Result<(), String> {
            self.commands.push((iface.into(), command.into()));
            if self.fail_command.as_ref() == Some(&(iface.into(), command.into())) {
                return Err("failed".into());
            }
            if command == "DISABLE" {
                self.disabled.insert(iface.into());
            }
            if command == "ENABLE" {
                self.disabled.remove(iface);
                if self.repair && (!self.acs_reroll || self.runtime_channels.get(iface) != Some(&0))
                {
                    for ap in &mut self.sample.aps {
                        if ap.iface == iface {
                            ap.driver_frequency = ap.host_frequency;
                        }
                    }
                }
            }
            Ok(())
        }
        fn state(&mut self, iface: &str, _: Instant) -> Result<String, String> {
            if self.restore_state_delay > 0
                && self
                    .commands
                    .iter()
                    .any(|(_, command)| command.starts_with("SET "))
            {
                self.restore_state_delay -= 1;
                return if self.restore_state_errors {
                    Err("unreadable".into())
                } else {
                    Ok("UNINITIALIZED".into())
                };
            }
            Ok(if self.disabled.contains(iface) {
                "DISABLED"
            } else {
                "ENABLED"
            }
            .into())
        }
        fn configured_channel(&mut self, iface: &str, _: Instant) -> Result<u16, String> {
            self.configured_channels
                .get(iface)
                .copied()
                .ok_or_else(|| "unreadable".into())
        }
        fn set_channel(&mut self, iface: &str, channel: u16, _: Instant) -> Result<(), String> {
            assert!(
                self.sample
                    .aps
                    .iter()
                    .filter(|ap| ap.intended)
                    .all(|ap| self.disabled.contains(&ap.iface)),
                "every active AP must stop before SET"
            );
            let command = format!("SET channel {channel}");
            self.commands.push((iface.into(), command.clone()));
            self.runtime_channels.insert(iface.into(), channel);
            if self.fail_command.as_ref() == Some(&(iface.into(), command)) {
                return Err("failed after mutating runtime channel".into());
            }
            Ok(())
        }
    }

    fn prime(monitor: &mut Monitor, fake: &mut Fake) {
        assert!(monitor.check_with(fake).unwrap().is_none());
        fake.advance(15);
        fake.fresh();
    }

    #[test]
    fn recovers_observed_two_band_fault_only_after_stable_mismatch_and_new_error() {
        let mut fake = Fake::new();
        let mut monitor = Monitor::default();
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.advance(14);
        fake.fresh();
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        assert!(fake.commands.is_empty());
        fake.advance(1);
        assert!(monitor.check_with(&mut fake).unwrap().is_some());
        assert_eq!(
            fake.commands,
            vec![
                ("wlan0".into(), "DISABLE".into()),
                ("wlan2".into(), "DISABLE".into()),
                ("wlan0".into(), "SET channel 7".into()),
                ("wlan2".into(), "SET channel 40".into()),
                ("wlan0".into(), "ENABLE".into()),
                ("wlan2".into(), "ENABLE".into())
            ]
        );
        assert!(fake.sample.ready());
    }

    #[test]
    fn historical_errors_do_not_trigger_and_recovery_is_one_shot() {
        let mut fake = Fake::new();
        let mut monitor = Monitor::default();
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.advance(30);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        assert!(fake.commands.is_empty());
        fake.advance(1);
        fake.fresh();
        assert!(monitor.check_with(&mut fake).unwrap().is_some());
        fake.sample.aps[0].driver_frequency = Some(2412);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.advance(15);
        fake.fresh();
        assert!(monitor.check_with(&mut fake).is_err());
        assert_eq!(fake.commands.len(), 6);
        assert!(monitor.check_with(&mut fake).is_err());
        monitor.baseline_with(&mut fake);
        assert!(monitor.check_with(&mut fake).is_err());
        assert_eq!(fake.commands.len(), 6);
    }

    #[test]
    fn explicit_baseline_preserves_errors_since_operation_start() {
        let mut fake = Fake::new();
        let mut monitor = Monitor::default();
        monitor.baseline_with(&mut fake);
        fake.advance(1);
        fake.fresh();
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.advance(15);
        assert!(monitor.check_with(&mut fake).unwrap().is_some());
    }

    #[test]
    fn verified_post_change_window_recovers_resume_mismatch_without_a_new_csa_error() {
        let mut fake = Fake::new();
        fake.sample.aps[0].host_frequency = Some(2412);
        fake.ready();
        let mut monitor = Monitor::default();
        monitor.after_hotspot_change_with(&mut fake).unwrap();
        fake.sample.aps[1].driver_frequency = Some(5240);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.advance(14);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        assert!(fake.commands.is_empty());
        fake.advance(1);
        assert!(monitor.check_with(&mut fake).unwrap().is_some());
        assert_eq!(
            fake.commands,
            vec![
                ("wlan0".into(), "DISABLE".into()),
                ("wlan2".into(), "DISABLE".into()),
                ("wlan2".into(), "SET channel 40".into()),
                ("wlan0".into(), "ENABLE".into()),
                ("wlan2".into(), "ENABLE".into()),
            ]
        );
        assert!(fake.sample.ready());
        assert_eq!(fake.event_us, Some(90_000_000));
        assert!(monitor.post_change.is_some());
    }

    #[test]
    fn post_change_window_requires_ready_runtime_and_readable_fingerprint() {
        for fault in ["unknown", "busy", "ssid", "mismatch", "config", "read"] {
            let mut fake = Fake::new();
            fake.ready();
            match fault {
                "unknown" => fake.sample.aps[0].state = "UNKNOWN".into(),
                "busy" => fake.sample.idle = false,
                "ssid" => fake.sample.aps[0].ssid_matches = Some(false),
                "mismatch" => fake.sample.aps[1].driver_frequency = Some(5240),
                "config" => fake.fingerprint_error = true,
                "read" => fake.read_error = true,
                _ => unreachable!(),
            }
            let mut monitor = Monitor::default();
            assert!(
                monitor.after_hotspot_change_with(&mut fake).is_err(),
                "{fault}"
            );
            assert!(monitor.post_change.is_none());
            assert!(fake.commands.is_empty());
        }
    }

    #[test]
    fn ready_samples_do_not_consume_post_change_permission() {
        let mut fake = Fake::new();
        fake.ready();
        let mut monitor = Monitor::default();
        monitor.after_hotspot_change_with(&mut fake).unwrap();
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.advance(3);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        assert!(monitor.post_change.is_some());
        fake.sample.aps[1].driver_frequency = Some(5240);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.advance(15);
        assert!(monitor.check_with(&mut fake).unwrap().is_some());
    }

    #[test]
    fn post_change_permission_is_revoked_by_expiry_config_change_or_read_error() {
        for revoked_by in ["expired", "changed", "unreadable"] {
            let mut fake = Fake::new();
            fake.ready();
            let mut monitor = Monitor::default();
            monitor.after_hotspot_change_with(&mut fake).unwrap();
            fake.sample.aps[1].driver_frequency = Some(5240);
            assert!(monitor.check_with(&mut fake).unwrap().is_none());
            match revoked_by {
                "expired" => fake.advance(120),
                "changed" => {
                    fake.advance(15);
                    fake.fingerprint_value = 1;
                }
                "unreadable" => {
                    fake.advance(15);
                    fake.fingerprint_error = true;
                }
                _ => unreachable!(),
            }
            assert!(
                monitor.check_with(&mut fake).unwrap().is_none(),
                "{revoked_by}"
            );
            assert!(monitor.post_change.is_none());
            fake.fingerprint_value = 0;
            fake.fingerprint_error = false;
            fake.advance(15);
            assert!(monitor.check_with(&mut fake).unwrap().is_none());
            assert!(fake.commands.is_empty());
            fake.advance(1);
            fake.fresh();
            assert!(monitor.check_with(&mut fake).unwrap().is_some());
        }
    }

    #[test]
    fn post_change_recurrence_latches_without_a_new_csa_error_or_second_cycle() {
        let mut fake = Fake::new();
        fake.ready();
        let mut monitor = Monitor::default();
        monitor.after_hotspot_change_with(&mut fake).unwrap();
        for recurrence in [false, true] {
            fake.sample.aps[1].driver_frequency = Some(5240);
            assert!(monitor.check_with(&mut fake).unwrap().is_none());
            fake.advance(15);
            let result = monitor.check_with(&mut fake);
            if recurrence {
                assert!(result.is_err());
            } else {
                assert!(result.unwrap().is_some());
            }
        }
        assert_eq!(fake.commands.len(), 5);
        fake.ready();
        assert!(monitor.after_hotspot_change_with(&mut fake).is_err());
        assert!(monitor.check_with(&mut fake).is_err());
        assert_eq!(fake.commands.len(), 5);
    }

    #[test]
    fn post_change_window_does_not_authorize_wrong_ssid_or_unarmed_background_mismatch() {
        for armed in [false, true] {
            let mut fake = Fake::new();
            fake.ready();
            let mut monitor = Monitor::default();
            if armed {
                monitor.after_hotspot_change_with(&mut fake).unwrap();
            }
            fake.sample.aps[1].driver_frequency = Some(5240);
            if armed {
                fake.sample.aps[1].ssid_matches = Some(false);
            }
            assert!(monitor.check_with(&mut fake).unwrap().is_none());
            fake.advance(30);
            assert!(monitor.check_with(&mut fake).unwrap().is_none());
            assert!(fake.commands.is_empty());
        }
    }

    #[test]
    fn expiry_during_observation_cannot_latch_a_recurrence_without_new_csa() {
        let mut fake = Fake::new();
        fake.ready();
        let mut monitor = Monitor::default();
        monitor.after_hotspot_change_with(&mut fake).unwrap();
        fake.sample.aps[1].driver_frequency = Some(5240);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.advance(15);
        assert!(monitor.check_with(&mut fake).unwrap().is_some());
        fake.sample.aps[1].driver_frequency = Some(5240);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.sleep(Duration::from_secs(119) - fake.elapsed);
        fake.sample_delay = Duration::from_secs(2);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        assert!(monitor.post_change.is_none());
        assert!(monitor.failure.is_none());
        assert_eq!(fake.commands.len(), 5);
        fake.fresh();
        assert!(monitor.check_with(&mut fake).is_err());
        assert_eq!(fake.commands.len(), 5);
    }

    #[test]
    fn transient_states_and_read_errors_break_stability_and_discard_old_evidence() {
        for state in [
            "ACS",
            "DFS",
            "COUNTRY_UPDATE",
            "UNINITIALIZED",
            "DISABLED",
            "UNKNOWN",
            "MISSING",
        ] {
            let mut fake = Fake::new();
            let mut monitor = Monitor::default();
            prime(&mut monitor, &mut fake);
            fake.sample.aps[0].state = state.into();
            assert!(monitor.check_with(&mut fake).unwrap().is_none());
            fake.sample.aps[0].state = "ENABLED".into();
            fake.advance(1);
            assert!(monitor.check_with(&mut fake).unwrap().is_none());
            fake.advance(20);
            assert!(monitor.check_with(&mut fake).unwrap().is_none());
            assert!(fake.commands.is_empty());
        }
        let mut fake = Fake::new();
        let mut monitor = Monitor::default();
        prime(&mut monitor, &mut fake);
        fake.read_error = true;
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.read_error = false;
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        assert!(fake.commands.is_empty());
    }

    #[test]
    fn failed_disable_or_enable_attempts_every_enable_and_latches_failure() {
        for command in ["DISABLE", "ENABLE"] {
            for iface in ["wlan0", "wlan2"] {
                let mut fake = Fake::new();
                let mut monitor = Monitor::default();
                prime(&mut monitor, &mut fake);
                fake.fail_command = Some((iface.into(), command.into()));
                assert!(monitor.check_with(&mut fake).is_err());
                assert!(fake.commands.contains(&("wlan0".into(), "ENABLE".into())));
                assert!(fake.commands.contains(&("wlan2".into(), "ENABLE".into())));
                let count = fake.commands.len();
                assert!(monitor.check_with(&mut fake).is_err());
                assert_eq!(fake.commands.len(), count);
            }
        }
    }

    #[test]
    fn changed_settings_or_failed_readiness_stop_recovery_without_repeated_cycles() {
        for changed in [true, false] {
            let mut fake = Fake::new();
            let mut monitor = Monitor::default();
            prime(&mut monitor, &mut fake);
            fake.changed = changed;
            fake.repair = changed;
            assert!(monitor.check_with(&mut fake).is_err());
            assert!(fake.disabled.is_empty());
            let count = fake.commands.len();
            assert_eq!(count, if changed { 4 } else { 12 });
            assert!(monitor.check_with(&mut fake).is_err());
            assert_eq!(fake.commands.len(), count);
        }
    }

    #[test]
    fn one_intended_ap_is_recovered_without_touching_the_disabled_band() {
        let mut fake = Fake::new();
        fake.sample.aps[0].intended = false;
        fake.sample.aps[0].state = "DISABLED".into();
        let mut monitor = Monitor::default();
        prime(&mut monitor, &mut fake);
        assert!(monitor.check_with(&mut fake).unwrap().is_some());
        assert_eq!(
            fake.commands,
            vec![
                ("wlan2".into(), "DISABLE".into()),
                ("wlan2".into(), "SET channel 40".into()),
                ("wlan2".into(), "ENABLE".into())
            ]
        );
    }

    #[test]
    fn channel_pin_prevents_acs_reroll_and_only_changes_the_mismatched_ap() {
        let mut fake = Fake::new();
        fake.ready();
        fake.sample.aps[1].driver_frequency = Some(5240);
        fake.acs_reroll = true;
        let mut monitor = Monitor::default();
        prime(&mut monitor, &mut fake);
        assert!(monitor.check_with(&mut fake).unwrap().is_some());
        assert_eq!(
            fake.commands,
            vec![
                ("wlan0".into(), "DISABLE".into()),
                ("wlan2".into(), "DISABLE".into()),
                ("wlan2".into(), "SET channel 40".into()),
                ("wlan0".into(), "ENABLE".into()),
                ("wlan2".into(), "ENABLE".into()),
            ]
        );
        assert_eq!(fake.runtime_channels["wlan0"], 0);
        assert_eq!(fake.runtime_channels["wlan2"], 40);
        assert_eq!(fake.configured_channels["wlan2"], 0);
        assert!(fake.sample.ready());
    }

    #[test]
    fn failed_set_restores_original_policy_even_when_rejected_set_mutated_runtime() {
        let mut fake = Fake::new();
        fake.configured_channels.insert("wlan2".into(), 44);
        fake.runtime_channels.insert("wlan2".into(), 44);
        fake.fail_command = Some(("wlan2".into(), "SET channel 40".into()));
        let mut monitor = Monitor::default();
        prime(&mut monitor, &mut fake);
        assert!(monitor.check_with(&mut fake).is_err());
        assert_eq!(fake.runtime_channels, fake.configured_channels);
        assert_eq!(
            fake.commands,
            vec![
                ("wlan0".into(), "DISABLE".into()),
                ("wlan2".into(), "DISABLE".into()),
                ("wlan0".into(), "SET channel 7".into()),
                ("wlan2".into(), "SET channel 40".into()),
                ("wlan0".into(), "DISABLE".into()),
                ("wlan2".into(), "DISABLE".into()),
                ("wlan0".into(), "SET channel 0".into()),
                ("wlan2".into(), "SET channel 44".into()),
                ("wlan0".into(), "ENABLE".into()),
                ("wlan2".into(), "ENABLE".into()),
            ]
        );
        let commands = fake.commands.clone();
        assert!(monitor.check_with(&mut fake).is_err());
        assert_eq!(fake.commands, commands);
    }

    #[test]
    fn enable_and_readiness_failures_restore_auto_channel_before_final_enable() {
        for enable_fails in [false, true] {
            let mut fake = Fake::new();
            fake.repair = enable_fails;
            if enable_fails {
                fake.fail_command = Some(("wlan0".into(), "ENABLE".into()));
            }
            let mut monitor = Monitor::default();
            prime(&mut monitor, &mut fake);
            assert!(monitor.check_with(&mut fake).is_err());
            assert_eq!(fake.runtime_channels, fake.configured_channels);
            assert_eq!(
                &fake.commands[fake.commands.len() - 4..],
                &[
                    ("wlan0".into(), "SET channel 0".into()),
                    ("wlan2".into(), "SET channel 0".into()),
                    ("wlan0".into(), "ENABLE".into()),
                    ("wlan2".into(), "ENABLE".into()),
                ]
            );
        }
    }

    #[test]
    fn restoration_waits_for_transient_or_unreadable_disabled_state() {
        for unreadable in [false, true] {
            let mut fake = Fake::new();
            fake.restore_state_delay = 2;
            fake.restore_state_errors = unreadable;
            fake.fail_command = Some(("wlan2".into(), "SET channel 40".into()));
            let mut monitor = Monitor::default();
            prime(&mut monitor, &mut fake);
            let before = fake.elapsed;
            assert!(monitor.check_with(&mut fake).is_err());
            assert!(fake.elapsed - before >= POLL);
            assert_eq!(fake.runtime_channels, fake.configured_channels);
            assert!(fake.disabled.is_empty());
        }
    }

    #[test]
    fn restoration_deadline_never_sets_on_unconfirmed_aps_and_still_enables_every_ap() {
        let mut fake = Fake::new();
        fake.restore_state_delay = 1000;
        fake.fail_command = Some(("wlan2".into(), "SET channel 40".into()));
        let mut monitor = Monitor::default();
        prime(&mut monitor, &mut fake);
        let before = fake.elapsed;
        assert!(monitor.check_with(&mut fake).is_err());
        assert!(fake.elapsed - before <= CHANNEL_RESTORE_TIMEOUT);
        assert!(!fake
            .commands
            .iter()
            .any(|(_, command)| command == "SET channel 0"));
        assert_eq!(
            &fake.commands[fake.commands.len() - 2..],
            &[
                ("wlan0".into(), "ENABLE".into()),
                ("wlan2".into(), "ENABLE".into()),
            ]
        );
        assert!(fake.disabled.is_empty());
    }

    #[test]
    fn unsupported_targets_or_unreadable_original_policy_never_mutate() {
        for fault in [
            "dfs",
            "channel14",
            "6ghz",
            "original_dfs",
            "original_missing",
        ] {
            let mut fake = Fake::new();
            match fault {
                "dfs" => fake.sample.aps[1].host_frequency = Some(5260),
                "channel14" => fake.sample.aps[0].host_frequency = Some(2484),
                "6ghz" => fake.sample.aps[1].host_frequency = Some(5955),
                "original_dfs" => {
                    fake.configured_channels.insert("wlan2".into(), 52);
                }
                "original_missing" => {
                    fake.configured_channels.remove("wlan2");
                }
                _ => unreachable!(),
            }
            let mut monitor = Monitor::default();
            prime(&mut monitor, &mut fake);
            assert!(monitor.check_with(&mut fake).is_err(), "{fault}");
            assert!(fake.commands.is_empty());
            assert!(!monitor.attempted);
        }
        for channel in [1, 6, 13, 36, 40, 44, 48, 149, 153, 157, 161, 165] {
            let frequency = if channel <= 13 {
                2407 + channel * 5
            } else {
                5000 + channel * 5
            };
            assert_eq!(target_channel(frequency), Some(channel as u16));
            assert_eq!(
                configured_channel(&format!("channel={channel}\n")),
                Ok(channel as u16)
            );
        }
        assert_eq!(configured_channel("channel=0\n"), Ok(0));
        for config in [
            "",
            "channel=bad\n",
            "channel=0\nchannel=40\n",
            "channel=52\n",
        ] {
            assert!(configured_channel(config).is_err());
        }
    }

    #[test]
    fn readiness_accepts_disabled_intent_but_not_unreadable_or_mismatched_runtime() {
        let mut fake = Fake::new();
        for ap in &mut fake.sample.aps {
            ap.intended = false;
            ap.state = "DISABLED".into();
        }
        let deadline = fake.now() + Duration::from_secs(1);
        assert!(wait_ready_with(&mut fake, deadline).is_ok());
        fake.read_error = true;
        assert!(wait_ready_with(&mut fake, deadline).is_err());
        let mut fake = Fake::new();
        let deadline = fake.now() + Duration::from_secs(1);
        assert!(wait_ready_with(&mut fake, deadline).is_err());
        assert!(fake.commands.is_empty());
    }

    #[test]
    fn readiness_waits_for_runtime_and_disabled_intent_to_settle() {
        let mut fake = Fake::new();
        for ap in &mut fake.sample.aps {
            ap.driver_frequency = ap.host_frequency;
        }
        let mut missing = fake.sample.clone();
        missing.aps[0].state = "UNKNOWN".into();
        fake.samples.push_back(missing);
        let deadline = fake.now() + Duration::from_secs(2);
        assert!(wait_ready_with(&mut fake, deadline).is_ok());
        assert!(fake.elapsed >= POLL * 2);

        for ap in &mut fake.sample.aps {
            ap.intended = false;
            ap.state = "MISSING".into();
        }
        let mut busy = fake.sample.clone();
        busy.idle = false;
        let mut still_on = fake.sample.clone();
        still_on.aps[0].state = "ENABLED".into();
        fake.samples.extend([busy, still_on]);
        let before = fake.elapsed;
        let deadline = fake.now() + Duration::from_secs(2);
        assert!(wait_ready_with(&mut fake, deadline).is_ok());
        assert!(fake.elapsed - before >= POLL * 3);
        assert!(fake.commands.is_empty());
    }

    #[test]
    fn log_clock_rollback_restarts_evidence_and_stability() {
        let mut fake = Fake::new();
        let mut monitor = Monitor::default();
        prime(&mut monitor, &mut fake);
        fake.log_base = 1_000_000;
        fake.fresh();
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        fake.advance(20);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        assert!(fake.commands.is_empty());
        fake.advance(1);
        fake.fresh();
        assert!(monitor.check_with(&mut fake).unwrap().is_some());
    }

    #[test]
    fn unchanged_ready_runtime_never_acknowledges_reload() {
        let mut fake = Fake::new();
        fake.ready();
        let deadline = fake.now() + Duration::from_secs(2);
        assert!(reload_and_wait_with(&mut fake, deadline).is_err());
        assert_eq!(fake.reloads, 1);
        assert_eq!(fake.elapsed, Duration::from_secs(2));
        assert!(fake.commands.is_empty());
    }

    #[test]
    fn replaced_runtime_needs_two_consistent_ready_samples_on_every_active_band() {
        for changed_bands in [1, 2] {
            let mut fake = Fake::new();
            fake.ready();
            fake.generations.push_back(Ok(fake.generation.clone()));
            for marker in fake.generation.iter_mut().take(changed_bands) {
                marker.socket = Some((1, 100, 2, 0));
            }
            let deadline = fake.now() + Duration::from_secs(2);
            assert_eq!(
                reload_and_wait_with(&mut fake, deadline).is_ok(),
                changed_bands == 2
            );
            assert!(fake.elapsed >= POLL);
            assert_eq!(fake.reloads, 1);
        }
    }

    #[test]
    fn observed_busy_phase_allows_in_place_reload_to_settle() {
        let mut fake = Fake::new();
        fake.ready();
        fake.samples.push_back(fake.sample.clone());
        let mut busy = fake.sample.clone();
        busy.idle = false;
        fake.samples.push_back(busy);
        let deadline = fake.now() + Duration::from_secs(2);
        assert!(reload_and_wait_with(&mut fake, deadline).is_ok());
        assert!(fake.elapsed >= POLL * 2);
    }

    #[test]
    fn disabled_shutdown_is_verified_but_unchanged_off_state_is_not_a_reload() {
        for already_off in [false, true] {
            let mut fake = Fake::new();
            for ap in &mut fake.sample.aps {
                ap.intended = false;
                if already_off {
                    ap.state = "MISSING".into();
                }
            }
            fake.samples.push_back(fake.sample.clone());
            fake.generations.push_back(Ok(fake.generation.clone()));
            for ap in &mut fake.sample.aps {
                ap.state = "MISSING".into();
            }
            if !already_off {
                for marker in &mut fake.generation {
                    marker.socket = None;
                    marker.ifindex = None;
                }
            }
            let deadline = fake.now() + Duration::from_secs(2);
            assert_eq!(
                reload_and_wait_with(&mut fake, deadline).is_ok(),
                !already_off
            );
        }
    }

    #[test]
    fn unreadable_runtime_cannot_supply_reload_generation_evidence() {
        let mut fake = Fake::new();
        fake.ready();
        fake.samples.push_back(fake.sample.clone());
        let mut unknown = fake.sample.clone();
        unknown.stock_known = false;
        unknown.idle = false;
        for ap in &mut unknown.aps {
            ap.state = "UNKNOWN".into();
        }
        fake.samples.push_back(unknown);
        fake.generations.push_back(Ok(fake.generation.clone()));
        fake.generations.push_back(Err("unreadable".into()));
        let deadline = fake.now() + Duration::from_secs(2);
        assert!(reload_and_wait_with(&mut fake, deadline).is_err());
        assert_eq!(fake.reloads, 1);

        let mut fake = Fake::new();
        fake.generations.push_back(Err("unreadable".into()));
        let deadline = fake.now() + Duration::from_secs(2);
        assert!(reload_and_wait_with(&mut fake, deadline).is_err());
        assert_eq!(fake.reloads, 0);
    }

    #[test]
    fn ssid_mismatch_blocks_readiness_but_cannot_trigger_csa_recovery() {
        let mut fake = Fake::new();
        fake.ready();
        fake.sample.aps[0].ssid_matches = Some(false);
        assert!(!fake.sample.ready());
        let mut monitor = Monitor::default();
        prime(&mut monitor, &mut fake);
        assert!(monitor.check_with(&mut fake).unwrap().is_none());
        assert!(fake.commands.is_empty());
        assert_eq!(
            hostapd_ssid_text(" 空 格 "),
            " \\xe7\\xa9\\xba \\xe6\\xa0\\xbc "
        );
        assert_eq!(
            hostapd_ssid_text("a\\\"\n\r\t\u{1b}"),
            "a\\\\\\\"\\n\\r\\t\\e"
        );
        assert_eq!(
            raw_value("ssid[0]= name \nstate=ENABLED\n", "ssid[0]"),
            Some(" name ")
        );
    }

    #[test]
    fn parsing_excludes_non_csa_errors_and_requires_valid_channel_and_intent() {
        assert_eq!(
            csa_timestamp(
                "[ 123.456789] wlan: wlan_hdd_add_key_sap: Vdev 0 wait for csa event failed!!"
            ),
            Some(123_456_789)
        );
        assert_eq!(
            csa_timestamp("[123.5] other: wait for csa event failed"),
            None
        );
        assert_eq!(
            csa_timestamp("wlan_hdd_add_key_sap: wait for csa event failed"),
            None
        );
        assert_eq!(
            driver_frequency("type AP\nchannel 40 (5200 MHz), width: 160 MHz, center1: 5250 MHz"),
            Ok(5200)
        );
        assert!(driver_frequency("type managed\nchannel 40 (5200 MHz)").is_err());
        let config = "wireless.zte_mbb.wifi_onoff='1'\nwireless.wifi0.disabled='0'\nwireless.wifi1.disabled='0'\nwireless.main_2g.disabled='1'\nwireless.main_5g.disabled='0'\nwireless.main_2g.ifname='wlan0'\nwireless.main_5g.ifname='wlan2'\nwireless.main_5g.ssid='example'\n";
        let aps = intended_aps(config, "").unwrap();
        assert_eq!(
            aps.iter()
                .map(|ap| (ap.iface.as_str(), ap.intended))
                .collect::<Vec<_>>(),
            vec![("wlan0", false), ("wlan2", true)]
        );
        assert!(intended_aps(config, "zte_mbb.wifi.wifi_onoff='0'").is_err());
        assert!(intended_aps("", "").is_err());
        assert!(stock_idle(
            &serde_json::json!({"app_status":"idle","driver_status":"idle","pending":0})
        )
        .unwrap());
        assert!(stock_idle(&serde_json::json!({})).is_err());
    }
}
