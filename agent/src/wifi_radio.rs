//! AP readiness and one bounded recovery of the Qualcomm CSA/key-install stall.
//!
//! Callers must hold the shared radio-operation lock. This module never changes
//! UCI, credentials, channels or channel geometry. A healthy upstream connection
//! is not evidence that hotspot clients can associate.
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

const STABLE_MISMATCH: Duration = Duration::from_secs(15);
const SAMPLE_TIMEOUT: Duration = Duration::from_secs(12);
const RECOVERY_TIMEOUT: Duration = Duration::from_secs(30);
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

/// One monitor belongs to one supervisor lifetime. Replacing it explicitly after
/// a coordinated settings operation also establishes a new kernel-log baseline.
/// No historical error count, unreadable sample, or lone mismatch can restart APs.
#[derive(Default)]
pub struct Monitor {
    watermark_us: Option<u64>,
    last_uptime_us: Option<u64>,
    pending: Option<Pending>,
    attempted: bool,
    failure: Option<String>,
}

impl Monitor {
    /// Establish a read-only baseline before a coordinated operation can emit
    /// CSA errors. A failed read makes the next successful check baseline only.
    /// This does not reset a spent recovery allowance or a latched error.
    pub fn baseline(&mut self) {
        self.baseline_with(&mut Native);
    }

    fn baseline_with(&mut self, backend: &mut impl Backend) {
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
        let evidence = match backend.evidence(deadline) {
            Ok(value) => value,
            Err(_) => {
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
            self.pending = None;
        }
        // Kernel printk timestamps and uptime can treat suspend differently.
        // Compare log events only with the previous log's own timestamp clock.
        self.watermark_us = Some(evidence.log_watermark_us);
        self.last_uptime_us = Some(evidence.uptime_us);
        let sample = match backend.sample(deadline) {
            Ok(value) if value.mismatched() => value,
            _ => {
                self.pending = None;
                return Ok(None);
            }
        };
        let now = backend.now();
        match &mut self.pending {
            Some(pending) if pending.sample == sample => pending.fresh_error |= fresh,
            _ => {
                self.pending = Some(Pending {
                    since: now,
                    sample: sample.clone(),
                    fresh_error: fresh,
                });
                return Ok(None);
            }
        }
        let pending = self.pending.as_ref().unwrap();
        if now.duration_since(pending.since) < STABLE_MISMATCH || !pending.fresh_error {
            return Ok(None);
        }
        if self.attempted {
            return self.fail("The Wi-Fi channel fault returned after one recovery; automatic recovery is stopped");
        }
        let interfaces: Vec<_> = sample
            .aps
            .iter()
            .filter(|ap| ap.intended)
            .map(|ap| ap.iface.clone())
            .collect();
        let before = match backend.fingerprint(&interfaces, deadline) {
            Ok(value) => value,
            Err(_) => {
                self.pending = None;
                return Ok(None);
            }
        };
        // The samples above are observations, not a claim on the stock service.
        // Recheck immediately before the first write as it does not share our lock.
        match backend.sample(deadline) {
            Ok(current) if current == sample => {}
            _ => {
                self.pending = None;
                return Ok(None);
            }
        }
        self.attempted = true;
        self.pending = None;
        if let Err(error) = recover(backend, &interfaces, before) {
            return self.fail(&error);
        }
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
    before: [u8; 32],
) -> Result<(), String> {
    let deadline = backend.now() + RECOVERY_TIMEOUT;
    let stopped = (|| {
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
        Ok(())
    })();

    // A separate small restoration budget also covers an expired stop deadline.
    // Continue through all APs even if one enable command fails.
    let restore_deadline = backend.now() + COMMAND_TIMEOUT * (interfaces.len() as u32 + 1);
    let mut enable_failed = false;
    for iface in interfaces {
        enable_failed |= backend.control(iface, "ENABLE", restore_deadline).is_err();
    }
    if stopped.is_err() || enable_failed {
        return Err("Wi-Fi recovery failed; re-enabling every previously active AP was attempted and automatic recovery is stopped".into());
    }
    if wait_ready_with(backend, deadline).is_err() {
        return Err(
            "Wi-Fi recovery did not reach a verified ready state; automatic recovery is stopped"
                .into(),
        );
    }
    if backend.fingerprint(interfaces, deadline)? != before {
        return Err("Wi-Fi settings changed during recovery; automatic recovery is stopped".into());
    }
    Ok(())
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
    if !valid_iface(iface) {
        return Err("Invalid hotspot control request".into());
    }
    let command = match command {
        "STATUS" => "status",
        "DISABLE" => "disable",
        "ENABLE" => "enable",
        _ => return Err("Invalid hotspot control request".into()),
    };
    // The firmware client creates a reply socket accessible to the unprivileged
    // hostapd daemon; a root-only client socket directory prevents its replies.
    let timeout = COMMAND_TIMEOUT.min(remaining(deadline, Instant::now())?);
    let reply = process_runner::output(
        Command::new("hostapd_cli").args(["-p", CTRL, "-i", iface, command]),
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
    use std::collections::{HashSet, VecDeque};

    struct Fake {
        now: Instant,
        elapsed: Duration,
        sample: Sample,
        samples: VecDeque<Sample>,
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
        repair: bool,
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
                repair: true,
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
            Ok([u8::from(self.changed && !self.commands.is_empty()); 32])
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
                if self.repair {
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
            Ok(if self.disabled.contains(iface) {
                "DISABLED"
            } else {
                "ENABLED"
            }
            .into())
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
        assert_eq!(fake.commands.len(), 4);
        assert!(monitor.check_with(&mut fake).is_err());
        monitor.baseline_with(&mut fake);
        assert!(monitor.check_with(&mut fake).is_err());
        assert_eq!(fake.commands.len(), 4);
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
            assert_eq!(fake.commands.len(), 4);
            assert!(monitor.check_with(&mut fake).is_err());
            assert_eq!(fake.commands.len(), 4);
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
                ("wlan2".into(), "ENABLE".into())
            ]
        );
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
