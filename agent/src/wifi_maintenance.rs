//! A temporary runtime hold while hotspot settings are applied. The relay must
//! acknowledge that its client has stopped before the caller changes the radio.
use std::sync::{Condvar, Mutex};
use std::time::{Duration, Instant};

static COORDINATOR: Coordinator = Coordinator::new();

struct Request {
    ticket: u64,
    acknowledgement: Option<Result<(), String>>,
}

struct State {
    next_ticket: u64,
    request: Option<Request>,
}

struct Coordinator {
    state: Mutex<State>,
    changed: Condvar,
}

impl Coordinator {
    const fn new() -> Self {
        Self {
            state: Mutex::new(State {
                next_ticket: 0,
                request: None,
            }),
            changed: Condvar::new(),
        }
    }

    fn begin(&self, wake: fn()) -> Result<Hold<'_>, String> {
        let ticket = {
            let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
            if state.request.is_some() {
                return Err("Another Wi-Fi settings change is in progress".into());
            }
            state.next_ticket = state
                .next_ticket
                .checked_add(1)
                .ok_or("Wi-Fi maintenance generation exhausted")?;
            let ticket = state.next_ticket;
            state.request = Some(Request {
                ticket,
                acknowledgement: None,
            });
            ticket
        };
        let hold = Hold {
            coordinator: self,
            ticket,
            wake,
            active: true,
        };
        // Do not hold the coordinator mutex while waking the supervisor.
        wake();
        Ok(hold)
    }

    fn pending(&self) -> Option<u64> {
        self.state
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .request
            .as_ref()
            .map(|request| request.ticket)
    }

    fn acknowledge(&self, ticket: u64, result: Result<(), String>) {
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        let Some(request) = state.request.as_mut().filter(|r| r.ticket == ticket) else {
            return;
        };
        if request.acknowledgement.is_none() {
            request.acknowledgement = Some(result);
            self.changed.notify_all();
        }
    }

    fn release(&self, ticket: u64) -> bool {
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if state.request.as_ref().map(|r| r.ticket) != Some(ticket) {
            return false;
        }
        state.request = None;
        self.changed.notify_all();
        true
    }
}

/// Keeps the relay stopped after acknowledgement until the settings operation
/// finishes. Dropping the hold always wakes the supervisor so it can resume.
pub struct Hold<'a> {
    coordinator: &'a Coordinator,
    ticket: u64,
    wake: fn(),
    active: bool,
}

impl Hold<'_> {
    /// Wait for actual supervisor teardown, not the published UI state. A timeout
    /// or failed acknowledgement releases the hold before returning the error.
    pub fn wait(&mut self, timeout: Duration) -> Result<(), String> {
        if !self.active {
            return Err("Wi-Fi maintenance request is no longer active".into());
        }
        let started = Instant::now();
        let result = {
            let mut state = self
                .coordinator
                .state
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            loop {
                let Some(request) = state.request.as_ref().filter(|r| r.ticket == self.ticket)
                else {
                    break Err("Wi-Fi maintenance request was cancelled".into());
                };
                if let Some(result) = &request.acknowledgement {
                    break result.clone();
                }
                let remaining = timeout.saturating_sub(started.elapsed());
                if remaining.is_zero() {
                    break Err("Timed out waiting for the Wi-Fi relay to stop".into());
                }
                state = self
                    .coordinator
                    .changed
                    .wait_timeout(state, remaining)
                    .unwrap_or_else(|e| e.into_inner())
                    .0;
            }
        };
        if result.is_err() {
            self.release();
        }
        result
    }

    fn release(&mut self) {
        if self.active {
            self.active = false;
            if self.coordinator.release(self.ticket) {
                (self.wake)();
            }
        }
    }
}

impl Drop for Hold<'_> {
    fn drop(&mut self) {
        self.release();
    }
}

/// Register a hold and wake the relay supervisor. The caller must then wait for
/// acknowledgement before touching radio settings, and retain the hold until done.
pub fn begin(wake: fn()) -> Result<Hold<'static>, String> {
    COORDINATOR.begin(wake)
}

/// Includes acknowledged requests: the supervisor must remain paused until the
/// caller releases its hold. Check this before acquiring radio-operation locks.
pub fn pending() -> Option<u64> {
    COORDINATOR.pending()
}

/// Acknowledge only after the client's processes and interface have stopped.
/// Expired generations and repeated acknowledgements cannot change a live result.
pub fn acknowledge(ticket: u64, result: Result<(), String>) {
    COORDINATOR.acknowledge(ticket, result);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc;
    use std::thread;

    const TEST_TIMEOUT: Duration = Duration::from_secs(5);

    fn no_wake() {}

    #[test]
    fn waits_for_teardown_and_stays_held_until_the_operation_finishes() {
        let coordinator = Coordinator::new();
        let (registered_tx, registered_rx) = mpsc::channel();
        let (result_tx, result_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        thread::scope(|scope| {
            let coordinator = &coordinator;
            scope.spawn(move || {
                let mut hold = coordinator.begin(no_wake).unwrap();
                registered_tx.send(hold.ticket).unwrap();
                result_tx.send(hold.wait(TEST_TIMEOUT)).unwrap();
                release_rx.recv_timeout(TEST_TIMEOUT).unwrap();
            });
            let ticket = registered_rx.recv_timeout(TEST_TIMEOUT).unwrap();
            assert!(matches!(
                result_rx.try_recv(),
                Err(mpsc::TryRecvError::Empty)
            ));
            assert_eq!(coordinator.pending(), Some(ticket));
            coordinator.acknowledge(ticket, Ok(()));
            assert_eq!(result_rx.recv_timeout(TEST_TIMEOUT).unwrap(), Ok(()));
            assert_eq!(coordinator.pending(), Some(ticket));
            release_tx.send(()).unwrap();
        });
        assert_eq!(coordinator.pending(), None);
    }

    #[test]
    fn timeout_releases_immediately_and_old_guard_cannot_release_the_next_hold() {
        let coordinator = Coordinator::new();
        let mut old = coordinator.begin(no_wake).unwrap();
        let old_ticket = old.ticket;
        assert!(old.wait(Duration::ZERO).is_err());
        assert_eq!(coordinator.pending(), None);
        let current = coordinator.begin(no_wake).unwrap();
        assert_ne!(old_ticket, current.ticket);
        drop(old);
        assert_eq!(coordinator.pending(), Some(current.ticket));
        drop(current);
        assert_eq!(coordinator.pending(), None);
    }

    #[test]
    fn late_acknowledgement_does_not_satisfy_a_new_request() {
        let coordinator = Coordinator::new();
        let old = coordinator.begin(no_wake).unwrap();
        let expired_ticket = old.ticket;
        drop(old);
        let mut current = coordinator.begin(no_wake).unwrap();
        thread::scope(|scope| {
            scope
                .spawn(|| coordinator.acknowledge(expired_ticket, Ok(())))
                .join()
                .unwrap();
        });
        assert!(current.wait(Duration::ZERO).is_err());
        assert_eq!(coordinator.pending(), None);
        let mut next = coordinator.begin(no_wake).unwrap();
        coordinator.acknowledge(next.ticket, Ok(()));
        assert_eq!(next.wait(Duration::ZERO), Ok(()));
    }

    #[test]
    fn failed_teardown_propagates_and_releases_the_hold() {
        let coordinator = Coordinator::new();
        let mut hold = coordinator.begin(no_wake).unwrap();
        let ticket = hold.ticket;
        let failure = "Wi-Fi client interface still exists".to_string();
        thread::scope(|scope| {
            scope.spawn(|| coordinator.acknowledge(ticket, Err(failure.clone())));
            assert_eq!(hold.wait(TEST_TIMEOUT), Err(failure.clone()));
        });
        assert_eq!(coordinator.pending(), None);
        assert!(coordinator.begin(no_wake).is_ok());
    }

    #[test]
    fn rejects_overlapping_requests_even_after_acknowledgement() {
        let coordinator = Coordinator::new();
        let mut hold = coordinator.begin(no_wake).unwrap();
        assert!(coordinator.begin(no_wake).is_err());
        coordinator.acknowledge(hold.ticket, Ok(()));
        hold.wait(Duration::ZERO).unwrap();
        assert!(coordinator.begin(no_wake).is_err());
        drop(hold);
        assert!(coordinator.begin(no_wake).is_ok());
    }

    #[test]
    fn first_acknowledgement_wins() {
        let coordinator = Coordinator::new();
        let mut hold = coordinator.begin(no_wake).unwrap();
        coordinator.acknowledge(hold.ticket, Err("Teardown failed".into()));
        coordinator.acknowledge(hold.ticket, Ok(()));
        assert_eq!(hold.wait(Duration::ZERO), Err("Teardown failed".into()));
    }

    #[test]
    fn registration_and_release_each_wake_the_supervisor_once() {
        static WAKES: AtomicUsize = AtomicUsize::new(0);
        fn wake() {
            WAKES.fetch_add(1, Ordering::SeqCst);
        }
        WAKES.store(0, Ordering::SeqCst);
        let coordinator = Coordinator::new();
        let mut hold = coordinator.begin(wake).unwrap();
        assert_eq!(WAKES.load(Ordering::SeqCst), 1);
        assert!(hold.wait(Duration::ZERO).is_err());
        assert_eq!(WAKES.load(Ordering::SeqCst), 2);
        drop(hold);
        assert_eq!(WAKES.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn supervisor_acknowledges_under_the_callers_operation_lock_and_waits_for_apply() {
        let coordinator = Coordinator::new();
        let operation = Mutex::new(());
        let (step_started_tx, step_started_rx) = mpsc::channel();
        let (finish_step_tx, finish_step_rx) = mpsc::channel();
        let (caller_waiting_tx, caller_waiting_rx) = mpsc::channel();
        let (registered_tx, registered_rx) = mpsc::channel();
        let (inspect_request_tx, inspect_request_rx) = mpsc::channel();
        let (teardown_started_tx, teardown_started_rx) = mpsc::channel();
        let (finish_teardown_tx, finish_teardown_rx) = mpsc::channel();
        let (apply_started_tx, apply_started_rx) = mpsc::channel();
        let (inspect_hold_tx, inspect_hold_rx) = mpsc::channel();
        let (held_tx, held_rx) = mpsc::channel();
        let (finish_apply_tx, finish_apply_rx) = mpsc::channel();
        let (released_tx, released_rx) = mpsc::channel();
        let (resume_tx, resume_rx) = mpsc::channel();

        thread::scope(|scope| {
            let coordinator = &coordinator;
            let operation = &operation;
            let supervisor = scope.spawn(move || {
                let step = operation.lock().unwrap();
                step_started_tx.send(()).unwrap();
                finish_step_rx.recv_timeout(TEST_TIMEOUT).unwrap();
                drop(step);

                inspect_request_rx.recv_timeout(TEST_TIMEOUT).unwrap();
                let ticket = coordinator.pending().unwrap();
                assert!(matches!(
                    operation.try_lock(),
                    Err(std::sync::TryLockError::WouldBlock)
                ));
                // The pending request must be handled before trying to acquire
                // the operation lock: its caller owns that lock while waiting.
                teardown_started_tx.send(()).unwrap();
                finish_teardown_rx.recv_timeout(TEST_TIMEOUT).unwrap();
                coordinator.acknowledge(ticket, Ok(()));

                inspect_hold_rx.recv_timeout(TEST_TIMEOUT).unwrap();
                assert_eq!(coordinator.pending(), Some(ticket));
                assert!(matches!(
                    operation.try_lock(),
                    Err(std::sync::TryLockError::WouldBlock)
                ));
                held_tx.send(()).unwrap();

                resume_rx.recv_timeout(TEST_TIMEOUT).unwrap();
                assert_eq!(coordinator.pending(), None);
                let _next_step = operation.try_lock().unwrap();
            });

            step_started_rx.recv_timeout(TEST_TIMEOUT).unwrap();
            let caller = scope.spawn(move || {
                caller_waiting_tx.send(()).unwrap();
                let operation = operation.lock().unwrap();
                let mut hold = coordinator.begin(no_wake).unwrap();
                registered_tx.send(hold.ticket).unwrap();
                hold.wait(TEST_TIMEOUT).unwrap();
                apply_started_tx.send(()).unwrap();
                finish_apply_rx.recv_timeout(TEST_TIMEOUT).unwrap();
                drop(hold);
                drop(operation);
                released_tx.send(()).unwrap();
            });

            caller_waiting_rx.recv_timeout(TEST_TIMEOUT).unwrap();
            assert_eq!(coordinator.pending(), None);
            assert!(matches!(
                registered_rx.try_recv(),
                Err(mpsc::TryRecvError::Empty)
            ));
            finish_step_tx.send(()).unwrap();
            let ticket = registered_rx.recv_timeout(TEST_TIMEOUT).unwrap();
            inspect_request_tx.send(()).unwrap();
            teardown_started_rx.recv_timeout(TEST_TIMEOUT).unwrap();
            assert!(matches!(
                apply_started_rx.try_recv(),
                Err(mpsc::TryRecvError::Empty)
            ));
            finish_teardown_tx.send(()).unwrap();
            apply_started_rx.recv_timeout(TEST_TIMEOUT).unwrap();
            assert_eq!(coordinator.pending(), Some(ticket));
            inspect_hold_tx.send(()).unwrap();
            held_rx.recv_timeout(TEST_TIMEOUT).unwrap();
            finish_apply_tx.send(()).unwrap();
            released_rx.recv_timeout(TEST_TIMEOUT).unwrap();
            resume_tx.send(()).unwrap();
            caller.join().unwrap();
            supervisor.join().unwrap();
        });
    }
}
