//! Cluster-capacity tracker.
//!
//! Workers report their available `lake_slots` on every claim; the
//! tracker keeps a (timestamp, count) per worker_id and sums the
//! "fresh" entries (last seen ≤5 min ago) to produce
//! `total_lake_slots()`. A separate atomic counter sums the slots
//! currently committed to paid `conjecture_jobs` so the claim path
//! can enforce the explorer floor without a DB round-trip.

use dashmap::DashMap;
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant};

const FRESH_WINDOW: Duration = Duration::from_secs(300);

pub struct CapacityTracker {
    workers: DashMap<String, (Instant, u32)>,
    paid_slots: AtomicU32,
}

impl Default for CapacityTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl CapacityTracker {
    pub fn new() -> Self {
        Self {
            workers: DashMap::new(),
            paid_slots: AtomicU32::new(0),
        }
    }

    /// Record a worker's currently-available lake slot count. Called
    /// on every `/api/jobs/claim` so the freshness window is always
    /// at most one chunk-boundary cadence behind reality.
    pub fn report_worker(&self, worker_id: &str, slots: u32) {
        self.workers
            .insert(worker_id.to_owned(), (Instant::now(), slots));
    }

    /// Record that `n` lake slots are now committed to a paid job.
    /// Counterpart to `release_paid_slots` on heartbeat-exhausted /
    /// release / cancel paths.
    pub fn add_paid_slots(&self, n: u32) {
        self.paid_slots.fetch_add(n, Ordering::SeqCst);
    }

    pub fn release_paid_slots(&self, n: u32) {
        // saturating_sub via fetch_update so we never underflow even
        // under double-release races.
        let _ = self
            .paid_slots
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |cur| {
                Some(cur.saturating_sub(n))
            });
    }

    /// Sum of every worker's reported slot count whose last report
    /// is within the freshness window. Stale workers age out.
    pub fn total_lake_slots(&self) -> u32 {
        let cutoff = Instant::now() - FRESH_WINDOW;
        self.workers
            .iter()
            .filter(|e| e.value().0 >= cutoff)
            .map(|e| e.value().1)
            .sum()
    }

    pub fn paid_slots(&self) -> u32 {
        self.paid_slots.load(Ordering::SeqCst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn total_sums_recent() {
        let t = CapacityTracker::new();
        t.report_worker("a", 4);
        t.report_worker("b", 8);
        assert_eq!(t.total_lake_slots(), 12);
    }

    #[test]
    fn paid_slot_round_trip() {
        let t = CapacityTracker::new();
        t.add_paid_slots(4);
        t.add_paid_slots(4);
        assert_eq!(t.paid_slots(), 8);
        t.release_paid_slots(4);
        assert_eq!(t.paid_slots(), 4);
        // saturating_sub: never underflows.
        t.release_paid_slots(99);
        assert_eq!(t.paid_slots(), 0);
    }

    #[test]
    fn report_overwrites_per_worker() {
        let t = CapacityTracker::new();
        t.report_worker("a", 4);
        t.report_worker("a", 12);
        assert_eq!(t.total_lake_slots(), 12);
    }
}
