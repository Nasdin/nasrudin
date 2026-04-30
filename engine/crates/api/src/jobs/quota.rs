//! Pure quota math + explorer-floor calculations.
//!
//! No DB or async — these are decision functions used both at claim
//! time (do we have headroom to award this paid job?) and at
//! heartbeat time (has this job exhausted its allowance?).

/// Floor of explorer-fleet lake slots. We never let paid jobs eat the
/// entire cluster: at minimum, 10% (rounded down) of total slots, but
/// always ≥2 so a single 8-core box still leaves an explorer alive.
pub fn min_explorer_slots(total_lake_slots: u32) -> u32 {
    std::cmp::max(2, (total_lake_slots as f32 * 0.10).floor() as u32)
}

/// `true` iff awarding the paid load `slots_on_paid_jobs` still
/// leaves enough free capacity to honor `min_explorer_slots`.
pub fn floor_satisfied(total_lake_slots: u32, slots_on_paid_jobs: u32) -> bool {
    let free = total_lake_slots.saturating_sub(slots_on_paid_jobs);
    free >= min_explorer_slots(total_lake_slots)
}

/// Slot-hours still owed to a job before `budget_exhausted` fires.
/// Returns 0.0 (never negative) when consumed has overshot.
pub fn quota_remaining_hours(quota: i32, consumed: f32) -> f32 {
    (quota as f32 - consumed).max(0.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floor_is_at_least_two() {
        assert_eq!(min_explorer_slots(0), 2);
        assert_eq!(min_explorer_slots(5), 2);
        assert_eq!(min_explorer_slots(20), 2);
    }

    #[test]
    fn floor_is_ten_percent_above_twenty() {
        assert_eq!(min_explorer_slots(50), 5);
        assert_eq!(min_explorer_slots(100), 10);
        assert_eq!(min_explorer_slots(257), 25);
    }

    #[test]
    fn floor_satisfied_simple() {
        assert!(floor_satisfied(50, 40)); // 50 total, 40 paid → 10 free, floor=5
        assert!(!floor_satisfied(50, 46)); // 4 free < 5 floor
    }

    #[test]
    fn quota_remaining_nonnegative() {
        assert_eq!(quota_remaining_hours(96, 100.0), 0.0);
        assert_eq!(quota_remaining_hours(96, 50.0), 46.0);
        assert_eq!(quota_remaining_hours(0, 0.0), 0.0);
    }
}
