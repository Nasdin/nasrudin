//! `PlanTier` is the single source of truth for what a paid user can do.
//! The `users.plan_tier` text column gets mapped through `from_db`, and
//! quotas (API/day, targeted searches/period) are looked up via `quotas()`.
//!
//! Unknown plan_tier values degrade to `Free` rather than panic — a
//! mistyped or stale row must not lock a user out of the read corpus.

use chrono::{DateTime, Datelike, TimeZone, Utc};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PlanTier {
    Free,
    Researcher,
    Institution,
    Enterprise,
}

impl PlanTier {
    pub fn from_db(s: &str) -> Self {
        match s {
            "researcher" => Self::Researcher,
            "institution" => Self::Institution,
            "enterprise" => Self::Enterprise,
            _ => Self::Free,
        }
    }

    pub fn as_db(self) -> &'static str {
        match self {
            Self::Free => "free",
            Self::Researcher => "researcher",
            Self::Institution => "institution",
            Self::Enterprise => "enterprise",
        }
    }

    pub fn quotas(self) -> Quotas {
        match self {
            Self::Free => Quotas {
                api_per_day: 1_000,
                targeted_searches_per_period: 0,
                library_max: 50,
                research_credits_per_period: 0,
            },
            Self::Researcher => Quotas {
                api_per_day: 10_000,
                targeted_searches_per_period: 10,
                library_max: u32::MAX,
                // One credit = one paid conjecture (96 lake-slot-hours
                // each). 10/period matches targeted_searches_per_period
                // and the pricing-page promise.
                research_credits_per_period: 10,
            },
            Self::Institution => Quotas {
                api_per_day: 250_000,
                targeted_searches_per_period: 200,
                library_max: u32::MAX,
                research_credits_per_period: 200,
            },
            Self::Enterprise => Quotas {
                api_per_day: u32::MAX,
                targeted_searches_per_period: u32::MAX,
                library_max: u32::MAX,
                research_credits_per_period: u32::MAX,
            },
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Quotas {
    pub api_per_day: u32,
    pub targeted_searches_per_period: u32,
    pub library_max: u32,
    /// Number of paid Researcher conjectures granted at the start of
    /// each billing period. Lose-it-or-use-it (mirrors
    /// `targeted_searches_per_period`).
    pub research_credits_per_period: u32,
}

/// The start of the user's current quota period. Paid users get the
/// Stripe billing period (anchored on `plan_cycle_start`); free users
/// get the first of the current UTC month so their counters reset
/// predictably without a Stripe sub.
pub fn period_start(plan_cycle_start: Option<DateTime<Utc>>, now: DateTime<Utc>) -> DateTime<Utc> {
    if let Some(cycle) = plan_cycle_start {
        return cycle;
    }
    Utc.with_ymd_and_hms(now.year(), now.month(), 1, 0, 0, 0)
        .unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn free_tier_has_zero_targeted_searches() {
        assert_eq!(PlanTier::Free.quotas().targeted_searches_per_period, 0);
    }

    #[test]
    fn researcher_quotas_match_pricing_page() {
        let q = PlanTier::Researcher.quotas();
        assert_eq!(q.api_per_day, 10_000);
        assert_eq!(q.targeted_searches_per_period, 10);
    }

    #[test]
    fn from_db_unknown_falls_back_to_free() {
        assert_eq!(PlanTier::from_db("garbage"), PlanTier::Free);
        assert_eq!(PlanTier::from_db(""), PlanTier::Free);
    }

    #[test]
    fn from_db_round_trips_known_tiers() {
        for tier in [
            PlanTier::Free,
            PlanTier::Researcher,
            PlanTier::Institution,
            PlanTier::Enterprise,
        ] {
            assert_eq!(PlanTier::from_db(tier.as_db()), tier);
        }
    }

    #[test]
    fn period_start_for_free_user_is_first_of_month() {
        let now = Utc.with_ymd_and_hms(2026, 4, 29, 12, 0, 0).unwrap();
        let start = period_start(None, now);
        assert_eq!(start, Utc.with_ymd_and_hms(2026, 4, 1, 0, 0, 0).unwrap());
    }

    #[test]
    fn period_start_for_paid_user_is_their_cycle_start() {
        let now = Utc.with_ymd_and_hms(2026, 4, 29, 12, 0, 0).unwrap();
        let cycle = Utc.with_ymd_and_hms(2026, 4, 17, 0, 0, 0).unwrap();
        assert_eq!(period_start(Some(cycle), now), cycle);
    }
}
