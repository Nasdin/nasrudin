//! UCB1 multi-armed bandit over per-cluster directive multipliers.
//!
//! Each (island_domain, action, strength_bucket) slot holds 5 arms
//! (one per multiplier_choice). The bandit picks the multiplier that
//! the cluster's mean-fitness delta one chunk later rewards. Worker
//! attributes the reward via `centroid_skeleton_hash` matching;
//! unmatched directives produce no reward and don't update arms.
//!
//! Cold-start fallback: until each slot has ≥COLD_START_PULL_THRESHOLD
//! cumulative pulls, the worker uses a static strength→choice mapping
//! instead of UCB1, so the first few cycles produce the same
//! behaviour the static-formula baseline did.

use crate::steerer::schema::ClusterAction;
use sea_orm::DatabaseConnection;

pub const STRENGTH_BUCKETS: u8 = 5;
pub const MULTIPLIER_CHOICES: u8 = 5;
pub const COLD_START_PULL_THRESHOLD: i64 = 15; // 3 pulls × 5 arms
pub const REWARD_BIAS: f32 = 0.5;
pub const HASH_MATCH_THRESHOLD: f32 = 0.10;

pub const BOOST_MULTIPLIERS: [f32; 5] = [1.00, 1.25, 1.50, 1.75, 2.00];
pub const EXPLOIT_MULTIPLIERS: [f32; 5] = [1.00, 1.25, 1.50, 1.75, 2.00];
pub const DIVERSIFY_FRACTIONS: [f32; 5] = [0.00, 0.10, 0.20, 0.30, 0.50];
pub const KILL_FRACTIONS: [f32; 5] = [0.00, 0.10, 0.20, 0.30, 0.50];

pub const ACTIONS: &[ClusterAction] = &[
    ClusterAction::Boost,
    ClusterAction::Exploit,
    ClusterAction::Diversify,
    ClusterAction::Kill,
];

pub fn action_str(action: ClusterAction) -> &'static str {
    match action {
        ClusterAction::Boost => "boost",
        ClusterAction::Exploit => "exploit",
        ClusterAction::Diversify => "diversify",
        ClusterAction::Kill => "kill",
    }
}

pub fn parse_action(s: &str) -> Option<ClusterAction> {
    match s {
        "boost" => Some(ClusterAction::Boost),
        "exploit" => Some(ClusterAction::Exploit),
        "diversify" => Some(ClusterAction::Diversify),
        "kill" => Some(ClusterAction::Kill),
        _ => None,
    }
}

/// Map a continuous strength in [0, 1] to one of 5 buckets.
/// Strength is clamped first so out-of-range LLM emissions don't
/// blow past the table.
pub fn bucketize_strength(strength: f32) -> u8 {
    let s = strength.clamp(0.0, 1.0);
    ((s * 5.0).floor() as u8).min(4)
}

/// Resolve a multiplier_choice index to its concrete multiplier value
/// for the given action. Out-of-range choice saturates at index 4.
pub fn lookup_multiplier_value(action: ClusterAction, choice: u8) -> f32 {
    let table: &[f32; 5] = match action {
        ClusterAction::Boost => &BOOST_MULTIPLIERS,
        ClusterAction::Exploit => &EXPLOIT_MULTIPLIERS,
        ClusterAction::Diversify => &DIVERSIFY_FRACTIONS,
        ClusterAction::Kill => &KILL_FRACTIONS,
    };
    table[(choice as usize).min(4)]
}

#[derive(Debug, Clone)]
pub struct DirectiveArmStat {
    pub multiplier_choice: u8,
    pub pulls: i64,
    pub total_reward: f64,
}

/// UCB1 selection over a slot's 5 arms. Cold-start (pulls==0) wins
/// before exploitation; otherwise classic UCB1 with `N` = sum of pulls
/// across the slot (local exploration term, not global).
pub fn select_multiplier(arms: &[DirectiveArmStat]) -> u8 {
    if arms.is_empty() {
        return 0;
    }
    if let Some(unpulled) = arms.iter().find(|a| a.pulls == 0) {
        return unpulled.multiplier_choice;
    }
    let total_pulls: i64 = arms.iter().map(|a| a.pulls).sum();
    let ln_n = (total_pulls as f64).ln();
    let mut best = arms[0].multiplier_choice;
    let mut best_score = f64::NEG_INFINITY;
    for a in arms {
        let mean = a.total_reward / a.pulls as f64;
        let exploration = (2.0 * ln_n / a.pulls as f64).sqrt();
        let score = mean + exploration;
        if score > best_score {
            best_score = score;
            best = a.multiplier_choice;
        }
    }
    best
}

/// Affine reward map: delta in roughly [-1, 1] → reward in [0, 1].
/// The +0.5 bias keeps a single-chunk regression from saturating an
/// arm to zero.
pub fn compute_reward(fitness_delta: f32) -> f64 {
    (fitness_delta + REWARD_BIAS).clamp(0.0, 1.0) as f64
}

/// Static fallback used until a slot has ≥COLD_START_PULL_THRESHOLD
/// pulls. Linearly maps strength ∈ [0, 1] across the 5-entry table.
pub fn strength_to_static_choice(strength: f32) -> u8 {
    bucketize_strength(strength)
}

/// Materialise every (island_domain, action, strength_bucket,
/// multiplier_choice) row at zero stats. Idempotent — pre-existing
/// rows are left alone. Called once at API boot, parallels
/// `bandit::ensure_all_arms` for the K-bandit.
pub async fn ensure_all_arms(db: &DatabaseConnection) -> Result<(), sea_orm::DbErr> {
    for &domain in crate::steerer::bandit::ISLAND_DOMAINS {
        for &action in ACTIONS {
            for bucket in 0..STRENGTH_BUCKETS as i16 {
                for choice in 0..MULTIPLIER_CHOICES as i16 {
                    nasrudin_pg::query::cluster_directive_arms::ensure_arm(
                        db,
                        domain,
                        action_str(action),
                        bucket,
                        choice,
                    )
                    .await?;
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lookup_returns_table_value() {
        assert!((lookup_multiplier_value(ClusterAction::Boost, 0) - 1.00).abs() < 1e-6);
        assert!((lookup_multiplier_value(ClusterAction::Boost, 4) - 2.00).abs() < 1e-6);
        assert!((lookup_multiplier_value(ClusterAction::Diversify, 0) - 0.00).abs() < 1e-6);
        assert!((lookup_multiplier_value(ClusterAction::Diversify, 4) - 0.50).abs() < 1e-6);
    }

    #[test]
    fn lookup_clamps_out_of_range() {
        assert!(
            (lookup_multiplier_value(ClusterAction::Boost, 99) - 2.00).abs() < 1e-6
        );
    }

    #[test]
    fn bucketize_strength_boundaries() {
        assert_eq!(bucketize_strength(0.0), 0);
        assert_eq!(bucketize_strength(0.199), 0);
        assert_eq!(bucketize_strength(0.2), 1);
        assert_eq!(bucketize_strength(0.4), 2);
        assert_eq!(bucketize_strength(0.6), 3);
        assert_eq!(bucketize_strength(0.8), 4);
        assert_eq!(bucketize_strength(1.0), 4);
    }

    #[test]
    fn bucketize_strength_clamps() {
        assert_eq!(bucketize_strength(-0.1), 0);
        assert_eq!(bucketize_strength(1.5), 4);
    }

    #[test]
    fn select_multiplier_cold_start_picks_unpulled() {
        let arms = vec![
            DirectiveArmStat {
                multiplier_choice: 0,
                pulls: 4,
                total_reward: 2.0,
            },
            DirectiveArmStat {
                multiplier_choice: 1,
                pulls: 0,
                total_reward: 0.0,
            },
            DirectiveArmStat {
                multiplier_choice: 2,
                pulls: 3,
                total_reward: 1.5,
            },
        ];
        assert_eq!(select_multiplier(&arms), 1);
    }

    #[test]
    fn select_multiplier_picks_highest_score() {
        let arms = vec![
            DirectiveArmStat {
                multiplier_choice: 0,
                pulls: 100,
                total_reward: 90.0,
            },
            DirectiveArmStat {
                multiplier_choice: 1,
                pulls: 100,
                total_reward: 50.0,
            },
        ];
        assert_eq!(select_multiplier(&arms), 0);
    }

    #[test]
    fn select_multiplier_explores_low_pull_arm() {
        let arms = vec![
            DirectiveArmStat {
                multiplier_choice: 0,
                pulls: 1000,
                total_reward: 800.0,
            },
            DirectiveArmStat {
                multiplier_choice: 1,
                pulls: 5,
                total_reward: 3.5,
            },
        ];
        assert_eq!(select_multiplier(&arms), 1);
    }

    #[test]
    fn select_multiplier_empty_returns_default() {
        assert_eq!(select_multiplier(&[]), 0);
    }

    #[test]
    fn compute_reward_centers_on_half() {
        let r = compute_reward(0.0);
        assert!((r - 0.5).abs() < 1e-6);
    }

    #[test]
    fn compute_reward_clamps() {
        assert_eq!(compute_reward(5.0), 1.0);
        assert_eq!(compute_reward(-5.0), 0.0);
    }

    #[test]
    fn parse_and_action_str_round_trip() {
        for &a in ACTIONS {
            let s = action_str(a);
            assert_eq!(parse_action(s), Some(a));
        }
        assert_eq!(parse_action("explode"), None);
    }
}
