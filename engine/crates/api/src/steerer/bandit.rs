//! UCB1 multi-armed bandit over K (number of clusters per island).
//!
//! Arms: K ∈ K_VALUES. Per-island state lives in `cluster_bandit_arms`.
//! Selection is deterministic given arm state. Reward is computed from
//! the most recent `cluster_reports` rows attributed to the K that
//! produced them.
//!
//! The bandit and the LLM are decoupled by design: bandit handles
//! structural decisions (how many clusters per island), the LLM handles
//! tactical decisions (per-cluster `Boost`/`Exploit`/`Diversify`/`Kill`
//! directives addressed by `centroid_skeleton_hash`).

use chrono::{DateTime, Utc};
use sea_orm::DatabaseConnection;
use sea_orm::DbErr;

/// K options offered to the bandit. Bounded to a range that keeps
/// k-means cheap (≤12) while giving the bandit room to discover that
/// some islands prefer a coarser or finer split.
pub const K_VALUES: &[i16] = &[2, 3, 4, 5, 6, 7, 8, 10, 12];

/// Island domains the bandit covers. Mirrors the GA's island ring.
pub const ISLAND_DOMAINS: &[&str] = &[
    "special_relativity",
    "electromagnetism",
    "quantum_mechanics",
    "thermodynamics",
    "classical_mechanics",
    "general_relativity",
];

/// Default K when there's no bandit state yet (cold boot, no reports).
pub const DEFAULT_K: u32 = 6;

#[derive(Debug, Clone)]
pub struct ArmStat {
    pub k: i16,
    pub pulls: i64,
    pub total_reward: f64,
}

/// UCB1 selection: pick the arm with highest mean reward + exploration.
/// Cold-start: any arm with `pulls == 0` wins immediately so every K
/// gets at least one trial before exploitation kicks in.
pub fn select_k_ucb1(arms: &[ArmStat]) -> i16 {
    if arms.is_empty() {
        return DEFAULT_K as i16;
    }
    if let Some(unpulled) = arms.iter().find(|a| a.pulls == 0) {
        return unpulled.k;
    }
    let total_pulls: i64 = arms.iter().map(|a| a.pulls).sum();
    let ln_n = (total_pulls as f64).ln();
    let mut best_k = arms[0].k;
    let mut best_score = f64::NEG_INFINITY;
    for a in arms {
        let mean = a.total_reward / a.pulls as f64;
        let exploration = (2.0 * ln_n / a.pulls as f64).sqrt();
        let score = mean + exploration;
        if score > best_score {
            best_score = score;
            best_k = a.k;
        }
    }
    best_k
}

const W_VERIFIED: f64 = 0.40;
const W_SILHOUETTE: f64 = 0.25;
const W_NOVELTY: f64 = 0.20;
const W_STAGNATION: f64 = 0.15;

pub struct RewardInputs {
    pub verified_per_pop: f64,
    pub mean_silhouette: f64,
    pub novelty_delta: f64,
    pub stagnation_penalty: f64,
}

/// Composite reward bounded to [0, 1]. Weights are constants — exposing
/// them to the LLM would create reward-hacking pressure and isn't worth
/// the flexibility.
pub fn compute_reward(r: RewardInputs) -> f64 {
    let raw = W_VERIFIED * r.verified_per_pop
        + W_SILHOUETTE * r.mean_silhouette
        + W_NOVELTY * r.novelty_delta
        - W_STAGNATION * r.stagnation_penalty;
    raw.clamp(0.0, 1.0)
}

/// Ensure all (ISLAND_DOMAINS × K_VALUES) arm rows exist with zero stats.
/// Idempotent. Called once at API boot.
pub async fn ensure_all_arms(db: &DatabaseConnection) -> Result<(), DbErr> {
    for domain in ISLAND_DOMAINS {
        for &k in K_VALUES {
            nasrudin_pg::query::cluster_bandit_arms::ensure_arm(db, domain, k).await?;
        }
    }
    Ok(())
}

/// Read all arms for `island_domain`. Returns empty if none exist.
pub async fn load_arms(
    db: &DatabaseConnection,
    island_domain: &str,
) -> Result<Vec<ArmStat>, DbErr> {
    let rows = nasrudin_pg::query::cluster_bandit_arms::list_for_island(db, island_domain).await?;
    Ok(rows
        .into_iter()
        .map(|m| ArmStat {
            k: m.k_value,
            pulls: m.pulls,
            total_reward: m.total_reward,
        })
        .collect())
}

/// Read recent `cluster_reports` rows for `island_domain` between
/// `[since, now)` filtered to `k_used` and aggregate to `RewardInputs`.
/// If no rows in window, returns a neutral input so the bandit doesn't
/// punish the K just because workers haven't reported yet.
pub async fn extract_reward_inputs(
    db: &DatabaseConnection,
    island_domain: &str,
    k_used: i16,
    since: DateTime<Utc>,
) -> Result<RewardInputs, DbErr> {
    let rows = nasrudin_pg::query::cluster_reports::recent_for_island_with_k(
        db,
        island_domain,
        k_used,
        since,
    )
    .await?;
    if rows.is_empty() {
        return Ok(RewardInputs {
            verified_per_pop: 0.5,
            mean_silhouette: 0.0,
            novelty_delta: 0.0,
            stagnation_penalty: 0.0,
        });
    }
    let summaries: Vec<serde_json::Value> = rows.iter().map(|r| r.summary.clone()).collect();
    let mean_silhouette = avg_field(&summaries, "silhouette");
    let novelty_delta = avg_field(&summaries, "novelty_trend");
    let stagnation = avg_field(&summaries, "stagnation_chunks") / 10.0;
    // Until /api/cluster-report carries verified-counts directly, we
    // proxy verified_per_pop with the cluster's mean_fitness — high
    // mean fitness across clusters strongly correlates with high
    // discovery rate in practice.
    let verified_per_pop = avg_field(&summaries, "mean_fitness");
    Ok(RewardInputs {
        verified_per_pop,
        mean_silhouette: (mean_silhouette + 1.0) / 2.0, // map [-1,1] → [0,1]
        novelty_delta,
        stagnation_penalty: stagnation,
    })
}

fn avg_field(rows: &[serde_json::Value], key: &str) -> f64 {
    let vals: Vec<f64> = rows
        .iter()
        .filter_map(|r| r.get(key).and_then(|v| v.as_f64()))
        .collect();
    if vals.is_empty() {
        0.0
    } else {
        vals.iter().sum::<f64>() / vals.len() as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cold_start_picks_unpulled_arm() {
        let arms = vec![
            ArmStat {
                k: 4,
                pulls: 5,
                total_reward: 2.5,
            },
            ArmStat {
                k: 6,
                pulls: 0,
                total_reward: 0.0,
            },
            ArmStat {
                k: 8,
                pulls: 3,
                total_reward: 1.5,
            },
        ];
        assert_eq!(select_k_ucb1(&arms), 6);
    }

    #[test]
    fn ucb1_picks_highest_score() {
        let arms = vec![
            ArmStat {
                k: 4,
                pulls: 100,
                total_reward: 90.0,
            },
            ArmStat {
                k: 6,
                pulls: 100,
                total_reward: 50.0,
            },
        ];
        assert_eq!(select_k_ucb1(&arms), 4);
    }

    #[test]
    fn ucb1_explores_low_pull_arm() {
        let arms = vec![
            ArmStat {
                k: 4,
                pulls: 1000,
                total_reward: 800.0,
            },
            ArmStat {
                k: 6,
                pulls: 5,
                total_reward: 3.5,
            },
        ];
        assert_eq!(select_k_ucb1(&arms), 6);
    }

    #[test]
    fn empty_arms_returns_default() {
        assert_eq!(select_k_ucb1(&[]), DEFAULT_K as i16);
    }

    #[test]
    fn reward_combines_components_clamped_to_unit() {
        let r = compute_reward(RewardInputs {
            verified_per_pop: 0.4,
            mean_silhouette: 0.6,
            novelty_delta: 0.2,
            stagnation_penalty: 0.1,
        });
        // 0.4*0.4 + 0.25*0.6 + 0.2*0.2 + (-0.15*0.1) = 0.335
        assert!((r - 0.335).abs() < 1e-6);
    }

    #[test]
    fn reward_clamps_to_zero_one() {
        let r = compute_reward(RewardInputs {
            verified_per_pop: 5.0,
            mean_silhouette: 5.0,
            novelty_delta: 5.0,
            stagnation_penalty: 0.0,
        });
        assert!(r <= 1.0);
        let r2 = compute_reward(RewardInputs {
            verified_per_pop: -5.0,
            mean_silhouette: -5.0,
            novelty_delta: -5.0,
            stagnation_penalty: 5.0,
        });
        assert!(r2 >= 0.0);
    }
}
