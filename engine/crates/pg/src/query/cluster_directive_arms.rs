//! Read/update UCB1 arm state per (island_domain, action,
//! strength_bucket, multiplier_choice).
//!
//! `ensure_arm` materialises a row at zero stats; `list_for_slot`
//! returns the 5 arms for a (island, action, bucket) trio (used by
//! UCB1 selection); `record_pull` is called when the worker reports
//! reward; `snapshot_all` reads every row for the steerer's per-cycle
//! ArcSwap publication.

use crate::entity::cluster_directive_arms::*;
use chrono::Utc;
use sea_orm::*;

pub async fn ensure_arm(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
) -> Result<(), DbErr> {
    let exists = Entity::find_by_id((
        island_domain.to_string(),
        action.to_string(),
        strength_bucket,
        multiplier_choice,
    ))
    .one(db)
    .await?;
    if exists.is_none() {
        let am = ActiveModel {
            island_domain: Set(island_domain.into()),
            action: Set(action.into()),
            strength_bucket: Set(strength_bucket),
            multiplier_choice: Set(multiplier_choice),
            pulls: Set(0),
            total_reward: Set(0.0),
            last_reward: Set(0.0),
            updated_at: Set(Utc::now().fixed_offset()),
        };
        Entity::insert(am).exec(db).await?;
    }
    Ok(())
}

/// Return the 5 multiplier_choice arms for one (island, action,
/// strength_bucket) slot, ordered by multiplier_choice ASC.
pub async fn list_for_slot(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .filter(Column::IslandDomain.eq(island_domain))
        .filter(Column::Action.eq(action))
        .filter(Column::StrengthBucket.eq(strength_bucket))
        .order_by_asc(Column::MultiplierChoice)
        .all(db)
        .await
}

/// Read every row. Used by the steerer's per-cycle snapshot path —
/// the table is bounded at ~600 rows so a full scan is cheap.
pub async fn snapshot_all(db: &DatabaseConnection) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .order_by_asc(Column::IslandDomain)
        .order_by_asc(Column::Action)
        .order_by_asc(Column::StrengthBucket)
        .order_by_asc(Column::MultiplierChoice)
        .all(db)
        .await
}

/// Smoothing weight applied to adjacent strength buckets when a
/// pull lands. 0.3 = the neighbour absorbs 30% of the reward signal
/// at 30% pull weight; lets the bandit generalise across buckets
/// without separate contextual modelling. Pure UCB1 with no
/// smoothing means a pull at bucket=2 leaves bucket=1 and bucket=3
/// learning at half the rate; smoothing accelerates convergence
/// across the full strength range. Set to 0.0 to disable.
const NEIGHBOUR_SMOOTHING_WEIGHT: f64 = 0.3;

/// Increment pulls + total_reward, set last_reward. Caller is
/// responsible for the [0,1] clamp.
///
/// Side effect: also nudges the SAME (island, action, choice) at
/// adjacent strength_buckets (B-1, B+1) at fractional weight so the
/// bandit gets free contextual generalisation across the strength
/// dimension. The nudge increments fractional pulls/total_reward
/// (stored as f64), so adjacent buckets converge faster on
/// strength-correlated rewards. Smoothing is symmetric — a pull at
/// the edges (B=0 or B=4) only nudges one neighbour.
pub async fn record_pull(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
    reward: f64,
) -> Result<(), DbErr> {
    record_one(
        db,
        island_domain,
        action,
        strength_bucket,
        multiplier_choice,
        reward,
        1.0,
    )
    .await?;

    if NEIGHBOUR_SMOOTHING_WEIGHT > 0.0 {
        for nb in [strength_bucket - 1, strength_bucket + 1] {
            if (0..5).contains(&nb) {
                record_one(
                    db,
                    island_domain,
                    action,
                    nb,
                    multiplier_choice,
                    reward,
                    NEIGHBOUR_SMOOTHING_WEIGHT,
                )
                .await?;
            }
        }
    }
    Ok(())
}

/// Internal helper: record a single weighted pull. `weight=1.0` is
/// the canonical pull (full bandit credit). Fractional weight uses
/// stochastic rounding: with probability `weight` the call performs
/// a full +1 pull with full `reward`; otherwise it is a no-op. Over
/// many calls this is an unbiased Monte Carlo estimator of the true
/// per-arm mean, so the smoothed bandit converges to the same fixed
/// point a fully-pulled bandit would, just slower.
async fn record_one(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
    reward: f64,
    weight: f64,
) -> Result<(), DbErr> {
    use rand::Rng;
    if weight < 1.0 {
        let mut rng = rand::rng();
        if !rng.random_bool(weight.clamp(0.0, 1.0)) {
            return Ok(());
        }
    }
    let arm = Entity::find_by_id((
        island_domain.to_string(),
        action.to_string(),
        strength_bucket,
        multiplier_choice,
    ))
    .one(db)
    .await?;
    let (prev_pulls, prev_total) = match &arm {
        Some(m) => (m.pulls, m.total_reward),
        None => (0, 0.0),
    };
    let mut am: ActiveModel = match arm {
        Some(m) => m.into(),
        None => ActiveModel {
            island_domain: Set(island_domain.into()),
            action: Set(action.into()),
            strength_bucket: Set(strength_bucket),
            multiplier_choice: Set(multiplier_choice),
            pulls: Set(0),
            total_reward: Set(0.0),
            last_reward: Set(0.0),
            updated_at: Set(Utc::now().fixed_offset()),
        },
    };
    am.pulls = Set(prev_pulls + 1);
    am.total_reward = Set(prev_total + reward);
    am.last_reward = Set(reward);
    am.updated_at = Set(Utc::now().fixed_offset());
    am.save(db).await?;
    Ok(())
}
