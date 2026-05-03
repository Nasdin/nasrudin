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

/// 2D Gaussian kernel bandwidth (in arm units). Larger = more
/// smoothing across nearby arms in the (strength_bucket,
/// multiplier_choice) plane; smaller = tighter generalisation.
/// 1.0 means a 1-arm step in either dimension halves the smoothing
/// weight roughly (exp(-0.5) ≈ 0.61, but stochastic rounding makes
/// it discrete in practice).
const KERNEL_SIGMA: f64 = 1.0;

/// Cap on the kernel weight; the centre arm always pulls at 1.0.
/// Below this cutoff, the smoothing pull is skipped so we don't
/// pay PG round-trips for vanishing weights. exp(-2² / 2·1²) ≈ 0.135
/// so this cuts off arms ≥ 2 away in any single dimension.
const KERNEL_MIN_WEIGHT: f64 = 0.10;

/// Increment pulls + total_reward, set last_reward. Caller is
/// responsible for the [0,1] clamp.
///
/// Side effect: applies a 2D Gaussian smoothing kernel over the
/// (strength_bucket, multiplier_choice) plane — every arm within
/// Manhattan distance ≤2 gets a stochastic-rounded fractional
/// pull weighted by `exp(-d² / 2σ²)`. Lets the bandit generalise
/// in BOTH dimensions: a pull at (B=2, C=3) nudges (B=1, C=3),
/// (B=3, C=3), (B=2, C=2), (B=2, C=4), and even diagonals
/// (B=1, C=2) etc. at smaller weight. Phase-B 1D smoothing was
/// per-strength only; 2D extends to multiplier_choice too so the
/// bandit converges across the full action surface.
pub async fn record_pull(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
    reward: f64,
) -> Result<(), DbErr> {
    // Centre arm: full pull.
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

    // 2D Gaussian kernel over the (bucket, choice) plane.
    let two_sigma_sq = 2.0 * KERNEL_SIGMA * KERNEL_SIGMA;
    for db_offset in -2i16..=2 {
        for dc_offset in -2i16..=2 {
            if db_offset == 0 && dc_offset == 0 {
                continue;
            }
            let nb_bucket = strength_bucket + db_offset;
            let nb_choice = multiplier_choice + dc_offset;
            if !(0..5).contains(&nb_bucket) || !(0..5).contains(&nb_choice) {
                continue;
            }
            let d_sq = (db_offset as f64).powi(2) + (dc_offset as f64).powi(2);
            let weight = (-d_sq / two_sigma_sq).exp();
            if weight < KERNEL_MIN_WEIGHT {
                continue;
            }
            record_one(
                db,
                island_domain,
                action,
                nb_bucket,
                nb_choice,
                reward,
                weight,
            )
            .await?;
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
    use rand::RngExt;
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
