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

/// Increment pulls + total_reward, set last_reward. Caller is
/// responsible for the [0,1] clamp.
pub async fn record_pull(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
    reward: f64,
) -> Result<(), DbErr> {
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
