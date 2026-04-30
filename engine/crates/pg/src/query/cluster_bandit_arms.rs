//! Read/update UCB1 arm state per (island_domain, K).
//!
//! `ensure_arm` is called at API boot to materialise all (domain, K)
//! pairs at zero stats. `record_pull` is called by the steerer cycle
//! after computing the reward for the previously-chosen K. UCB1
//! selection itself is in `physics_api::steerer::bandit`.

use crate::entity::cluster_bandit_arms::*;
use chrono::Utc;
use sea_orm::*;

pub async fn list_for_island(
    db: &DatabaseConnection,
    island_domain: &str,
) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .filter(Column::IslandDomain.eq(island_domain))
        .all(db)
        .await
}

/// Idempotent: insert with zero stats if missing, no-op if present.
pub async fn ensure_arm(
    db: &DatabaseConnection,
    island_domain: &str,
    k_value: i16,
) -> Result<(), DbErr> {
    let exists = Entity::find_by_id((island_domain.to_string(), k_value))
        .one(db)
        .await?;
    if exists.is_none() {
        let am = ActiveModel {
            island_domain: Set(island_domain.into()),
            k_value: Set(k_value),
            pulls: Set(0),
            total_reward: Set(0.0),
            last_reward: Set(0.0),
            updated_at: Set(Utc::now().fixed_offset()),
        };
        Entity::insert(am).exec(db).await?;
    }
    Ok(())
}

/// Increment `pulls` and `total_reward`, set `last_reward`. Caller is
/// responsible for clamping the reward to [0.0, 1.0]; this function
/// stores whatever it's given so the bandit can be inspected.
pub async fn record_pull(
    db: &DatabaseConnection,
    island_domain: &str,
    k_value: i16,
    reward: f64,
) -> Result<(), DbErr> {
    let arm = Entity::find_by_id((island_domain.to_string(), k_value))
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
            k_value: Set(k_value),
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
