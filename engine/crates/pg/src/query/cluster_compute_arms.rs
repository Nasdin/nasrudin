//! Read/update helpers for the compute-scaling bandit's arm table.
//! Mirrors `cluster_directive_arms` but without the `action`
//! dimension (compute is a single global knob, not per-action).

use crate::entity::cluster_compute_arms::*;
use chrono::Utc;
use sea_orm::*;

pub async fn ensure_arm(
    db: &DatabaseConnection,
    island_domain: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
) -> Result<(), DbErr> {
    let exists = Entity::find_by_id((
        island_domain.to_string(),
        strength_bucket,
        multiplier_choice,
    ))
    .one(db)
    .await?;
    if exists.is_none() {
        let am = ActiveModel {
            island_domain: Set(island_domain.into()),
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

pub async fn list_for_slot(
    db: &DatabaseConnection,
    island_domain: &str,
    strength_bucket: i16,
) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .filter(Column::IslandDomain.eq(island_domain))
        .filter(Column::StrengthBucket.eq(strength_bucket))
        .order_by_asc(Column::MultiplierChoice)
        .all(db)
        .await
}

pub async fn snapshot_all(db: &DatabaseConnection) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .order_by_asc(Column::IslandDomain)
        .order_by_asc(Column::StrengthBucket)
        .order_by_asc(Column::MultiplierChoice)
        .all(db)
        .await
}

pub async fn record_pull(
    db: &DatabaseConnection,
    island_domain: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
    reward: f64,
) -> Result<(), DbErr> {
    let arm = Entity::find_by_id((
        island_domain.to_string(),
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
