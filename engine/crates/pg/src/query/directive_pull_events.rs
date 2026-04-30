//! Read/insert helpers for the directive bandit's event log.
//!
//! `insert_event` is called inside the `/api/directive-feedback`
//! handler alongside `cluster_directive_arms::record_pull` so the
//! raw event stream is preserved for offline policy training (the
//! aggregate-only path loses per-pull information needed by
//! contextual bandits, replay-based learners, or value networks).

use crate::entity::directive_pull_events::*;
use sea_orm::*;

pub async fn insert_event(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
    reward: f64,
) -> Result<i64, DbErr> {
    let am = ActiveModel {
        island_domain: Set(island_domain.into()),
        action: Set(action.into()),
        strength_bucket: Set(strength_bucket),
        multiplier_choice: Set(multiplier_choice),
        reward: Set(reward),
        ..Default::default()
    };
    let res = Entity::insert(am).exec(db).await?;
    Ok(res.last_insert_id)
}

/// Read the most recent N events for one island, newest first.
/// Used by offline training jobs to fetch a replay batch.
pub async fn recent_for_island(
    db: &DatabaseConnection,
    island_domain: &str,
    n: u64,
) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .filter(Column::IslandDomain.eq(island_domain))
        .order_by_desc(Column::ReceivedAt)
        .limit(n)
        .all(db)
        .await
}

/// Delete events older than `cutoff`. Returns rows deleted. Run
/// daily to enforce ~30-day retention.
pub async fn purge_older_than(
    db: &DatabaseConnection,
    cutoff: chrono::DateTime<chrono::Utc>,
) -> Result<u64, DbErr> {
    let res = Entity::delete_many()
        .filter(Column::ReceivedAt.lt(cutoff.fixed_offset()))
        .exec(db)
        .await?;
    Ok(res.rows_affected)
}
