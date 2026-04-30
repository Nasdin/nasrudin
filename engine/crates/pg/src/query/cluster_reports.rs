//! Read/write helpers for `cluster_reports`.
//!
//! Workers write per-cluster summaries via `insert_summary`; the API
//! steerer reads recent rows via `recent_for_island` for both prompt
//! population and UCB1 reward computation. `purge_older_than` runs
//! hourly to enforce 7-day retention.

use crate::entity::cluster_reports::*;
use sea_orm::*;
use uuid::Uuid;

pub async fn insert_summary(
    db: &DatabaseConnection,
    worker_id: Uuid,
    chunk_index: i64,
    k_used: i16,
    island_domain: &str,
    cluster_id: i16,
    summary: serde_json::Value,
) -> Result<i64, DbErr> {
    let am = ActiveModel {
        worker_id: Set(worker_id),
        chunk_index: Set(chunk_index),
        k_used: Set(k_used),
        island_domain: Set(island_domain.into()),
        cluster_id: Set(cluster_id),
        summary: Set(summary),
        ..Default::default()
    };
    let res = Entity::insert(am).exec(db).await?;
    Ok(res.last_insert_id)
}

/// Most recent `n` rows for an island. Newest-first by `received_at`.
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

/// Most recent rows for an island within a time window, restricted to
/// rows that used the given K. Used by bandit reward computation to
/// attribute outcomes to the K that produced them.
pub async fn recent_for_island_with_k(
    db: &DatabaseConnection,
    island_domain: &str,
    k_used: i16,
    since: chrono::DateTime<chrono::Utc>,
) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .filter(Column::IslandDomain.eq(island_domain))
        .filter(Column::KUsed.eq(k_used))
        .filter(Column::ReceivedAt.gte(since.fixed_offset()))
        .all(db)
        .await
}

/// Delete rows older than `cutoff`. Returns rows deleted.
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
