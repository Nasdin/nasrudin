use anyhow::Result;
use chrono::Utc;
use sea_orm::prelude::Expr;
use sea_orm::*;

use crate::entity::workers::{self, WorkerStatus};

/// Register a new worker. Returns the inserted model.
pub async fn register(
    db: &DatabaseConnection,
    id: &str,
    name: Option<&str>,
    host: Option<&str>,
) -> Result<workers::Model, DbErr> {
    let model = workers::ActiveModel {
        id: Set(id.to_owned()),
        name: Set(name.map(|s| s.to_owned())),
        host: Set(host.map(|s| s.to_owned())),
        last_seen: Set(chrono::Utc::now().into()),
        theorems_contributed: Set(0),
        status: Set(WorkerStatus::Active),
        last_heartbeat_at: NotSet,
        last_contribution_at: NotSet,
        current_generation: NotSet,
        theorems_produced_total: NotSet,
        uptime_seconds: NotSet,
        engine_git_sha: NotSet,
    };
    model.insert(db).await
}

/// Record a heartbeat from a worker. Updates last_seen, generation stats, and status.
pub async fn heartbeat(
    db: &DatabaseConnection,
    id: &str,
    theorems_contributed: i64,
) -> Result<Option<workers::Model>, DbErr> {
    let existing = workers::Entity::find_by_id(id.to_owned()).one(db).await?;
    match existing {
        Some(record) => {
            let mut active: workers::ActiveModel = record.into();
            active.last_seen = Set(chrono::Utc::now().into());
            active.theorems_contributed = Set(theorems_contributed);
            active.status = Set(WorkerStatus::Active);
            Ok(Some(active.update(db).await?))
        }
        None => Ok(None),
    }
}

/// Mark a worker as disconnected.
pub async fn disconnect(
    db: &DatabaseConnection,
    id: &str,
) -> Result<Option<workers::Model>, DbErr> {
    let existing = workers::Entity::find_by_id(id.to_owned()).one(db).await?;
    match existing {
        Some(record) => {
            let mut active: workers::ActiveModel = record.into();
            active.status = Set(WorkerStatus::Disconnected);
            active.last_seen = Set(chrono::Utc::now().into());
            Ok(Some(active.update(db).await?))
        }
        None => Ok(None),
    }
}

/// List all workers, optionally filtered by status.
pub async fn list(
    db: &DatabaseConnection,
    status_filter: Option<WorkerStatus>,
) -> Result<Vec<workers::Model>, DbErr> {
    let mut query = workers::Entity::find();
    if let Some(status) = status_filter {
        query = query.filter(workers::Column::Status.eq(status));
    }
    query.order_by_desc(workers::Column::LastSeen).all(db).await
}

/// Find a worker by ID.
pub async fn find_by_id(
    db: &DatabaseConnection,
    id: &str,
) -> Result<Option<workers::Model>, DbErr> {
    workers::Entity::find_by_id(id.to_owned()).one(db).await
}

/// Mark stale workers (no heartbeat for `threshold`) as inactive.
pub async fn mark_stale(
    db: &DatabaseConnection,
    threshold: chrono::Duration,
) -> Result<UpdateResult, DbErr> {
    let cutoff = chrono::Utc::now() - threshold;
    workers::Entity::update_many()
        .col_expr(workers::Column::Status, Expr::val("inactive"))
        .filter(workers::Column::Status.eq(WorkerStatus::Active))
        .filter(workers::Column::LastSeen.lt(cutoff))
        .exec(db)
        .await
}

/// Delete a worker registration.
pub async fn delete(db: &DatabaseConnection, id: &str) -> Result<DeleteResult, DbErr> {
    workers::Entity::delete_by_id(id.to_owned()).exec(db).await
}

/// Get summary statistics for the worker pool.
pub async fn stats(db: &DatabaseConnection) -> Result<WorkerPoolStats, DbErr> {
    let all = workers::Entity::find().all(db).await?;
    let active = all
        .iter()
        .filter(|w| w.status == WorkerStatus::Active)
        .count();
    let total_contributed: i64 = all.iter().map(|w| w.theorems_contributed).sum();
    Ok(WorkerPoolStats {
        total_workers: all.len(),
        active_workers: active,
        total_theorems_contributed: total_contributed,
    })
}

/// Summary statistics for the worker pool.
#[derive(Debug, Clone, serde::Serialize)]
pub struct WorkerPoolStats {
    pub total_workers: usize,
    pub active_workers: usize,
    pub total_theorems_contributed: i64,
}

// ---------------------------------------------------------------------------
// Phase 9 / Task 1.5: heartbeat + contribution increment + leaderboard
//
// These functions accept `&impl ConnectionTrait` so they can be invoked either
// directly on a `DatabaseConnection` or inside a `DatabaseTransaction` for
// atomic multi-step workflows in the API layer.
// ---------------------------------------------------------------------------

/// Look up a single worker by ID. Generic over `ConnectionTrait` so callers in
/// transactions can use it too.
pub async fn get(
    db: &impl ConnectionTrait,
    id: &str,
) -> Result<Option<workers::Model>> {
    Ok(workers::Entity::find_by_id(id.to_string()).one(db).await?)
}

/// Record a full heartbeat from a worker, updating timestamps, generation
/// stats, uptime, and engine git SHA. Sets `status = Active`.
///
/// Errors out when the worker isn't registered — callers (the API heartbeat
/// handler) should treat that as a 404 / re-register prompt.
pub async fn update_heartbeat(
    db: &impl ConnectionTrait,
    id: &str,
    current_generation: i64,
    theorems_produced_total: i64,
    uptime_seconds: i64,
    engine_git_sha: &str,
) -> Result<()> {
    let model = workers::Entity::find_by_id(id.to_string())
        .one(db)
        .await?
        .ok_or_else(|| anyhow::anyhow!("worker not found: {id}"))?;
    let mut am: workers::ActiveModel = model.into();
    let now: chrono::DateTime<chrono::FixedOffset> = Utc::now().into();
    am.last_heartbeat_at = Set(Some(now));
    am.last_seen = Set(now);
    am.current_generation = Set(current_generation);
    am.theorems_produced_total = Set(theorems_produced_total);
    am.uptime_seconds = Set(uptime_seconds);
    am.engine_git_sha = Set(Some(engine_git_sha.into()));
    am.status = Set(WorkerStatus::Active);
    am.update(db).await?;
    Ok(())
}

/// Atomically increment `theorems_contributed` by 1 and stamp
/// `last_contribution_at = NOW()`. Implemented as a single UPDATE so concurrent
/// increments from the verification worker pool can't lose updates.
pub async fn increment_contribution(
    db: &impl ConnectionTrait,
    id: &str,
) -> Result<()> {
    let now: chrono::DateTime<chrono::FixedOffset> = Utc::now().into();
    db.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE workers \
         SET theorems_contributed = theorems_contributed + 1, \
             last_contribution_at = $1 \
         WHERE id = $2",
        [now.into(), id.into()],
    ))
    .await?;
    Ok(())
}

/// List all registered workers ordered by `theorems_contributed DESC` — the
/// shape the leaderboard endpoint serves.
pub async fn list_all(db: &impl ConnectionTrait) -> Result<Vec<workers::Model>> {
    Ok(workers::Entity::find()
        .order_by_desc(workers::Column::TheoremsContributed)
        .all(db)
        .await?)
}
