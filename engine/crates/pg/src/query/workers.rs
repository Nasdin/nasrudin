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
    query
        .order_by_desc(workers::Column::LastSeen)
        .all(db)
        .await
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
