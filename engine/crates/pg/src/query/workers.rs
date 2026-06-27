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
        reputation_score: NotSet, // defaults to 1.0 via the SQL DEFAULT
        spot_check_pass_count: NotSet,
        spot_check_fail_count: NotSet,
        auto_revoked_at: NotSet,
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
pub async fn get(db: &impl ConnectionTrait, id: &str) -> Result<Option<workers::Model>> {
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
    // Upsert semantics: if the workers row was lost (e.g. after a
    // PG dump/restore that pre-dated the worker's first heartbeat,
    // or a fresh-install where the operator already has a valid
    // api_key entry but never seeded the workers table), the
    // heartbeat itself reconstructs the row. The auth layer
    // (WorkerAuth → matches against api_keys) has already proven
    // the caller is the legitimate owner of `id` by this point —
    // creating the workers row in their name is safe and turns
    // the system self-healing across DB rebuilds.
    let now: chrono::DateTime<chrono::FixedOffset> = Utc::now().into();
    match workers::Entity::find_by_id(id.to_string()).one(db).await? {
        Some(model) => {
            let mut am: workers::ActiveModel = model.into();
            am.last_heartbeat_at = Set(Some(now));
            am.last_seen = Set(now);
            am.current_generation = Set(current_generation);
            am.theorems_produced_total = Set(theorems_produced_total);
            am.uptime_seconds = Set(uptime_seconds);
            am.engine_git_sha = Set(Some(engine_git_sha.into()));
            am.status = Set(WorkerStatus::Active);
            am.update(db).await?;
        }
        None => {
            tracing::info!(
                worker_id = id,
                "heartbeat from unknown worker — auto-registering (api_keys auth already verified ownership)"
            );
            let am = workers::ActiveModel {
                id: Set(id.to_string()),
                name: Set(Some(id.to_string())),
                host: Set(None),
                last_heartbeat_at: Set(Some(now)),
                last_seen: Set(now),
                current_generation: Set(current_generation),
                theorems_produced_total: Set(theorems_produced_total),
                uptime_seconds: Set(uptime_seconds),
                engine_git_sha: Set(Some(engine_git_sha.into())),
                status: Set(WorkerStatus::Active),
                ..Default::default()
            };
            am.insert(db).await?;
        }
    }
    Ok(())
}

/// Atomically increment `theorems_contributed` by 1 and stamp
/// `last_contribution_at = NOW()`. Implemented as a single UPDATE so concurrent
/// increments from the verification worker pool can't lose updates.
pub async fn increment_contribution(db: &impl ConnectionTrait, id: &str) -> Result<()> {
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

/// P-Task 5: record a single lake-promotion outcome for the worker
/// that submitted the underlying chain. Updates the EMA reputation
/// score (0.99 × prev + 0.01 × (1 if pass else 0)) and bumps the
/// pass/fail counters atomically. Single UPDATE so concurrent
/// promotion drains can't race.
///
/// Called by the lake_promotion drain after every Verified or
/// Rejected outcome, looking up the contributor_id from the theorem
/// row.
pub async fn record_spot_check(db: &impl ConnectionTrait, id: &str, passed: bool) -> Result<()> {
    let pass_inc = if passed { 1 } else { 0 };
    let fail_inc = if passed { 0 } else { 1 };
    let target = if passed { 1.0_f64 } else { 0.0_f64 };
    db.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE workers \
         SET reputation_score = (0.99::real * reputation_score) + (0.01::real * $2::real), \
             spot_check_pass_count = spot_check_pass_count + $3, \
             spot_check_fail_count = spot_check_fail_count + $4 \
         WHERE id = $1",
        [
            id.into(),
            target.into(),
            (pass_inc as i32).into(),
            (fail_inc as i32).into(),
        ],
    ))
    .await?;
    Ok(())
}

/// Mark a worker auto-revoked due to repeated lake-build failures.
/// Stamps `auto_revoked_at = NOW()`. The `WorkerAuth` extractor checks
/// `auto_revoked_at IS NULL` (alongside `revoked_at` on the api_keys
/// row) before accepting a bearer.
pub async fn auto_revoke(db: &impl ConnectionTrait, id: &str, reason: &str) -> Result<()> {
    let now: chrono::DateTime<chrono::FixedOffset> = Utc::now().into();
    db.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE workers SET auto_revoked_at = $1, status = 'disconnected' \
         WHERE id = $2 AND auto_revoked_at IS NULL",
        [now.into(), id.into()],
    ))
    .await?;
    tracing::warn!(worker_id = %id, reason = %reason, "worker auto-revoked");
    Ok(())
}

/// Look up a worker's current reputation score. Used by the ingest
/// gate (P-Task 5) — wrap in an in-process LRU cache with 5-min TTL
/// at the call site so a hot worker doesn't pay one PG round-trip per
/// theorem submission.
pub async fn get_reputation(db: &impl ConnectionTrait, id: &str) -> Result<Option<f32>> {
    use sea_orm::FromQueryResult;
    #[derive(FromQueryResult)]
    struct R {
        reputation_score: f32,
    }
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "SELECT reputation_score FROM workers WHERE id = $1",
        [id.into()],
    );
    Ok(R::find_by_statement(stmt)
        .one(db)
        .await?
        .map(|r| r.reputation_score))
}

/// List all registered workers ordered by `theorems_contributed DESC` — the
/// shape the leaderboard endpoint serves.
pub async fn list_all(db: &impl ConnectionTrait) -> Result<Vec<workers::Model>> {
    Ok(workers::Entity::find()
        .order_by_desc(workers::Column::TheoremsContributed)
        .all(db)
        .await?)
}

/// Paginated list of workers ordered by `theorems_contributed DESC`.
/// Returns a page of workers and a cursor for the next page.
pub async fn list_paginated(
    db: &impl ConnectionTrait,
    limit: u64,
    cursor: Option<String>,
) -> Result<(Vec<workers::Model>, Option<String>)> {
    let limit = std::cmp::min(limit, 100); // Cap at 100 per page
    let mut query = workers::Entity::find().order_by_desc(workers::Column::TheoremsContributed);

    // If cursor is provided, decode it and use it to skip to that position
    if let Some(cursor) = cursor {
        if let Ok(theorems_contributed) = cursor.parse::<i64>() {
            query = query.filter(workers::Column::TheoremsContributed.lt(theorems_contributed));
        }
    }

    let workers_list = query.limit(limit as u64).all(db).await?;

    // Generate next cursor from the last worker's theorems_contributed value
    let next_cursor = if workers_list.len() >= limit as usize {
        workers_list
            .last()
            .map(|w| w.theorems_contributed.to_string())
    } else {
        None
    };

    Ok((workers_list, next_cursor))
}

/// Count workers whose `last_seen` is more recent than `now() - threshold`.
/// Used by the public landing-stats endpoint.
pub async fn count_active_workers(
    db: &impl ConnectionTrait,
    threshold: chrono::Duration,
) -> Result<u64> {
    let cutoff = chrono::Utc::now() - threshold;
    let cutoff_offset: chrono::DateTime<chrono::FixedOffset> = cutoff.into();
    let count = workers::Entity::find()
        .filter(workers::Column::LastSeen.gt(cutoff_offset))
        .count(db)
        .await?;
    Ok(count)
}

/// Count distinct user_ids on api_keys rows of kind = 'worker' — i.e. the
/// number of people who have ever registered a worker. Used by the public
/// landing-stats endpoint.
pub async fn count_distinct_contributors(db: &impl ConnectionTrait) -> Result<u64> {
    use sea_orm::FromQueryResult;
    #[derive(FromQueryResult)]
    struct R {
        n: i64,
    }
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "SELECT COUNT(DISTINCT user_id)::bigint AS n \
         FROM api_keys WHERE kind = 'worker' AND user_id IS NOT NULL",
        [],
    );
    let row = R::find_by_statement(stmt).one(db).await?;
    Ok(row.map(|r| r.n).unwrap_or(0).try_into().unwrap_or(0))
}
