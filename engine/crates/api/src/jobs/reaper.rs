//! Lease reaper: requeue paid jobs whose worker died mid-grind.
//!
//! Workers heartbeat every 30s, extending `lease_expires_at` to
//! NOW()+5min. A worker that crashes / loses network never sends
//! another heartbeat and the lease falls into the past. The reaper
//! task ticks every 60s and flips any such row back to `queued` so
//! a fresh worker can pick it up via `claim_next_paid`.

use sea_orm::{ConnectionTrait, DatabaseBackend, DatabaseConnection, DbErr, Statement};

/// Requeue every `claimed`/`running` row whose lease has expired.
/// Returns rows_affected so the caller can log a one-line summary.
pub async fn reap_dead_leases(db: &DatabaseConnection) -> Result<u64, DbErr> {
    let stmt = Statement::from_string(
        DatabaseBackend::Postgres,
        r#"UPDATE conjecture_jobs
           SET state='queued',
               claimed_by=NULL,
               claimed_at=NULL,
               lease_expires_at=NULL
           WHERE state IN ('claimed','running','Running')
             AND lease_expires_at IS NOT NULL
             AND lease_expires_at < NOW()"#
            .to_string(),
    );
    let r = db.execute_raw(stmt).await?;
    Ok(r.rows_affected())
}

/// Mark workers as inactive if they haven't been seen recently.
///
/// 180-second threshold = 6× the worker's 30 s heartbeat tick. A single
/// dropped heartbeat (transient network blip, brief socket hang during
/// a Lake build, API restart) cannot flip a healthy worker to Inactive.
/// Worker-side retry-with-backoff fires another beat 10 s after a
/// failure, so even back-to-back failures stay well inside this window.
/// Returns rows_affected.
pub async fn mark_stale_workers(db: &DatabaseConnection) -> Result<u64, DbErr> {
    let result =
        nasrudin_pg::query::workers::mark_stale(db, chrono::Duration::seconds(180)).await?;
    Ok(result.rows_affected)
}
