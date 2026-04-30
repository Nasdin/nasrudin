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
