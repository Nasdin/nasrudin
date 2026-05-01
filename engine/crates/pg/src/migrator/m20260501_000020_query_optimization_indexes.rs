//! Query-optimization indexes for hot read paths.
//!
//! Adds indexes that audit-of-the-query-layer flagged as missing or
//! sub-optimal — every CREATE INDEX statement here corresponds to a
//! specific query that previously triggered a full table scan or
//! filter-then-sort on heap.
//!
//! Why partial indexes: most of these queries filter by a single small
//! cardinality value (`status='Verified'`, `state='Running'`,
//! `is_admin=true`). A partial index keeps the index size proportional
//! to the matching slice rather than the whole table, which is cheaper
//! to maintain and cache-warmer per byte.
//!
//! All indexes are created with `IF NOT EXISTS` so this migration is
//! idempotent across re-runs. None use `CONCURRENTLY` because SeaORM
//! runs each migration inside a transaction; for tables that grow into
//! the millions of rows the dba should re-run the equivalent
//! `CREATE INDEX CONCURRENTLY` out-of-band before this migration is
//! applied — the IF NOT EXISTS guard means the migration is then a
//! no-op.

use sea_orm_migration::prelude::*;
use sea_orm_migration::sea_orm::ConnectionTrait;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();

        // ─── admin_audit_log.list_recent() ───────────────────────────
        // Plain `ORDER BY created_at DESC LIMIT N` — backs the admin
        // audit dashboard's unfiltered recent-events view. Without this
        // index Postgres scans the whole table to find the newest rows.
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_admin_audit_log_created_at_desc
                ON admin_audit_log (created_at DESC)
            "#,
        )
        .await?;

        // ─── admin_audit_log.list_filtered() — action-only filter ────
        // Filtered timeline by action (e.g. all impersonations across
        // the org, ordered newest-first). The (action, created_at DESC)
        // composite supports both the equality filter and the order in
        // a single index scan.
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_admin_audit_log_action_created_at
                ON admin_audit_log (action, created_at DESC)
            "#,
        )
        .await?;

        // ─── cluster_steering.last_validated() ───────────────────────
        // Find the most-recent successful steering decision: filter
        // `validation_failed=false`, order `started_at DESC LIMIT 1`.
        // Partial index on the `false` slice keeps the index tiny — the
        // happy path is the vast majority of rows.
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_cluster_steering_validated
                ON cluster_steering (started_at DESC)
                WHERE validation_failed = false
            "#,
        )
        .await?;

        // ─── conjecture_jobs.requeue_expired_leases() ────────────────
        // Worker lease reaper: `WHERE state='Running' AND
        // lease_expires_at < NOW()`. Running rows are the small slice
        // (most jobs are Done/Queued); partial index on the slice keeps
        // the reaper sub-millisecond regardless of total job count.
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_conjecture_jobs_running_leases
                ON conjecture_jobs (lease_expires_at ASC)
                WHERE state = 'Running'
            "#,
        )
        .await?;

        // ─── conjecture_jobs.atomic_claim_paid() ─────────────────────
        // Worker dequeue path for paid jobs: `WHERE state='queued'
        // ORDER BY slice_priority DESC, created_at ASC LIMIT 1
        // FOR UPDATE SKIP LOCKED`. Partial index on queued rows with
        // both ordering columns turns the dequeue into an O(1) index
        // pop — critical for worker scaling.
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_conjecture_jobs_paid_claim
                ON conjecture_jobs (slice_priority DESC, created_at ASC)
                WHERE state = 'queued'
            "#,
        )
        .await?;

        // ─── conjecture_jobs.count_in_states() ───────────────────────
        // Plain `COUNT(*) WHERE state IN (...)`. Index-only scan eligible
        // — no need to touch heap rows for the count.
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_conjecture_jobs_state
                ON conjecture_jobs (state)
            "#,
        )
        .await?;

        // ─── admin_users.list_paginated() ────────────────────────────
        // `WHERE is_admin=true ORDER BY created_at DESC LIMIT/OFFSET`.
        // Admins are <0.1% of rows; partial index keeps this an O(log n)
        // scan over a tiny slice, avoiding the full users-table sort.
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_users_admin_created_at
                ON users (created_at DESC)
                WHERE is_admin = true
            "#,
        )
        .await?;

        // ─── theorems search.find_by_ac_hash() — partial on Verified ─
        // `canonical_ac_hash = $1 AND status='Verified'` is the public
        // "did anyone already prove this?" lookup. Partial index on the
        // Verified slice means the filter happens at index level (no
        // heap fetch on Pending/Rejected duplicates).
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_theorems_canonical_ac_hash_verified
                ON theorems (canonical_ac_hash)
                WHERE status = 'Verified'
            "#,
        )
        .await?;

        // ─── theorems search.candidates() — domain + depth + verified ─
        // Composite for the GA candidate-fetch path:
        // `WHERE domain=$1 AND depth <= $2 AND status='Verified'
        //  ORDER BY depth ASC, verified_at DESC`.
        // The full sort can be served from the index (no heap-sort) when
        // result sets exceed ~10K rows.
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_theorems_search_candidates
                ON theorems (domain, depth ASC, verified_at DESC)
                WHERE status = 'Verified'
            "#,
        )
        .await?;

        // ─── pipeline-funnel queries (landing/workers analytics) ─────
        // Three counter queries back the discard-funnel ticker:
        //   • submitted (24h) — `WHERE created_at >= NOW() - 24h`
        //   • rejected (24h)  — `WHERE status='Rejected' AND created_at >= NOW() - 24h`
        //   • pending (now)   — `WHERE status='Pending'`
        // Submitted hits a global `created_at` index (most theorems are
        // recent so the lookup is cheap and the index doubles as a
        // chronological scan for archival). Rejected + Pending are the
        // small slices, so partial indexes keep them tiny and the queries
        // index-only.
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_theorems_created_at
                ON theorems (created_at DESC)
            "#,
        )
        .await?;
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_theorems_rejected_created_at
                ON theorems (created_at DESC)
                WHERE status = 'Rejected'
            "#,
        )
        .await?;
        conn.execute_unprepared(
            r#"
            CREATE INDEX IF NOT EXISTS idx_theorems_pending_created_at
                ON theorems (created_at DESC)
                WHERE status = 'Pending'
            "#,
        )
        .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();
        for ix in [
            "idx_admin_audit_log_created_at_desc",
            "idx_admin_audit_log_action_created_at",
            "idx_cluster_steering_validated",
            "idx_conjecture_jobs_running_leases",
            "idx_conjecture_jobs_paid_claim",
            "idx_conjecture_jobs_state",
            "idx_users_admin_created_at",
            "idx_theorems_canonical_ac_hash_verified",
            "idx_theorems_search_candidates",
            "idx_theorems_created_at",
            "idx_theorems_rejected_created_at",
            "idx_theorems_pending_created_at",
        ] {
            conn.execute_unprepared(&format!("DROP INDEX IF EXISTS {ix}"))
                .await?;
        }
        Ok(())
    }
}
