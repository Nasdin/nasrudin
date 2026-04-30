//! Tracks long-running bulk operations (e.g. "set is_trusted=true on
//! 50 users"). Runner appends per-user failures to the JSONB array. A
//! restart reaper marks rows older than 1 hour as `aborted`.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared(
            r#"
            CREATE TABLE IF NOT EXISTS bulk_runs (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                started_by_admin_id UUID NOT NULL REFERENCES users(id),
                action TEXT NOT NULL,
                params JSONB NOT NULL,
                total_count INTEGER NOT NULL,
                completed_count INTEGER NOT NULL DEFAULT 0,
                failed_count INTEGER NOT NULL DEFAULT 0,
                status TEXT NOT NULL DEFAULT 'running',
                started_at TIMESTAMPTZ NOT NULL DEFAULT now(),
                completed_at TIMESTAMPTZ,
                failures JSONB
            );
            CREATE INDEX IF NOT EXISTS bulk_runs_status
                ON bulk_runs (status, started_at DESC);
            CREATE INDEX IF NOT EXISTS bulk_runs_admin
                ON bulk_runs (started_by_admin_id, started_at DESC);
            "#,
        )
        .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared("DROP TABLE IF EXISTS bulk_runs")
            .await?;
        Ok(())
    }
}
