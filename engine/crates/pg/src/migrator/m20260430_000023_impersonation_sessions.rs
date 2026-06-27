//! Tracks active impersonation sessions. The `expires_at` column is the
//! authoritative deadline; the HMAC token's expiry must match. The
//! 60-second expiry tick (in `crates/api/src/admin/impersonation_expiry.rs`)
//! sets `ended_at` for rows whose `expires_at` has passed without
//! a manual end.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared(
                r#"
            CREATE TABLE IF NOT EXISTS impersonation_sessions (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                admin_user_id UUID NOT NULL REFERENCES users(id),
                target_user_id UUID NOT NULL REFERENCES users(id),
                started_at TIMESTAMPTZ NOT NULL DEFAULT now(),
                expires_at TIMESTAMPTZ NOT NULL,
                ended_at TIMESTAMPTZ,
                end_reason TEXT,
                reason TEXT NOT NULL
            );
            CREATE INDEX IF NOT EXISTS impersonation_active
                ON impersonation_sessions (admin_user_id) WHERE ended_at IS NULL;
            CREATE INDEX IF NOT EXISTS impersonation_target
                ON impersonation_sessions (target_user_id, started_at DESC);
            "#,
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared("DROP TABLE IF EXISTS impersonation_sessions")
            .await?;
        Ok(())
    }
}
