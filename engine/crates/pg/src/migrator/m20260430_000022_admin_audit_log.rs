//! Tamper-evident audit log of admin mutations. Every entry written
//! transactionally with the mutation it describes (see
//! `crates/api/src/admin/audit.rs::perform_audited`). Reasons are
//! required (>= 10 chars, validated server-side).
//!
//! Indexed by target_user_id, actor_user_id, and action for the three
//! query shapes the admin UI exercises.

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
            CREATE TABLE IF NOT EXISTS admin_audit_log (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                actor_user_id UUID NOT NULL REFERENCES users(id),
                target_user_id UUID REFERENCES users(id),
                action TEXT NOT NULL,
                before_value JSONB,
                after_value JSONB,
                reason TEXT NOT NULL,
                impersonating_user_id UUID REFERENCES users(id),
                request_ip TEXT,
                user_agent TEXT,
                created_at TIMESTAMPTZ NOT NULL DEFAULT now()
            );
            CREATE INDEX IF NOT EXISTS admin_audit_log_target
                ON admin_audit_log (target_user_id, created_at DESC);
            CREATE INDEX IF NOT EXISTS admin_audit_log_actor
                ON admin_audit_log (actor_user_id, created_at DESC);
            CREATE INDEX IF NOT EXISTS admin_audit_log_action
                ON admin_audit_log (action, created_at DESC);
            "#,
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared("DROP TABLE IF EXISTS admin_audit_log")
            .await?;
        Ok(())
    }
}
