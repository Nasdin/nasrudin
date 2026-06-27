//! Outbox queue for transactional + admin-composed email. Status values:
//! `queued`, `sent`, `failed_terminal`, `failed_retrying`,
//! `cancelled_dependent`. The drain worker (`crates/api/src/email/worker.rs`)
//! claims rows whose backoff window has elapsed and `attempts < 5`.

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
            CREATE TABLE IF NOT EXISTS email_outbox (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                to_user_id UUID REFERENCES users(id),
                to_address TEXT NOT NULL,
                template TEXT NOT NULL,
                subject TEXT NOT NULL,
                body_text TEXT NOT NULL,
                body_html TEXT,
                status TEXT NOT NULL DEFAULT 'queued',
                attempts INTEGER NOT NULL DEFAULT 0,
                last_attempt_at TIMESTAMPTZ,
                last_error TEXT,
                provider_message_id TEXT,
                queued_by_admin_id UUID REFERENCES users(id),
                queued_by_action TEXT,
                created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
                sent_at TIMESTAMPTZ
            );
            CREATE INDEX IF NOT EXISTS email_outbox_pending
                ON email_outbox (status, created_at)
                WHERE status IN ('queued', 'failed_retrying');
            CREATE INDEX IF NOT EXISTS email_outbox_user
                ON email_outbox (to_user_id, created_at DESC);
            "#,
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared("DROP TABLE IF EXISTS email_outbox")
            .await?;
        Ok(())
    }
}
