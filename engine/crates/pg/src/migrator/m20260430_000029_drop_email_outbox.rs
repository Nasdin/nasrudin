//! Drop the `email_outbox` table.
//!
//! Decision (2026-04-30): Stripe handles every transactional email we
//! actually need (subscription change, refund issued, payment failure,
//! invoice receipts) out of the box. The remaining cases (research
//! credit grant, admin one-offs) don't justify a dedicated email
//! provider; the operator handles those via personal email.
//!
//! This migration cleans up after `m20260430_000024_email_outbox` —
//! the table was created but never had a writer. We leave migration 24
//! in place so existing dev DBs keep `seaql_migrations` consistent;
//! this migration only drops the empty table.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared("DROP TABLE IF EXISTS email_outbox")
            .await?;
        Ok(())
    }

    async fn down(&self, _manager: &SchemaManager) -> Result<(), DbErr> {
        // No-op down: re-running migration 000024 would recreate the
        // table if you really wanted to roll back this far.
        Ok(())
    }
}
