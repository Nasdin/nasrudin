//! Refund records keyed on `refund_records.id` (also used as the Stripe
//! Idempotency-Key when creating the refund). The reconciler queries
//! `status='pending' AND requested_at < now() - 90 s` to recover from
//! mid-call crashes.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared(
            r#"
            CREATE TABLE IF NOT EXISTS refund_records (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                user_id UUID NOT NULL REFERENCES users(id),
                admin_user_id UUID NOT NULL REFERENCES users(id),
                stripe_refund_id TEXT UNIQUE,
                stripe_charge_id TEXT NOT NULL,
                amount_cents INTEGER NOT NULL,
                currency TEXT NOT NULL,
                reason TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'pending',
                stripe_failure_reason TEXT,
                requested_at TIMESTAMPTZ NOT NULL DEFAULT now(),
                completed_at TIMESTAMPTZ
            );
            CREATE INDEX IF NOT EXISTS refund_records_status
                ON refund_records (status, requested_at);
            CREATE INDEX IF NOT EXISTS refund_records_user
                ON refund_records (user_id, requested_at DESC);
            CREATE INDEX IF NOT EXISTS refund_records_charge
                ON refund_records (stripe_charge_id);
            "#,
        )
        .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared("DROP TABLE IF EXISTS refund_records")
            .await?;
        Ok(())
    }
}
