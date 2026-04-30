//! `user_sponsorships` — public-profile-facing record of every donation
//! and subscription that ever touched a user's account.
//!
//! Distinct from `users.plan_tier` (current entitlement) and
//! `billing_events` (raw audit log of webhook deliveries):
//!   - `users.plan_tier` answers "what can this user do today";
//!   - `billing_events` answers "what did Stripe say happened";
//!   - `user_sponsorships` answers "what should we put on the public
//!     profile to thank this person".
//!
//! Both subscription and one-time rows live in this table. We unique on
//! `stripe_subscription_id` and `stripe_charge_id` so a webhook replay
//! is naturally idempotent at the DB layer; a partial unique index on
//! `stripe_event_id` (when set) gives us a second belt-and-braces
//! guarantee that the same event never produces two rows.

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
                CREATE TABLE IF NOT EXISTS user_sponsorships (
                    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                    user_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
                    stripe_event_id TEXT,
                    kind TEXT NOT NULL,
                    tier TEXT,
                    amount_cents BIGINT,
                    currency TEXT NOT NULL DEFAULT 'usd',
                    stripe_subscription_id TEXT,
                    stripe_charge_id TEXT,
                    status TEXT NOT NULL,
                    started_at TIMESTAMPTZ NOT NULL,
                    canceled_at TIMESTAMPTZ,
                    created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
                    CONSTRAINT user_sponsorships_kind_chk
                        CHECK (kind IN ('subscription', 'one_time')),
                    CONSTRAINT user_sponsorships_status_chk
                        CHECK (status IN ('active', 'canceled', 'completed', 'refunded')),
                    -- A `kind='subscription'` row must carry the sub id;
                    -- a `kind='one_time'` row must carry the charge id.
                    -- Either-or guards prevent silently inserting NULL
                    -- on the wrong side.
                    CONSTRAINT user_sponsorships_sub_id_when_subscription
                        CHECK (kind <> 'subscription' OR stripe_subscription_id IS NOT NULL),
                    CONSTRAINT user_sponsorships_charge_id_when_one_time
                        CHECK (kind <> 'one_time' OR stripe_charge_id IS NOT NULL),
                    CONSTRAINT user_sponsorships_sub_unique UNIQUE (stripe_subscription_id),
                    CONSTRAINT user_sponsorships_charge_unique UNIQUE (stripe_charge_id)
                );
                CREATE INDEX IF NOT EXISTS user_sponsorships_user
                    ON user_sponsorships (user_id, started_at DESC);
                CREATE INDEX IF NOT EXISTS user_sponsorships_active_subs
                    ON user_sponsorships (user_id)
                    WHERE kind = 'subscription' AND status = 'active';
                -- Idempotency: a single `stripe_event_id` may only ever
                -- produce one row. Partial because backfill rows have
                -- no event id (they're synthesised from API queries).
                CREATE UNIQUE INDEX IF NOT EXISTS user_sponsorships_event_id_unique
                    ON user_sponsorships (stripe_event_id)
                    WHERE stripe_event_id IS NOT NULL;
                "#,
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared("DROP TABLE IF EXISTS user_sponsorships")
            .await?;
        Ok(())
    }
}
