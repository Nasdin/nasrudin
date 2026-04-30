//! `user_sponsorships` — public-profile sponsorship + donation ledger.
//!
//! Driven by Stripe webhooks (`checkout.session.completed` for one-time
//! donations, `customer.subscription.{created,updated,deleted}` for
//! subscriptions) and an opt-in startup backfill. Read by the
//! public profile endpoint via `summary_for_user`.
//!
//! Idempotency:
//! - `upsert_subscription` keys on `stripe_subscription_id` (UNIQUE) so
//!   a `subscription.updated` replay updates the existing row instead
//!   of inserting a duplicate.
//! - `upsert_one_time` keys on `stripe_charge_id` (UNIQUE) and skips
//!   when `stripe_event_id` already exists in the table (partial
//!   unique index).

use chrono::{DateTime, Utc};
use sea_orm::ActiveValue::*;
use sea_orm::prelude::*;
use sea_orm::{ConnectionTrait, DatabaseBackend, FromQueryResult, QueryOrder, Statement};
use serde::Serialize;
use uuid::Uuid;

use crate::entity::user_sponsorships as ent;

/// Insert-or-update a subscription row. Keyed on
/// `stripe_subscription_id`; a replay overwrites mutable fields
/// (status, amount_cents, tier) and leaves `started_at` /
/// `created_at` untouched.
#[allow(clippy::too_many_arguments)]
pub async fn upsert_subscription<C: ConnectionTrait>(
    conn: &C,
    user_id: Uuid,
    stripe_sub_id: &str,
    tier: Option<&str>,
    amount_cents: Option<i64>,
    status: &str,
    started_at: DateTime<Utc>,
    stripe_event_id: Option<&str>,
) -> Result<(), DbErr> {
    let id = Uuid::new_v4();
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        INSERT INTO user_sponsorships
            (id, user_id, stripe_event_id, kind, tier, amount_cents, currency,
             stripe_subscription_id, stripe_charge_id, status,
             started_at, canceled_at, created_at)
        VALUES
            ($1, $2, $3, 'subscription', $4, $5, 'usd',
             $6, NULL, $7, $8, NULL, now())
        ON CONFLICT (stripe_subscription_id) DO UPDATE SET
            status = EXCLUDED.status,
            tier = EXCLUDED.tier,
            amount_cents = EXCLUDED.amount_cents,
            stripe_event_id = COALESCE(EXCLUDED.stripe_event_id, user_sponsorships.stripe_event_id),
            canceled_at = CASE
                WHEN EXCLUDED.status = 'canceled' AND user_sponsorships.canceled_at IS NULL
                    THEN now()
                ELSE user_sponsorships.canceled_at
            END
        "#,
        [
            id.into(),
            user_id.into(),
            stripe_event_id.map(|s| s.to_string()).into(),
            tier.map(|s| s.to_string()).into(),
            amount_cents.into(),
            stripe_sub_id.to_string().into(),
            status.to_string().into(),
            started_at.fixed_offset().into(),
        ],
    ))
    .await?;
    Ok(())
}

/// Insert a one-time donation row. Keyed on `stripe_charge_id`
/// (UNIQUE); a replay is a no-op.
#[allow(clippy::too_many_arguments)]
pub async fn upsert_one_time<C: ConnectionTrait>(
    conn: &C,
    user_id: Uuid,
    stripe_charge_id: &str,
    tier: Option<&str>,
    amount_cents: i64,
    started_at: DateTime<Utc>,
    stripe_event_id: Option<&str>,
) -> Result<(), DbErr> {
    let id = Uuid::new_v4();
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        INSERT INTO user_sponsorships
            (id, user_id, stripe_event_id, kind, tier, amount_cents, currency,
             stripe_subscription_id, stripe_charge_id, status,
             started_at, canceled_at, created_at)
        VALUES
            ($1, $2, $3, 'one_time', $4, $5, 'usd',
             NULL, $6, 'completed', $7, NULL, now())
        ON CONFLICT (stripe_charge_id) DO NOTHING
        "#,
        [
            id.into(),
            user_id.into(),
            stripe_event_id.map(|s| s.to_string()).into(),
            tier.map(|s| s.to_string()).into(),
            amount_cents.into(),
            stripe_charge_id.to_string().into(),
            started_at.fixed_offset().into(),
        ],
    ))
    .await?;
    Ok(())
}

/// Mark a subscription as canceled. Idempotent — already-canceled rows
/// keep their original `canceled_at` timestamp.
pub async fn mark_canceled<C: ConnectionTrait>(
    conn: &C,
    stripe_sub_id: &str,
    canceled_at: DateTime<Utc>,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        UPDATE user_sponsorships
           SET status = 'canceled',
               canceled_at = COALESCE(canceled_at, $2)
         WHERE stripe_subscription_id = $1
        "#,
        [
            stripe_sub_id.to_string().into(),
            canceled_at.fixed_offset().into(),
        ],
    ))
    .await?;
    Ok(())
}

/// Returns true if a row already exists for this `stripe_event_id`.
/// Used by the webhook handler as a pre-check; the partial unique
/// index would also catch a race, but the explicit check lets us skip
/// further work cheaply on a replay.
pub async fn event_already_processed<C: ConnectionTrait>(
    conn: &C,
    stripe_event_id: &str,
) -> Result<bool, DbErr> {
    let row = ent::Entity::find()
        .filter(ent::Column::StripeEventId.eq(stripe_event_id))
        .one(conn)
        .await?;
    Ok(row.is_some())
}

/// Every sponsorship row for a user, newest first.
pub async fn list_for_user<C: ConnectionTrait>(
    conn: &C,
    user_id: Uuid,
) -> Result<Vec<ent::Model>, DbErr> {
    ent::Entity::find()
        .filter(ent::Column::UserId.eq(user_id))
        .order_by_desc(ent::Column::StartedAt)
        .all(conn)
        .await
}

/// Aggregated per-tier label for the public-profile badge. We only
/// expose the `tier` and `amount_cents` (NEVER the underlying Stripe
/// id) so a badge consumer can render gold/silver/bronze without
/// learning anything about the user's payment instruments.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct TierSummary {
    pub tier: Option<String>,
    pub amount_cents: Option<i64>,
}

/// Public-profile-shaped aggregate. `active_subscription` is the
/// most-recent `kind='subscription' AND status='active'` row;
/// `lifetime_total_cents` sums every completed one-time donation
/// AND every (current OR ended) subscription's amount_cents weighted
/// by 1 (see note). `donation_count` only counts one-time donations.
///
/// Subscription weighting: we don't multiply by "months active"
/// because Stripe gives us per-event amount_cents (the latest
/// per-interval price). Surfacing the *total dollars contributed*
/// would require iterating invoices — out of scope for the public
/// badge. The badge intentionally undercounts subscribers; the
/// `active_subscription` field is what conveys ongoing support.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct SponsorshipSummary {
    pub active_subscription: Option<TierSummary>,
    pub lifetime_total_cents: i64,
    pub donation_count: i32,
    pub first_supported_at: Option<DateTimeWithTimeZone>,
    pub latest_supported_at: Option<DateTimeWithTimeZone>,
}

#[derive(Debug, FromQueryResult)]
struct SummaryRow {
    lifetime_total_cents: Option<i64>,
    donation_count: Option<i64>,
    first_supported_at: Option<DateTimeWithTimeZone>,
    latest_supported_at: Option<DateTimeWithTimeZone>,
}

#[derive(Debug, FromQueryResult)]
struct ActiveTierRow {
    tier: Option<String>,
    amount_cents: Option<i64>,
}

pub async fn summary_for_user<C: ConnectionTrait>(
    conn: &C,
    user_id: Uuid,
) -> Result<SponsorshipSummary, DbErr> {
    // Aggregate stats. We sum `amount_cents` for one-time donations
    // (every completed charge) and add the latest known per-interval
    // price for any subscription that ever existed — see the doc
    // comment on `SponsorshipSummary` for rationale.
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        SELECT
            COALESCE(SUM(CASE
                WHEN kind = 'one_time' AND status = 'completed' THEN COALESCE(amount_cents, 0)
                WHEN kind = 'subscription' THEN COALESCE(amount_cents, 0)
                ELSE 0
            END), 0)::BIGINT AS lifetime_total_cents,
            COUNT(*) FILTER (WHERE kind = 'one_time' AND status = 'completed')::BIGINT
                AS donation_count,
            MIN(started_at) AS first_supported_at,
            MAX(started_at) AS latest_supported_at
          FROM user_sponsorships
         WHERE user_id = $1
        "#,
        [user_id.into()],
    );
    let agg = SummaryRow::find_by_statement(stmt)
        .one(conn)
        .await?
        .unwrap_or(SummaryRow {
            lifetime_total_cents: Some(0),
            donation_count: Some(0),
            first_supported_at: None,
            latest_supported_at: None,
        });

    // Active subscription tier (latest by started_at).
    let active_stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        SELECT tier, amount_cents
          FROM user_sponsorships
         WHERE user_id = $1
           AND kind = 'subscription'
           AND status = 'active'
         ORDER BY started_at DESC
         LIMIT 1
        "#,
        [user_id.into()],
    );
    let active = ActiveTierRow::find_by_statement(active_stmt)
        .one(conn)
        .await?
        .map(|r| TierSummary {
            tier: r.tier,
            amount_cents: r.amount_cents,
        });

    Ok(SponsorshipSummary {
        active_subscription: active,
        lifetime_total_cents: agg.lifetime_total_cents.unwrap_or(0),
        donation_count: agg.donation_count.unwrap_or(0) as i32,
        first_supported_at: agg.first_supported_at,
        latest_supported_at: agg.latest_supported_at,
    })
}

/// Insert a subscription row with explicit values. Test-only helper
/// for cases where we want to seed a row without going through the
/// upsert path. Production code should use `upsert_subscription`.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub async fn _insert_for_test<C: ConnectionTrait>(
    conn: &C,
    user_id: Uuid,
    kind: &str,
    tier: Option<&str>,
    amount_cents: Option<i64>,
    stripe_subscription_id: Option<&str>,
    stripe_charge_id: Option<&str>,
    status: &str,
    started_at: DateTime<Utc>,
) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    ent::ActiveModel {
        id: Set(id),
        user_id: Set(user_id),
        stripe_event_id: Set(None),
        kind: Set(kind.into()),
        tier: Set(tier.map(|s| s.into())),
        amount_cents: Set(amount_cents),
        currency: Set("usd".into()),
        stripe_subscription_id: Set(stripe_subscription_id.map(|s| s.into())),
        stripe_charge_id: Set(stripe_charge_id.map(|s| s.into())),
        status: Set(status.into()),
        started_at: Set(started_at.fixed_offset()),
        canceled_at: Set(None),
        created_at: Set(Utc::now().fixed_offset()),
    }
    .insert(conn)
    .await?;
    Ok(id)
}
