//! Webhook-driven user-state mutations and event idempotency.
//!
//! Stripe webhook → `record_event_if_new` (idempotent insert) → dispatch
//! → `apply_subscription_active` / `apply_subscription_cancelled` →
//! `mark_event_processed` (success / error).

use chrono::{DateTime, Utc};
use sea_orm::ActiveValue::*;
use sea_orm::prelude::*;
use uuid::Uuid;

use crate::entity::{billing_events, users};

/// Idempotent webhook insert. Returns `Ok(true)` if newly inserted,
/// `Ok(false)` if Stripe replayed a delivery we've already processed.
pub async fn record_event_if_new(
    db: &DatabaseConnection,
    stripe_event_id: &str,
    event_type: &str,
    payload: serde_json::Value,
) -> Result<bool, DbErr> {
    let existing = billing_events::Entity::find()
        .filter(billing_events::Column::StripeEventId.eq(stripe_event_id))
        .one(db)
        .await?;
    if existing.is_some() {
        return Ok(false);
    }
    billing_events::ActiveModel {
        id: Set(Uuid::new_v4()),
        stripe_event_id: Set(stripe_event_id.to_string()),
        event_type: Set(event_type.to_string()),
        payload: Set(payload),
        received_at: Set(Utc::now().fixed_offset()),
        processed_at: NotSet,
        process_error: NotSet,
    }
    .insert(db)
    .await
    .map(|_| true)
}

pub async fn mark_event_processed(
    db: &DatabaseConnection,
    stripe_event_id: &str,
    error: Option<&str>,
) -> Result<(), DbErr> {
    let err_value: Option<String> = error.map(|s| s.to_string());
    billing_events::Entity::update_many()
        .col_expr(
            billing_events::Column::ProcessedAt,
            Expr::value(Utc::now().fixed_offset()),
        )
        .col_expr(billing_events::Column::ProcessError, Expr::value(err_value))
        .filter(billing_events::Column::StripeEventId.eq(stripe_event_id))
        .exec(db)
        .await
        .map(|_| ())
}

pub async fn apply_subscription_active(
    db: &DatabaseConnection,
    customer_id: &str,
    subscription_id: &str,
    plan_tier: &str,
    cycle_start: DateTime<Utc>,
    period_end: DateTime<Utc>,
) -> Result<(), DbErr> {
    users::Entity::update_many()
        .col_expr(users::Column::PlanTier, Expr::value(plan_tier))
        .col_expr(
            users::Column::StripeSubscriptionId,
            Expr::value(subscription_id),
        )
        .col_expr(
            users::Column::PlanCycleStart,
            Expr::value(cycle_start.fixed_offset()),
        )
        .col_expr(
            users::Column::CurrentPeriodEnd,
            Expr::value(period_end.fixed_offset()),
        )
        .filter(users::Column::StripeCustomerId.eq(customer_id))
        .exec(db)
        .await
        .map(|_| ())
}

pub async fn apply_subscription_cancelled(
    db: &DatabaseConnection,
    customer_id: &str,
) -> Result<(), DbErr> {
    let no_string: Option<String> = None;
    let no_dt: Option<chrono::DateTime<chrono::FixedOffset>> = None;
    users::Entity::update_many()
        .col_expr(users::Column::PlanTier, Expr::value("free"))
        .col_expr(users::Column::StripeSubscriptionId, Expr::value(no_string))
        .col_expr(users::Column::CurrentPeriodEnd, Expr::value(no_dt))
        .filter(users::Column::StripeCustomerId.eq(customer_id))
        .exec(db)
        .await
        .map(|_| ())
}
