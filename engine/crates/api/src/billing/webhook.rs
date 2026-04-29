//! Stripe webhook signature verification + dispatch.
//!
//! Built on `stripe::Webhook::construct_event` — async-stripe handles
//! the HMAC-SHA256 over `<timestamp>.<body>`, the v1 signature parsing,
//! and the rotation-window multi-signature accept. We just give it the
//! payload + header + secret and pattern-match on the typed
//! `EventObject`.

use stripe::{Event, EventObject, EventType, Webhook, WebhookError};

use crate::billing::stripe_client::{customer_id_from_expandable, first_price_id, BillingConfig};
use crate::billing::tier::PlanTier;

#[derive(Debug, thiserror::Error)]
pub enum DispatchError {
    #[error("no customer on event")]
    NoCustomer,
    #[error("db: {0}")]
    Db(#[from] nasrudin_pg::sea_orm::DbErr),
}

/// Verify the `Stripe-Signature` header against the raw body and return
/// the typed `Event`. Wraps `stripe::Webhook::construct_event`.
pub fn parse_event(payload: &[u8], sig_header: &str, secret: &str) -> Result<Event, WebhookError> {
    let payload_str = std::str::from_utf8(payload).map_err(|_| WebhookError::BadKey)?;
    Webhook::construct_event(payload_str, sig_header, secret)
}

/// Phase-1 price→tier map. Researcher is the only paid tier with
/// self-serve checkout right now; Team / Institution / Enterprise route
/// through a sales-contact CTA and ship in a separate plan.
pub fn tier_for_price(price_id: &str, cfg: &BillingConfig) -> PlanTier {
    if price_id == cfg.price_researcher_monthly || price_id == cfg.price_researcher_annual {
        PlanTier::Researcher
    } else {
        PlanTier::Free
    }
}

/// Drive `users.plan_tier` and the Stripe-side period columns from a
/// webhook event. Returns `Ok(())` on the no-op event types we don't
/// care about, so the caller can mark them processed without branching.
pub async fn dispatch(
    event: &Event,
    cfg: &BillingConfig,
    pg: &nasrudin_pg::sea_orm::DatabaseConnection,
) -> Result<(), DispatchError> {
    match (&event.type_, &event.data.object) {
        (
            EventType::CustomerSubscriptionCreated | EventType::CustomerSubscriptionUpdated,
            EventObject::Subscription(sub),
        ) => {
            let customer_id = customer_id_from_expandable(&sub.customer)
                .ok_or(DispatchError::NoCustomer)?;
            // Stripe's status enum: any of these terminal states means
            // "treat as cancelled" even when arriving via .updated.
            let cancelled = matches!(
                sub.status,
                stripe::SubscriptionStatus::Canceled
                    | stripe::SubscriptionStatus::IncompleteExpired
                    | stripe::SubscriptionStatus::Unpaid
            );
            if cancelled {
                nasrudin_pg::query::billing::apply_subscription_cancelled(pg, &customer_id)
                    .await?;
                return Ok(());
            }
            let price_id = first_price_id(sub).unwrap_or_default();
            let tier = tier_for_price(&price_id, cfg);
            let cycle_start = chrono::DateTime::<chrono::Utc>::from_timestamp(
                sub.current_period_start,
                0,
            )
            .unwrap_or_else(chrono::Utc::now);
            let period_end =
                chrono::DateTime::<chrono::Utc>::from_timestamp(sub.current_period_end, 0)
                    .unwrap_or_else(chrono::Utc::now);
            nasrudin_pg::query::billing::apply_subscription_active(
                pg,
                &customer_id,
                sub.id.as_str(),
                tier.as_db(),
                cycle_start,
                period_end,
            )
            .await?;
            Ok(())
        }
        (EventType::CustomerSubscriptionDeleted, EventObject::Subscription(sub)) => {
            let customer_id = customer_id_from_expandable(&sub.customer)
                .ok_or(DispatchError::NoCustomer)?;
            nasrudin_pg::query::billing::apply_subscription_cancelled(pg, &customer_id).await?;
            Ok(())
        }
        // invoice.paid / invoice.payment_failed are no-ops at Phase 1 —
        // subscription.updated already drives period rollover. Dunning
        // UX (warn user, downgrade on grace period exhaust) is later.
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg_with_prices(monthly: &str, annual: &str) -> BillingConfig {
        BillingConfig {
            price_researcher_monthly: monthly.to_string(),
            price_researcher_annual: annual.to_string(),
            checkout_success_url: "x".into(),
            checkout_cancel_url: "x".into(),
            portal_return_url: "x".into(),
            webhook_secret: "x".into(),
        }
    }

    #[test]
    fn rejects_invalid_signature() {
        let result = parse_event(b"{}", "t=1,v1=garbage", "whsec_test");
        assert!(result.is_err());
    }

    #[test]
    fn rejects_missing_v1() {
        let result = parse_event(b"{}", "t=1700000000", "whsec_test");
        assert!(result.is_err());
    }

    #[test]
    fn tier_map_picks_researcher_for_known_price() {
        let cfg = cfg_with_prices("price_monthly_xyz", "price_annual_xyz");
        assert_eq!(
            tier_for_price("price_monthly_xyz", &cfg),
            PlanTier::Researcher
        );
        assert_eq!(
            tier_for_price("price_annual_xyz", &cfg),
            PlanTier::Researcher
        );
        assert_eq!(tier_for_price("price_unknown", &cfg), PlanTier::Free);
    }
}
