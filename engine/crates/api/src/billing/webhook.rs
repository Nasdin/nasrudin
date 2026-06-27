//! Stripe webhook signature verification + dispatch.
//!
//! Built on `stripe_webhook::Webhook::construct_event` — async-stripe
//! handles the HMAC-SHA256 over `<timestamp>.<body>`, the v1 signature
//! parsing, and the rotation-window multi-signature accept. We just
//! give it the payload + header + secret and pattern-match on the
//! typed `EventObject`.
//!
//! async-stripe 1.0 split the SDK; the webhook surface lives in
//! `async-stripe-webhook` (`stripe_webhook::*`). `Subscription` +
//! `SubscriptionStatus` are in `stripe_shared`; `Expandable` is in
//! `stripe_types`; `CheckoutSessionMode` is in `stripe_checkout`.

use stripe_shared::{CheckoutSessionMode, SubscriptionStatus};
use stripe_types::Expandable;
use stripe_webhook::{Event, EventObject, Webhook, WebhookError};

use crate::billing::stripe_client::{BillingConfig, customer_id_from_expandable, first_price_id};
use crate::billing::tier::PlanTier;

/// Translate a Stripe price id into our internal sponsorship tier
/// label. Returns `None` for prices we don't recognise (e.g. legacy
/// or test prices) — those still produce a sponsorship row, but with
/// `tier=NULL` so the public-profile renderer falls back to the
/// generic badge.
pub fn sponsorship_tier_for_price(price_id: &str, cfg: &BillingConfig) -> Option<&'static str> {
    if price_id.is_empty() {
        return None;
    }
    if price_id == cfg.price_researcher_monthly {
        Some("researcher_monthly")
    } else if price_id == cfg.price_researcher_annual {
        Some("researcher_annual")
    } else if price_id == cfg.price_sponsor_5 {
        Some("sponsor_5")
    } else if price_id == cfg.price_sponsor_25 {
        Some("sponsor_25")
    } else if price_id == cfg.price_sponsor_100 {
        Some("sponsor_100")
    } else if price_id == cfg.price_sponsor_open {
        Some("sponsor_open")
    } else {
        None
    }
}

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

/// Phase-1 price→tier map. Researcher is the only paid *service* tier
/// with self-serve checkout right now; Team / Institution / Enterprise
/// route through a sales-contact CTA and ship in a separate plan.
///
/// Sponsor prices stay `PlanTier::Free` — they're donations, not service
/// upgrades. The Stripe customer record is still the source of truth for
/// "this user is a sponsor"; we just don't grant Researcher quota for it.
pub fn tier_for_price(price_id: &str, cfg: &BillingConfig) -> PlanTier {
    if price_id == cfg.price_researcher_monthly || price_id == cfg.price_researcher_annual {
        PlanTier::Researcher
    } else {
        // Includes sponsor prices and any unrecognized id — both stay Free.
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
    // async-stripe 1.0: EventObject variants now encode the EventType
    // directly (e.g. `CustomerSubscriptionCreated(Box<Subscription>)`),
    // so the dispatch is a single match on `event.data.object`.
    match &event.data.object {
        EventObject::CustomerSubscriptionCreated(sub)
        | EventObject::CustomerSubscriptionUpdated(sub) => {
            let customer_id =
                customer_id_from_expandable(&sub.customer).ok_or(DispatchError::NoCustomer)?;
            // Stripe's status enum: any of these terminal states means
            // "treat as cancelled" even when arriving via .updated.
            let cancelled = matches!(
                sub.status,
                SubscriptionStatus::Canceled
                    | SubscriptionStatus::IncompleteExpired
                    | SubscriptionStatus::Unpaid
            );
            if cancelled {
                nasrudin_pg::query::billing::apply_subscription_cancelled(pg, &customer_id).await?;
                // Mirror to the public-profile ledger.
                let now = chrono::Utc::now();
                let _ =
                    nasrudin_pg::query::user_sponsorships::mark_canceled(pg, sub.id.as_str(), now)
                        .await;
                return Ok(());
            }
            let price_id = first_price_id(sub).unwrap_or_default();
            let tier = tier_for_price(&price_id, cfg);
            // async-stripe 1.0: `current_period_start/end` moved off the
            // top-level Subscription onto each SubscriptionItem (every
            // item now has its own billing cycle). Our Phase-1 plans
            // have exactly one item, so reading from the first item is
            // semantically equivalent.
            let (cycle_start_ts, period_end_ts) = sub
                .items
                .data
                .first()
                .map(|i| (i.current_period_start, i.current_period_end))
                .unwrap_or((sub.start_date, sub.start_date));
            let cycle_start = chrono::DateTime::<chrono::Utc>::from_timestamp(cycle_start_ts, 0)
                .unwrap_or_else(chrono::Utc::now);
            let period_end = chrono::DateTime::<chrono::Utc>::from_timestamp(period_end_ts, 0)
                .unwrap_or_else(chrono::Utc::now);
            // Credits grant runs BEFORE apply_subscription_active so
            // it can read the user's PREVIOUS plan_cycle_start to
            // detect a fresh period. apply_subscription_active then
            // overwrites plan_cycle_start with the new value.
            let credits = tier.quotas().research_credits_per_period as i32;
            if credits > 0 {
                match nasrudin_pg::query::users::grant_research_credits_on_period_advance(
                    pg,
                    &customer_id,
                    cycle_start,
                    credits,
                )
                .await
                {
                    Ok(1) => tracing::info!(
                        customer = %customer_id,
                        tier = %tier.as_db(),
                        credits,
                        "research_credits granted (new billing period)"
                    ),
                    Ok(_) => tracing::debug!(
                        customer = %customer_id,
                        "research_credits unchanged (same billing period — Stripe sub.updated for non-period-advance reason)"
                    ),
                    Err(e) => tracing::warn!(
                        customer = %customer_id,
                        error = %e,
                        "research_credits grant failed (continuing — subscription state still applies)"
                    ),
                }
            }

            nasrudin_pg::query::billing::apply_subscription_active(
                pg,
                &customer_id,
                sub.id.as_str(),
                tier.as_db(),
                cycle_start,
                period_end,
            )
            .await?;

            // Public-profile sponsorship ledger. Resolve customer →
            // user; a missing user is logged but not treated as a
            // dispatch error (apply_subscription_active is the
            // source of truth for entitlement; the ledger is
            // best-effort decoration for the profile badge).
            if let Ok(Some(user)) =
                nasrudin_pg::query::users::find_by_stripe_customer_id(pg, &customer_id).await
            {
                let amount_cents = sub
                    .items
                    .data
                    .first()
                    .and_then(|item| item.price.unit_amount);
                let sponsor_tier = sponsorship_tier_for_price(&price_id, cfg);
                let started_at = chrono::DateTime::<chrono::Utc>::from_timestamp(sub.start_date, 0)
                    .unwrap_or(cycle_start);
                if let Err(e) = nasrudin_pg::query::user_sponsorships::upsert_subscription(
                    pg,
                    user.id,
                    sub.id.as_str(),
                    sponsor_tier,
                    amount_cents,
                    "active",
                    started_at,
                    Some(event.id.as_str()),
                )
                .await
                {
                    tracing::warn!(
                        customer = %customer_id,
                        error = %e,
                        "user_sponsorships upsert (subscription) failed",
                    );
                }
            }

            Ok(())
        }
        EventObject::CustomerSubscriptionDeleted(sub) => {
            let customer_id =
                customer_id_from_expandable(&sub.customer).ok_or(DispatchError::NoCustomer)?;
            nasrudin_pg::query::billing::apply_subscription_cancelled(pg, &customer_id).await?;
            let canceled_at = sub
                .canceled_at
                .and_then(|ts| chrono::DateTime::<chrono::Utc>::from_timestamp(ts, 0))
                .unwrap_or_else(chrono::Utc::now);
            if let Err(e) = nasrudin_pg::query::user_sponsorships::mark_canceled(
                pg,
                sub.id.as_str(),
                canceled_at,
            )
            .await
            {
                tracing::warn!(error = %e, "user_sponsorships mark_canceled failed");
            }
            Ok(())
        }
        EventObject::CheckoutSessionCompleted(session) => {
            // Pay-what-you-want one-time donation. Subscriptions
            // also fire `checkout.session.completed`, but
            // `subscription.created` already covers them — we filter
            // here on `mode == Payment` to avoid double-recording.
            if session.mode != CheckoutSessionMode::Payment {
                return Ok(());
            }
            // Idempotency belt-and-braces: the partial unique index
            // on stripe_event_id catches replays at the DB layer,
            // but checking here lets us short-circuit cheaply.
            if nasrudin_pg::query::user_sponsorships::event_already_processed(pg, event.id.as_str())
                .await
                .unwrap_or(false)
            {
                return Ok(());
            }
            let customer_id = match session.customer.as_ref() {
                Some(c) => customer_id_from_expandable(c).ok_or(DispatchError::NoCustomer)?,
                None => return Ok(()), // anonymous donations skipped
            };
            let user = match nasrudin_pg::query::users::find_by_stripe_customer_id(pg, &customer_id)
                .await?
            {
                Some(u) => u,
                None => return Ok(()), // donation by a customer with no user account; nothing to attribute
            };
            // Use the PaymentIntent id as the unique charge key. The
            // CheckoutSession itself isn't unique per payment for
            // long-lived sessions, but every successful payment
            // exposes a fresh PaymentIntent id, so we get
            // idempotent insert via the UNIQUE(stripe_charge_id)
            // constraint regardless of webhook replays.
            let charge_key = session
                .payment_intent
                .as_ref()
                .map(|pi| match pi {
                    Expandable::Id(id) => id.to_string(),
                    Expandable::Object(obj) => obj.id.to_string(),
                })
                .unwrap_or_else(|| session.id.to_string());
            let amount = session.amount_total.unwrap_or(0);
            let started_at = chrono::DateTime::<chrono::Utc>::from_timestamp(session.created, 0)
                .unwrap_or_else(chrono::Utc::now);
            // For the open-amount donate flow we tag the price as
            // `sponsor_open`; any other one-time charge falls back
            // to NULL.
            let tier = session
                .metadata
                .as_ref()
                .and_then(|m| m.get("kind"))
                .map(|s| s.as_str());
            if let Err(e) = nasrudin_pg::query::user_sponsorships::upsert_one_time(
                pg,
                user.id,
                &charge_key,
                tier,
                amount,
                started_at,
                Some(event.id.as_str()),
            )
            .await
            {
                tracing::warn!(
                    customer = %customer_id,
                    error = %e,
                    "user_sponsorships upsert (one_time) failed",
                );
            }
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
            price_sponsor_5: String::new(),
            price_sponsor_25: String::new(),
            price_sponsor_100: String::new(),
            price_sponsor_open: String::new(),
            sponsor_payment_link: String::new(),
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
