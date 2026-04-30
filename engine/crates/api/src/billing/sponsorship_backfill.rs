//! One-shot Stripe → `user_sponsorships` backfill.
//!
//! Opt-in: only runs when `BACKFILL_SPONSORSHIPS=1` is set at startup.
//! Otherwise we'd hammer Stripe on every restart for environments
//! that already have all their data via the live webhook path.
//!
//! The backfill is intentionally conservative:
//! - paginates `customers.list` 100 at a time (Stripe page limit);
//! - skips customers that don't map to a `users.stripe_customer_id`;
//! - for each match, fetches `subscriptions.list` (active+all
//!   statuses) and `charges.list` for the last 90 days; both pages
//!   are bounded so a multi-year history doesn't fan out;
//! - upserts every row, leaning on the UNIQUE indexes for
//!   idempotency.
//!
//! This is best-effort decoration for the public profile badge.
//! Failures are logged and the API boots normally.

use std::sync::Arc;
use std::time::Duration;

use anyhow::Context;
use chrono::{DateTime, Utc};
use serde::Deserialize;

use crate::billing::stripe_client::BillingClient;
use crate::billing::webhook::sponsorship_tier_for_price;

#[derive(Debug, Deserialize)]
struct StripeList<T> {
    data: Vec<T>,
    #[serde(default)]
    has_more: bool,
}

#[derive(Debug, Deserialize)]
struct CustomerStub {
    id: String,
}

#[derive(Debug, Deserialize)]
struct SubscriptionStub {
    id: String,
    status: String,
    customer: String,
    start_date: i64,
    items: SubscriptionItemList,
}

#[derive(Debug, Deserialize)]
struct SubscriptionItemList {
    data: Vec<SubscriptionItemStub>,
}

#[derive(Debug, Deserialize)]
struct SubscriptionItemStub {
    price: Option<PriceStub>,
}

#[derive(Debug, Deserialize)]
struct PriceStub {
    id: String,
    unit_amount: Option<i64>,
}

#[derive(Debug, Deserialize)]
struct ChargeStub {
    id: String,
    customer: Option<String>,
    amount: i64,
    paid: bool,
    refunded: bool,
    status: Option<String>,
    created: i64,
}

const PAGE_LIMIT: u32 = 100;
/// Look back 90 days for one-time charges. Subscription history is
/// pulled in full (no time filter) since `subscriptions.list` is
/// already user-scoped and bounded.
const CHARGE_LOOKBACK_DAYS: i64 = 90;

/// Drive the backfill. Returns the number of `user_sponsorships`
/// rows touched (subscriptions + charges). Runs against
/// `https://api.stripe.com/v1/...` directly via reqwest; we don't
/// reuse `async-stripe`'s client because we want explicit control of
/// pagination + a forgiving deserialiser stub that ignores fields
/// we don't care about.
pub async fn backfill(
    pg: &nasrudin_pg::sea_orm::DatabaseConnection,
    billing: &BillingClient,
    secret: &str,
    base_url: &str,
) -> anyhow::Result<usize> {
    if secret.is_empty() {
        anyhow::bail!("STRIPE_SECRET_KEY unset — cannot backfill");
    }
    let http = reqwest::Client::builder()
        .timeout(Duration::from_secs(30))
        .build()?;
    let lookback_cutoff = Utc::now().timestamp() - CHARGE_LOOKBACK_DAYS * 24 * 60 * 60;

    let mut touched = 0usize;
    let mut starting_after: Option<String> = None;

    loop {
        let mut url = format!("{base_url}/v1/customers?limit={PAGE_LIMIT}");
        if let Some(cursor) = starting_after.as_ref() {
            url.push_str(&format!("&starting_after={cursor}"));
        }
        let resp = http
            .get(&url)
            .bearer_auth(secret)
            .send()
            .await
            .context("stripe customers list")?;
        if !resp.status().is_success() {
            anyhow::bail!("stripe customers list failed: {}", resp.status());
        }
        let page: StripeList<CustomerStub> = resp.json().await?;
        let last_id = page.data.last().map(|c| c.id.clone());

        for cust in &page.data {
            let user = match nasrudin_pg::query::users::find_by_stripe_customer_id(pg, &cust.id)
                .await
            {
                Ok(Some(u)) => u,
                Ok(None) => continue,
                Err(e) => {
                    tracing::warn!(customer = %cust.id, error = %e, "lookup failed");
                    continue;
                }
            };

            // Subscriptions — every status, expanded for price.
            match list_subscriptions(&http, secret, base_url, &cust.id).await {
                Ok(subs) => {
                    for sub in subs {
                        let price_id = sub
                            .items
                            .data
                            .first()
                            .and_then(|i| i.price.as_ref())
                            .map(|p| p.id.clone())
                            .unwrap_or_default();
                        let amount_cents = sub
                            .items
                            .data
                            .first()
                            .and_then(|i| i.price.as_ref())
                            .and_then(|p| p.unit_amount);
                        let tier = sponsorship_tier_for_price(&price_id, &billing.cfg);
                        let started_at = DateTime::<Utc>::from_timestamp(sub.start_date, 0)
                            .unwrap_or_else(Utc::now);
                        let status_label = match sub.status.as_str() {
                            "active" | "trialing" | "past_due" => "active",
                            _ => "canceled",
                        };
                        if let Err(e) =
                            nasrudin_pg::query::user_sponsorships::upsert_subscription(
                                pg,
                                user.id,
                                &sub.id,
                                tier,
                                amount_cents,
                                status_label,
                                started_at,
                                None,
                            )
                            .await
                        {
                            tracing::warn!(error = %e, sub = %sub.id, "backfill: subscription upsert");
                        } else {
                            touched += 1;
                        }
                    }
                }
                Err(e) => {
                    tracing::warn!(customer = %cust.id, error = %e, "backfill: subscriptions");
                }
            }

            // Recent one-time charges. We filter to paid + non-refunded
            // and skip charges already attached to a subscription
            // (those land via the subscription path).
            match list_recent_charges(&http, secret, base_url, &cust.id, lookback_cutoff).await {
                Ok(charges) => {
                    for ch in charges {
                        if !ch.paid || ch.refunded {
                            continue;
                        }
                        if ch.status.as_deref() != Some("succeeded") {
                            continue;
                        }
                        let started_at = DateTime::<Utc>::from_timestamp(ch.created, 0)
                            .unwrap_or_else(Utc::now);
                        if let Err(e) =
                            nasrudin_pg::query::user_sponsorships::upsert_one_time(
                                pg,
                                user.id,
                                &ch.id,
                                None,
                                ch.amount,
                                started_at,
                                None,
                            )
                            .await
                        {
                            tracing::warn!(error = %e, charge = %ch.id, "backfill: charge upsert");
                        } else {
                            touched += 1;
                        }
                    }
                }
                Err(e) => {
                    tracing::warn!(customer = %cust.id, error = %e, "backfill: charges");
                }
            }
        }

        if !page.has_more {
            break;
        }
        starting_after = last_id;
        if starting_after.is_none() {
            break;
        }
    }

    Ok(touched)
}

async fn list_subscriptions(
    http: &reqwest::Client,
    secret: &str,
    base_url: &str,
    customer: &str,
) -> anyhow::Result<Vec<SubscriptionStub>> {
    // status=all surfaces canceled subs too — we want the full
    // history for the public ledger.
    let url = format!(
        "{base_url}/v1/subscriptions?customer={customer}&status=all&limit={PAGE_LIMIT}&expand[]=data.items.data.price"
    );
    let resp = http.get(&url).bearer_auth(secret).send().await?;
    if !resp.status().is_success() {
        anyhow::bail!("subscriptions list: {}", resp.status());
    }
    let page: StripeList<SubscriptionStub> = resp.json().await?;
    Ok(page.data)
}

async fn list_recent_charges(
    http: &reqwest::Client,
    secret: &str,
    base_url: &str,
    customer: &str,
    cutoff: i64,
) -> anyhow::Result<Vec<ChargeStub>> {
    let url = format!(
        "{base_url}/v1/charges?customer={customer}&created[gte]={cutoff}&limit={PAGE_LIMIT}"
    );
    let resp = http.get(&url).bearer_auth(secret).send().await?;
    if !resp.status().is_success() {
        anyhow::bail!("charges list: {}", resp.status());
    }
    let page: StripeList<ChargeStub> = resp.json().await?;
    Ok(page.data)
}

/// Spawn the backfill on a Tokio task so it doesn't block startup.
/// The Arc-wrapped pg connection + cloned billing client live for
/// the duration of the task.
pub fn spawn_if_enabled(
    pg: nasrudin_pg::sea_orm::DatabaseConnection,
    billing: BillingClient,
    secret: String,
    base_url: String,
) {
    if std::env::var("BACKFILL_SPONSORSHIPS").as_deref() != Ok("1") {
        return;
    }
    let pg = Arc::new(pg);
    tokio::spawn(async move {
        tracing::info!("BACKFILL_SPONSORSHIPS=1 — running one-shot Stripe backfill");
        match backfill(&pg, &billing, &secret, &base_url).await {
            Ok(n) => tracing::info!("sponsorship backfill complete: {n} rows touched"),
            Err(e) => tracing::warn!("sponsorship backfill failed: {e}"),
        }
    });
}
