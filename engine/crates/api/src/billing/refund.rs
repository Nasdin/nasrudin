//! Stripe refund flow: DB-first → Stripe-second with idempotency.
//!
//! 1. INSERT `refund_records (status='pending')` and write the audit
//!    row in one transaction.
//! 2. Call `POST /v1/refunds` with `Idempotency-Key = refund_record_id`
//!    so a retry after a network blip is safe.
//! 3. On 2xx: mark succeeded with `stripe_refund_id`.
//! 4. On 4xx: mark failed with `stripe_failure_reason`.
//! 5. On 5xx / network: leave pending — the reconciler resolves.
//!
//! Stripe sends the user-facing "Refund Issued" email automatically.
//! We do not queue any email here.

use serde::Deserialize;
use uuid::Uuid;

#[derive(Debug, Deserialize)]
pub struct ChargeView {
    pub id: String,
    pub customer: Option<String>,
    pub amount: i64,
    pub currency: String,
    pub status: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct RefundResponse {
    pub id: String,
    pub status: String,
}

/// Fetch a charge by id. Returns `Ok(None)` on 404 so the caller can
/// surface a 422-shaped error to the admin without a stack trace.
pub async fn fetch_charge(
    client: &reqwest::Client,
    base_url: &str,
    secret: &str,
    charge_id: &str,
) -> Result<Option<ChargeView>, anyhow::Error> {
    let resp = client
        .get(format!("{base_url}/v1/charges/{charge_id}"))
        .bearer_auth(secret)
        .send()
        .await?;
    if resp.status().as_u16() == 404 {
        return Ok(None);
    }
    if !resp.status().is_success() {
        anyhow::bail!("stripe charge fetch failed: {}", resp.status());
    }
    Ok(Some(resp.json().await?))
}

/// Create a refund. `idempotency_key` is the refund_records.id; Stripe
/// returns the same response on retry within the idempotency window
/// (24 hours).
pub async fn create_refund(
    client: &reqwest::Client,
    base_url: &str,
    secret: &str,
    charge_id: &str,
    amount_cents: i64,
    idempotency_key: Uuid,
    refund_record_id: Uuid,
) -> Result<RefundResponse, anyhow::Error> {
    let resp = client
        .post(format!("{base_url}/v1/refunds"))
        .bearer_auth(secret)
        .header("Idempotency-Key", idempotency_key.to_string())
        .form(&[
            ("charge".to_string(), charge_id.to_string()),
            ("amount".to_string(), amount_cents.to_string()),
            (
                "metadata[refund_record_id]".to_string(),
                refund_record_id.to_string(),
            ),
        ])
        .send()
        .await?;
    let status = resp.status();
    if status.is_success() {
        return Ok(resp.json().await?);
    }
    let body = resp.text().await.unwrap_or_default();
    if status.as_u16() >= 400 && status.as_u16() < 500 {
        anyhow::bail!("4xx: stripe rejected refund: {body}");
    }
    anyhow::bail!("5xx: stripe transient: {body}");
}
