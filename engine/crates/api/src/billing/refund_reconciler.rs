//! 60-second reconciler that walks `refund_records` rows still
//! `status='pending'` after 90 seconds and asks Stripe whether they
//! actually went through.
//!
//! Why 90s buffer: the happy-path handler typically resolves a refund
//! within 1–2s. A pending row older than that means the API process
//! crashed mid-call or Stripe was 5xx. Stripe's idempotency-key
//! semantics guarantee a single refund per refund_records.id even if
//! we retried the POST during the crash window — the reconciler just
//! needs to ask "did it go through?".
//!
//! After 5 minutes, mark as `failed` with reconciler_timeout — we've
//! given Stripe enough time, the request is presumed dead.

use std::time::Duration;

use nasrudin_pg::sea_orm::DatabaseConnection;

pub fn spawn(
    pg: DatabaseConnection,
    http: reqwest::Client,
    base_url: String,
    secret: String,
) {
    if secret.is_empty() {
        tracing::info!("refund reconciler disabled (STRIPE_SECRET_KEY unset)");
        return;
    }
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(60));
        interval.tick().await; // burn the immediate tick
        loop {
            interval.tick().await;
            tick_once(&pg, &http, &base_url, &secret).await;
        }
    });
}

pub async fn tick_once(
    pg: &DatabaseConnection,
    http: &reqwest::Client,
    base_url: &str,
    secret: &str,
) {
    let stale = match nasrudin_pg::query::refund_records::list_pending_older_than(pg, 90).await {
        Ok(r) => r,
        Err(e) => {
            tracing::warn!(error = %e, "refund reconciler: list_pending_older_than failed");
            return;
        }
    };
    for record in stale {
        let url = format!(
            "{base_url}/v1/refunds?charge={}&limit=100",
            record.stripe_charge_id
        );
        let resp = match http.get(&url).bearer_auth(secret).send().await {
            Ok(r) => r,
            Err(e) => {
                tracing::warn!(error = %e, "stripe list refunds failed");
                continue;
            }
        };
        let body: serde_json::Value = match resp.json().await {
            Ok(v) => v,
            Err(e) => {
                tracing::warn!(error = %e, "stripe list refunds: bad json");
                continue;
            }
        };
        let arr = body.get("data").and_then(|v| v.as_array());
        let needle = record.id.to_string();
        let matched = arr.and_then(|items| {
            items.iter().find(|r| {
                r.pointer("/metadata/refund_record_id")
                    .and_then(|v| v.as_str())
                    == Some(&needle)
            })
        });
        match matched {
            Some(m) => {
                let stripe_id = m.get("id").and_then(|v| v.as_str()).unwrap_or_default();
                let status = m.get("status").and_then(|v| v.as_str()).unwrap_or("pending");
                if status == "succeeded" {
                    let _ = nasrudin_pg::query::refund_records::mark_succeeded(
                        pg, record.id, stripe_id,
                    )
                    .await;
                } else if status == "failed" {
                    let _ = nasrudin_pg::query::refund_records::mark_failed(
                        pg,
                        record.id,
                        "stripe_returned_failed",
                    )
                    .await;
                }
                // pending → leave; reconciler will revisit next tick.
            }
            None => {
                // No matching refund at Stripe AND we've been pending for
                // 5+ minutes → presume dead.
                let elapsed = chrono::Utc::now().timestamp() - record.requested_at.timestamp();
                if elapsed > 300 {
                    let _ = nasrudin_pg::query::refund_records::mark_failed(
                        pg,
                        record.id,
                        "reconciler_timeout",
                    )
                    .await;
                }
            }
        }
    }
}
