//! HTTP client for the paid Researcher tier endpoints.
//!
//! Distinct from `research_client.rs` (which targets the legacy
//! `/api/conjecture/*` Phase E flow). The paid Researcher tier lives
//! under `/api/jobs/*` and runs against a different state machine —
//! `queued`/`claimed`/`running` with a 96 lake-slot-hour quota and
//! cluster-side capacity gating.
//!
//! Worker contract per job:
//!   1. POST /api/jobs/claim with current `available_lake_slots`.
//!   2. On 200, run a paid GA slice; heartbeat every 30 s with
//!      `lake_slot_hours_consumed_delta`.
//!   3. On a verified theorem matching the conjecture target, call
//!      `mark_proved`.
//!   4. On normal end-of-budget (`continue: false` from heartbeat),
//!      stop. On voluntary abandon (shutdown, network loss), call
//!      `release` so another worker can pick the job up immediately.
//!
//! All calls use the worker's `nsk_worker_…` bearer.

use anyhow::{Context, Result};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::time::Duration;
use uuid::Uuid;

#[derive(Debug, Clone, Serialize)]
pub struct ClaimBody {
    pub available_lake_slots: u32,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub domains_supported: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct PaidJob {
    pub job_id: Uuid,
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub suggestions: Option<serde_json::Value>,
    pub lake_slot_hours_remaining: f32,
    pub lease_expires_at: Option<String>,
    pub heartbeat_url: String,
    pub release_url: String,
    pub mark_proved_url: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct HeartbeatBody {
    pub candidates_attempted_delta: i32,
    pub candidates_verified_delta: i32,
    pub lake_slot_hours_consumed_delta: f32,
    pub current_best_fitness: f32,
    pub current_best_chain_length: i32,
}

#[derive(Debug, Clone, Deserialize)]
pub struct HeartbeatResp {
    #[serde(rename = "continue")]
    pub continue_: bool,
    pub lake_slot_hours_consumed: Option<f32>,
    pub reason: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct MarkProvedBody {
    pub theorem_id_hex: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub statement_latex: Option<String>,
}

pub struct PaidJobsClient {
    pub api_url: String,
    pub worker_key: String,
    http: Client,
}

impl PaidJobsClient {
    pub fn new(api_url: String, worker_key: String) -> Self {
        Self {
            api_url,
            worker_key,
            http: Client::builder()
                .timeout(Duration::from_secs(30))
                .build()
                .expect("reqwest client"),
        }
    }

    /// `Ok(Some(job))` on award, `Ok(None)` on 204 (queue empty or
    /// explorer floor protection). `Err` is reserved for transport /
    /// auth failures the caller should log + retry on.
    pub async fn claim(&self, body: &ClaimBody) -> Result<Option<PaidJob>> {
        let resp = self
            .http
            .post(format!("{}/api/jobs/claim", self.api_url))
            .bearer_auth(&self.worker_key)
            .json(body)
            .send()
            .await
            .context("POST /api/jobs/claim")?;
        if resp.status() == reqwest::StatusCode::NO_CONTENT {
            return Ok(None);
        }
        let resp = resp.error_for_status()?;
        Ok(Some(resp.json::<PaidJob>().await?))
    }

    pub async fn heartbeat(&self, id: Uuid, body: &HeartbeatBody) -> Result<HeartbeatResp> {
        let resp = self
            .http
            .post(format!("{}/api/jobs/{id}/heartbeat", self.api_url))
            .bearer_auth(&self.worker_key)
            .json(body)
            .send()
            .await?
            .error_for_status()?;
        Ok(resp.json::<HeartbeatResp>().await?)
    }

    pub async fn release(&self, id: Uuid) -> Result<()> {
        self.http
            .post(format!("{}/api/jobs/{id}/release", self.api_url))
            .bearer_auth(&self.worker_key)
            .send()
            .await?
            .error_for_status()?;
        Ok(())
    }

    pub async fn mark_proved(&self, id: Uuid, body: &MarkProvedBody) -> Result<()> {
        self.http
            .post(format!("{}/api/jobs/{id}/mark_proved", self.api_url))
            .bearer_auth(&self.worker_key)
            .json(body)
            .send()
            .await?
            .error_for_status()?;
        Ok(())
    }
}
