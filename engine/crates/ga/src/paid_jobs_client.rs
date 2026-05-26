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

use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::worker_http::WorkerHttp;

#[derive(Debug, Clone, Serialize)]
pub struct ClaimBody {
    pub available_lake_slots: u32,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub domains_supported: Vec<String>,
}

#[derive(Debug, Clone, Default, Deserialize)]
pub struct PaidJob {
    pub job_id: Uuid,
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub suggestions: Option<serde_json::Value>,
    /// Per-job steering overrides set by the researcher at submit
    /// time (or by the platform target seeder when the cluster
    /// hunts a featured target with no paying owner). Shape mirrors
    /// the LLM-emitted cluster payload's `config.*` so the same
    /// applier (`apply_steering_knobs_for_domain`) consumes both.
    /// `None` → fall through to the live cluster-steerer snapshot.
    #[serde(default)]
    pub seed: Option<serde_json::Value>,
    pub lake_slot_hours_remaining: f32,
    pub lease_expires_at: Option<String>,
    pub heartbeat_url: String,
    pub release_url: String,
    pub mark_proved_url: String,
    /// Slots the server allocated to this job at claim time. `None`
    /// when the row pre-dates elastic per-job sizing (server defaults
    /// to 4 in that case). The slice runner uses this for slot-hour
    /// accounting math.
    #[serde(default)]
    pub allocated_slots: Option<u32>,
}

#[derive(Debug, Clone, Serialize)]
pub struct HeartbeatBody {
    pub candidates_attempted_delta: i32,
    pub candidates_verified_delta: i32,
    pub lake_slot_hours_consumed_delta: f32,
    pub current_best_fitness: f32,
    pub current_best_chain_length: i32,
}

#[derive(Debug, Clone, Default, Deserialize)]
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
    http: WorkerHttp,
}

impl PaidJobsClient {
    pub fn new(api_url: String, worker_key: String) -> Self {
        let http = WorkerHttp::from_env(&api_url).expect("invalid NASRUDIN_API_URL");
        Self {
            api_url,
            worker_key,
            http,
        }
    }

    fn auth(&self) -> String {
        format!("Bearer {}", self.worker_key)
    }

    /// `Ok(Some(job))` on award, `Ok(None)` on 204 (queue empty or
    /// explorer floor protection). `Err` is reserved for transport /
    /// auth failures the caller should log + retry on.
    pub async fn claim(&self, body: &ClaimBody) -> Result<Option<PaidJob>> {
        let auth = self.auth();
        let headers = [("authorization", auth.as_str())];
        let body_bytes = serde_json::to_vec(body).context("serialize ClaimBody")?;
        let (status, resp_bytes) = self
            .http
            .post_bytes(
                "/api/jobs/claim",
                body_bytes.into(),
                &[
                    ("authorization", auth.as_str()),
                    ("content-type", "application/json"),
                ],
            )
            .await
            .context("POST /api/jobs/claim")?;
        let _ = headers;
        if status == 204 {
            return Ok(None);
        }
        if !(200..300).contains(&status) {
            return Err(anyhow!("claim failed: {status}"));
        }
        let parsed: PaidJob = serde_json::from_slice(&resp_bytes).context("decode PaidJob")?;
        Ok(Some(parsed))
    }

    pub async fn heartbeat(&self, id: Uuid, body: &HeartbeatBody) -> Result<HeartbeatResp> {
        let auth = self.auth();
        let headers = [("authorization", auth.as_str())];
        let (status, parsed): (u16, HeartbeatResp) = self
            .http
            .post_json(&format!("/api/jobs/{id}/heartbeat"), body, &headers)
            .await?;
        if !(200..300).contains(&status) {
            return Err(anyhow!("heartbeat failed: {status}"));
        }
        Ok(parsed)
    }

    pub async fn release(&self, id: Uuid) -> Result<()> {
        let auth = self.auth();
        let headers = [("authorization", auth.as_str())];
        let (status, _) = self
            .http
            .post_bytes(&format!("/api/jobs/{id}/release"), bytes::Bytes::new(), &headers)
            .await?;
        if !(200..300).contains(&status) {
            return Err(anyhow!("release failed: {status}"));
        }
        Ok(())
    }

    pub async fn mark_proved(&self, id: Uuid, body: &MarkProvedBody) -> Result<()> {
        let auth = self.auth();
        let headers = [("authorization", auth.as_str())];
        let (status, _): (u16, serde_json::Value) = self
            .http
            .post_json(&format!("/api/jobs/{id}/mark_proved"), body, &headers)
            .await?;
        if !(200..300).contains(&status) {
            return Err(anyhow!("mark_proved failed: {status}"));
        }
        Ok(())
    }
}
