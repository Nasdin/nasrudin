//! Phase E research-mode HTTP client. Pairs with the worker binary's
//! `--research-mode` poll loop.
//!
//! All five endpoints are POST and authenticate with the worker's
//! `nsk_worker_…` API key. `claim` returns 204 NoContent when nothing
//! is queued; the worker can then fall back to background corpus-fill.
//!
//! Transport is `WorkerHttp` so this client works equally over TCP and
//! the unix socket trust-bypass entry point.

use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::worker_http::WorkerHttp;

#[derive(Debug, Clone, Deserialize)]
pub struct ClaimedJob {
    pub job_id: Uuid,
    pub seed: serde_json::Value,
    pub budget: serde_json::Value,
    pub hunch: String,
    pub provider: String,
    pub model: String,
    pub lease_seconds: u32,
}

#[derive(Debug, Clone, Serialize)]
pub struct HeartbeatBody {
    pub candidates_attempted: i32,
    pub candidates_verified: i32,
    pub time_elapsed_s: u32,
}

#[derive(Debug, Clone, Serialize)]
pub struct SubmitTheorem {
    pub canonical_statement: String,
    pub domain: String,
    pub lean_source: String,
    pub chain: serde_json::Value,
    pub axioms_used: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub depth: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub generation: Option<u64>,
}

#[derive(Debug, Clone, Serialize)]
pub struct SubmitBody {
    pub engine_git_sha: String,
    pub lean_version: String,
    pub theorem: SubmitTheorem,
}

#[derive(Debug, Clone, Default, Deserialize)]
pub struct SubmitResponse {
    pub theorem_id: String,
    pub canonical_hash: String,
    pub status: serde_json::Value,
}

#[derive(Debug, Clone, Serialize)]
pub struct CompleteBody {
    pub outcome: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

pub struct ResearchClient {
    pub api_url: String,
    pub worker_key: String,
    http: WorkerHttp,
}

impl ResearchClient {
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

    /// Returns `Ok(Some(job))` when a conjecture was claimed, `Ok(None)`
    /// when the queue is empty (HTTP 204), and `Err` for transport errors.
    pub async fn claim(&self) -> Result<Option<ClaimedJob>> {
        let auth = self.auth();
        let headers = [("authorization", auth.as_str())];
        let (status, body) = self
            .http
            .post_bytes("/api/conjecture/claim", bytes::Bytes::new(), &headers)
            .await
            .context("POST /api/conjecture/claim")?;
        if status == 204 {
            return Ok(None);
        }
        if !(200..300).contains(&status) {
            return Err(anyhow!("claim failed: {status}"));
        }
        let parsed: ClaimedJob =
            serde_json::from_slice(&body).context("decode ClaimedJob")?;
        Ok(Some(parsed))
    }

    pub async fn heartbeat(&self, id: Uuid, body: &HeartbeatBody) -> Result<()> {
        let auth = self.auth();
        let headers = [("authorization", auth.as_str())];
        let (status, _): (u16, serde_json::Value) = self
            .http
            .post_json(&format!("/api/conjecture/{id}/heartbeat"), body, &headers)
            .await?;
        if !(200..300).contains(&status) {
            return Err(anyhow!("heartbeat failed: {status}"));
        }
        Ok(())
    }

    pub async fn submit(&self, id: Uuid, body: &SubmitBody) -> Result<SubmitResponse> {
        let auth = self.auth();
        let headers = [("authorization", auth.as_str())];
        let (status, parsed): (u16, SubmitResponse) = self
            .http
            .post_json(&format!("/api/conjecture/{id}/submit"), body, &headers)
            .await?;
        if !(200..300).contains(&status) {
            return Err(anyhow!("submit failed: {status}"));
        }
        Ok(parsed)
    }

    pub async fn complete(&self, id: Uuid, body: &CompleteBody) -> Result<()> {
        let auth = self.auth();
        let headers = [("authorization", auth.as_str())];
        let (status, _): (u16, serde_json::Value) = self
            .http
            .post_json(&format!("/api/conjecture/{id}/complete"), body, &headers)
            .await?;
        if !(200..300).contains(&status) {
            return Err(anyhow!("complete failed: {status}"));
        }
        Ok(())
    }
}
