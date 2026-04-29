//! Phase E research-mode HTTP client. Pairs with the worker binary's
//! `--research-mode` poll loop.
//!
//! All five endpoints are POST and authenticate with the worker's
//! `nsk_worker_…` API key. `claim` returns 204 NoContent when nothing
//! is queued; the worker can then fall back to background corpus-fill.

use anyhow::{Context, Result};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::time::Duration;
use uuid::Uuid;

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

#[derive(Debug, Clone, Deserialize)]
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
    http: Client,
}

impl ResearchClient {
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

    /// Returns `Ok(Some(job))` when a conjecture was claimed, `Ok(None)`
    /// when the queue is empty (HTTP 204), and `Err` for transport errors.
    pub async fn claim(&self) -> Result<Option<ClaimedJob>> {
        let resp = self
            .http
            .post(format!("{}/api/conjecture/claim", self.api_url))
            .bearer_auth(&self.worker_key)
            .send()
            .await
            .context("POST /api/conjecture/claim")?;
        if resp.status() == reqwest::StatusCode::NO_CONTENT {
            return Ok(None);
        }
        let resp = resp.error_for_status()?;
        Ok(Some(resp.json::<ClaimedJob>().await?))
    }

    pub async fn heartbeat(&self, id: Uuid, body: &HeartbeatBody) -> Result<()> {
        self.http
            .post(format!("{}/api/conjecture/{id}/heartbeat", self.api_url))
            .bearer_auth(&self.worker_key)
            .json(body)
            .send()
            .await?
            .error_for_status()?;
        Ok(())
    }

    pub async fn submit(&self, id: Uuid, body: &SubmitBody) -> Result<SubmitResponse> {
        let resp = self
            .http
            .post(format!("{}/api/conjecture/{id}/submit", self.api_url))
            .bearer_auth(&self.worker_key)
            .json(body)
            .send()
            .await?
            .error_for_status()?;
        Ok(resp.json::<SubmitResponse>().await?)
    }

    pub async fn complete(&self, id: Uuid, body: &CompleteBody) -> Result<()> {
        self.http
            .post(format!("{}/api/conjecture/{id}/complete", self.api_url))
            .bearer_auth(&self.worker_key)
            .json(body)
            .send()
            .await?
            .error_for_status()?;
        Ok(())
    }
}
