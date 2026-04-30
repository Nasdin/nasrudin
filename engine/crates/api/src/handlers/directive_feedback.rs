//! `POST /api/directive-feedback`
//!
//! Workers POST per-cluster reward observations, batched per chunk.
//! Each entry pulls one (island, action, strength_bucket,
//! multiplier_choice) arm with the observed reward. Reward is the
//! cluster's mean-fitness delta one chunk later, affine-mapped into
//! [0, 1]. Auth reuses the worker bearer token middleware (same as
//! `/api/ingest`, `/api/cluster-report`).

use axum::{extract::State, http::StatusCode, Json};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::state::AppState;

#[derive(Debug, Deserialize)]
pub struct DirectiveFeedbackBody {
    pub feedback: Vec<DirectiveFeedbackEntry>,
}

#[derive(Debug, Deserialize)]
pub struct DirectiveFeedbackEntry {
    pub island_domain: String,
    pub action: String,
    pub strength_bucket: i16,
    pub multiplier_choice: i16,
    pub reward: f64,
}

#[derive(Debug, Serialize)]
pub struct Resp {
    pub received: bool,
    pub applied: u32,
}

pub async fn handler(
    State(state): State<Arc<AppState>>,
    Json(body): Json<DirectiveFeedbackBody>,
) -> (StatusCode, Json<Resp>) {
    let Some(pg) = state.pg.as_ref() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(Resp {
                received: false,
                applied: 0,
            }),
        );
    };
    let mut applied = 0u32;
    for e in body.feedback {
        // Hard-validate action + buckets so a malformed body can't
        // poison an arbitrary row.
        if !matches!(
            e.action.as_str(),
            "boost" | "exploit" | "diversify" | "kill"
        ) {
            tracing::warn!(action = %e.action, "rejected feedback entry: bad action");
            continue;
        }
        if !(0..5).contains(&e.strength_bucket) || !(0..5).contains(&e.multiplier_choice) {
            tracing::warn!(
                strength_bucket = e.strength_bucket,
                multiplier_choice = e.multiplier_choice,
                "rejected feedback entry: bucket/choice out of range"
            );
            continue;
        }
        // Defensive clamp — the bandit math assumes bounded rewards.
        let reward = e.reward.clamp(0.0, 1.0);
        match nasrudin_pg::query::cluster_directive_arms::record_pull(
            pg,
            &e.island_domain,
            &e.action,
            e.strength_bucket,
            e.multiplier_choice,
            reward,
        )
        .await
        {
            Ok(_) => applied += 1,
            Err(err) => tracing::warn!(error=%err, "directive_feedback record_pull failed"),
        }
    }
    (
        StatusCode::OK,
        Json(Resp {
            received: true,
            applied,
        }),
    )
}
