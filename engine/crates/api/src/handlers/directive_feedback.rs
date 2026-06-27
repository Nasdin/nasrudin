//! `POST /api/directive-feedback`
//!
//! Workers POST per-cluster reward observations, batched per chunk.
//! Each entry pulls one (island, action, strength_bucket,
//! multiplier_choice) arm with the observed reward. Reward is the
//! cluster's mean-fitness delta one chunk later, affine-mapped into
//! [0, 1]. Auth reuses the worker bearer token middleware (same as
//! `/api/ingest`, `/api/cluster-report`).

use axum::{Json, extract::State, http::StatusCode};
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

        // Update the running aggregate (live UCB1 reads this).
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
            Err(err) => {
                tracing::warn!(error=%err, "directive_feedback record_pull failed");
                continue;
            }
        }

        // Append to the raw event log (replay buffer). Soft-fail on
        // error — the aggregate update already happened so the live
        // bandit isn't impaired; only offline training is.
        if let Err(err) = nasrudin_pg::query::directive_pull_events::insert_event(
            pg,
            &e.island_domain,
            &e.action,
            e.strength_bucket,
            e.multiplier_choice,
            reward,
        )
        .await
        {
            tracing::debug!(error=%err, "directive_pull_events insert failed (non-blocking)");
        }

        // LinUCB rank-1 sufficient-statistics update. Pure CPU
        // (~120 flops); runs inline. The discrete UCB1 update above
        // and this contextual update both train from the same pull,
        // so the system has *both* a per-arm point estimate AND a
        // smooth predictor across the (strength, choice) plane —
        // worker-side selection blends them via the snapshot.
        if let Ok(Some(row)) =
            nasrudin_pg::query::cluster_directive_linucb::get(pg, &e.island_domain, &e.action).await
        {
            let mut a_flat = row.a_matrix;
            let mut b_vec = row.b_vector;
            // Worker emits strength_bucket; reconstruct the
            // continuous strength as the bucket's midpoint
            // [0.0, 0.2, 0.4, 0.6, 0.8] → [0.1, 0.3, 0.5, 0.7, 0.9].
            let s_mid = (e.strength_bucket as f64 + 0.5) / 5.0;
            let max_choice = (crate::steerer::directive_bandit::MAX_MULTIPLIER_CHOICES - 1).min(8);
            let x = crate::steerer::linucb::features(s_mid, e.multiplier_choice as u8, max_choice);
            crate::steerer::linucb::update_in_place(&mut a_flat, &mut b_vec, &x, reward);
            if let Err(err) = nasrudin_pg::query::cluster_directive_linucb::save_update(
                pg,
                &e.island_domain,
                &e.action,
                a_flat,
                b_vec,
                row.pulls + 1,
            )
            .await
            {
                tracing::debug!(error=%err, "linucb save_update failed (non-blocking)");
            }
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
