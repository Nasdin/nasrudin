//! `POST /api/compute-feedback`
//!
//! Workers POST per-(island, strength_bucket, multiplier_choice)
//! reward observations for the compute-scaling bandit. Same shape
//! as `/api/directive-feedback` minus the `action` field —
//! compute is a single global knob, not per-action.

use axum::{Json, extract::State, http::StatusCode};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::state::AppState;

#[derive(Debug, Deserialize)]
pub struct ComputeFeedbackBody {
    pub feedback: Vec<ComputeFeedbackEntry>,
}

#[derive(Debug, Deserialize)]
pub struct ComputeFeedbackEntry {
    pub island_domain: String,
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
    Json(body): Json<ComputeFeedbackBody>,
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
        if !(0..5).contains(&e.strength_bucket) || !(0..5).contains(&e.multiplier_choice) {
            tracing::warn!(
                strength_bucket = e.strength_bucket,
                multiplier_choice = e.multiplier_choice,
                "rejected compute feedback entry: bucket/choice out of range"
            );
            continue;
        }
        let reward = e.reward.clamp(0.0, 1.0);
        match nasrudin_pg::query::cluster_compute_arms::record_pull(
            pg,
            &e.island_domain,
            e.strength_bucket,
            e.multiplier_choice,
            reward,
        )
        .await
        {
            Ok(_) => applied += 1,
            Err(err) => tracing::warn!(error=%err, "compute_feedback record_pull failed"),
        }

        // LinUCB rank-1 update (per-island compute bandit).
        if let Ok(Some(row)) =
            nasrudin_pg::query::cluster_compute_linucb::get(pg, &e.island_domain).await
        {
            let mut a_flat = row.a_matrix;
            let mut b_vec = row.b_vector;
            let s_mid = (e.strength_bucket as f64 + 0.5) / 5.0;
            let max_choice = std::cmp::min(
                crate::steerer::directive_bandit::MAX_MULTIPLIER_CHOICES - 1,
                8,
            );
            let x = crate::steerer::linucb::features(s_mid, e.multiplier_choice as u8, max_choice);
            crate::steerer::linucb::update_in_place(&mut a_flat, &mut b_vec, &x, reward);
            if let Err(err) = nasrudin_pg::query::cluster_compute_linucb::save_update(
                pg,
                &e.island_domain,
                a_flat,
                b_vec,
                row.pulls + 1,
            )
            .await
            {
                tracing::debug!(error=%err,
                    "compute linucb save_update failed (non-blocking)");
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
