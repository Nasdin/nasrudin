//! Worker-side endpoints for paid Researcher jobs:
//!
//!   POST /api/jobs/claim        — atomic dequeue with 5-min lease
//!   POST /api/jobs/{id}/heartbeat — extend lease, debit slot-hours
//!   POST /api/jobs/{id}/release    — voluntarily abandon a claim
//!   POST /api/jobs/{id}/mark_proved — flag a verified-theorem hit
//!
//! All require a valid worker bearer token (`WorkerAuth`). The claim
//! path also reports the worker's current `available_lake_slots` to
//! the cluster `CapacityTracker` so the explorer-floor calculation
//! has a fresh denominator.

use std::sync::Arc;

use axum::{
    Json,
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
};
use serde::Deserialize;
use uuid::Uuid;

use crate::auth::WorkerAuth;
use crate::jobs::JobEvent;
use crate::state::AppState;

/// Floor on the slot footprint reserved for any paid job; the actual
/// committed amount is `body.available_lake_slots` (clamped to
/// [MIN_SLOTS_PER_JOB, MAX_SLOTS_PER_JOB]) and stamped onto
/// `conjecture_jobs.allocated_slots` at claim time. The
/// floor-satisfaction check + capacity counters use the committed
/// number, so a small worker grabs a job at minimum-1 slots and a
/// big worker grabs at its real capacity.
const MIN_SLOTS_PER_JOB: u32 = 1;
/// Hard cap to defeat workers reporting absurd slot counts.
const MAX_SLOTS_PER_JOB: u32 = 64;
/// Backwards-compat for any code still naming the legacy fixed
/// constant. Reads as the historical default for out-of-band paths
/// (release / mark_proved) where the row's allocated_slots is more
/// authoritative anyway.
const SLOTS_PER_JOB: u32 = 4;

#[derive(Deserialize)]
pub struct ClaimBody {
    /// Worker's currently-available lake slot count. Sent on every
    /// poll so the capacity tracker's window is fresh.
    pub available_lake_slots: u32,
    /// Domains the worker is willing to claim for. `["all"]` =
    /// no preference. Currently advisory; future tiering may use it
    /// for affinity routing.
    #[serde(default)]
    pub domains_supported: Vec<String>,
}

/// `POST /api/jobs/claim` — atomic dequeue with 5-min lease.
pub async fn claim(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Json(body): Json<ClaimBody>,
) -> impl IntoResponse {
    let worker_id = auth.0.worker_handle.clone();
    state
        .capacity
        .report_worker(&worker_id, body.available_lake_slots);

    // Slots we'd commit to this claim. Clamp to the [MIN, MAX] range
    // so a worker can't lie its way into a 0-slot or 1000-slot
    // allocation. The committed number flows through to the floor
    // check, the in-process counter, and the row's allocated_slots.
    let committed_slots: u32 = body
        .available_lake_slots
        .clamp(MIN_SLOTS_PER_JOB, MAX_SLOTS_PER_JOB);

    // Explorer-floor check: do not award if doing so would push the
    // cluster's free explorer slots below the 10% / min-2 floor.
    let total = state.capacity.total_lake_slots();
    let already_paid = state.capacity.paid_slots();
    if !crate::jobs::quota::floor_satisfied(total, already_paid + committed_slots) {
        return (StatusCode::NO_CONTENT, "explorer_floor_protected").into_response();
    }

    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response();
        }
    };

    match nasrudin_pg::query::conjecture_jobs::atomic_claim_paid(
        pg,
        &worker_id,
        committed_slots as i32,
    )
    .await
    {
        Ok(Some(job)) => {
            state.capacity.add_paid_slots(committed_slots);
            let remaining = crate::jobs::quota::quota_remaining_hours(
                job.lake_slot_hours_quota,
                job.lake_slot_hours_consumed,
            );
            crate::handlers::research_jobs::emit_job_event(
                &state,
                job.id,
                JobEvent::JobState {
                    state: "claimed".into(),
                },
            );
            (
                StatusCode::OK,
                Json(serde_json::json!({
                    "job_id": job.id,
                    "hunch": job.hunch,
                    "domain_hint": job.domain_hint,
                    "suggestions": job.suggestions,
                    "seed": job.seed,
                    "lake_slot_hours_remaining": remaining,
                    "lease_expires_at": job.lease_expires_at,
                    "allocated_slots": job.allocated_slots,
                    "heartbeat_url": format!("/api/jobs/{}/heartbeat", job.id),
                    "release_url": format!("/api/jobs/{}/release", job.id),
                    "mark_proved_url": format!("/api/jobs/{}/mark_proved", job.id),
                })),
            )
                .into_response()
        }
        Ok(None) => (StatusCode::NO_CONTENT, "no_paid_jobs_queued").into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

#[derive(Deserialize)]
pub struct HeartbeatBody {
    pub candidates_attempted_delta: i32,
    pub candidates_verified_delta: i32,
    pub lake_slot_hours_consumed_delta: f32,
    #[serde(default)]
    pub current_best_fitness: f32,
    #[serde(default)]
    pub current_best_chain_length: i32,
}

/// `POST /api/jobs/{id}/heartbeat`
pub async fn heartbeat(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
    Json(body): Json<HeartbeatBody>,
) -> impl IntoResponse {
    let worker_id = auth.0.worker_handle.clone();
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };

    // Resolve allocated_slots once so we know how many to release on
    // budget exhaustion (the heartbeat helper reads it internally for
    // the sanity-cap math; we duplicate the lookup here so the
    // capacity counter stays in sync).
    let allocated_slots: u32 = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) => (j.allocated_slots as u32).max(MIN_SLOTS_PER_JOB),
        _ => SLOTS_PER_JOB,
    };
    match nasrudin_pg::query::conjecture_jobs::heartbeat_paid(
        pg,
        id,
        &worker_id,
        body.candidates_attempted_delta,
        body.candidates_verified_delta,
        body.lake_slot_hours_consumed_delta,
    )
    .await
    {
        Ok(Some((new_consumed, exhausted))) => {
            crate::handlers::research_jobs::emit_job_event(
                &state,
                id,
                JobEvent::Progress {
                    candidates_attempted: body.candidates_attempted_delta,
                    candidates_verified: body.candidates_verified_delta,
                    best_fitness: body.current_best_fitness,
                    best_chain_length: body.current_best_chain_length,
                    lake_slot_hours_consumed: new_consumed,
                },
            );
            if exhausted {
                let _ = nasrudin_pg::query::conjecture_jobs::release_paid_claim(
                    pg,
                    id,
                    Some(&worker_id),
                    "budget_exhausted",
                )
                .await;
                state.capacity.release_paid_slots(allocated_slots);
                crate::handlers::research_jobs::emit_job_event(
                    &state,
                    id,
                    JobEvent::BudgetExhausted {
                        best_partial_summary: format!(
                            "fitness={:.3} chain={}",
                            body.current_best_fitness, body.current_best_chain_length
                        ),
                        // Refund rule: zero verified during the entire
                        // run AND the worker reported <1000 candidates
                        // attempted. We don't know the cumulative count
                        // here without a re-fetch; SSE consumers reading
                        // this just see the partial summary, the cancel
                        // path issues the actual refund.
                        refund_credits: 0,
                    },
                );
                return Json(serde_json::json!({
                    "continue": false,
                    "reason": "budget_exhausted",
                    "lake_slot_hours_consumed": new_consumed,
                }))
                .into_response();
            }
            Json(serde_json::json!({
                "continue": true,
                "lake_slot_hours_consumed": new_consumed,
            }))
            .into_response()
        }
        Ok(None) => (
            StatusCode::FORBIDDEN,
            Json(serde_json::json!({ "error": "lease_lost" })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

/// `POST /api/jobs/{id}/release` — worker abandons the claim
/// without solving (network drop, shutdown, etc.). Job goes back to
/// `queued` so another worker can pick it up.
pub async fn release(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let worker_id = auth.0.worker_handle.clone();
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    let allocated_slots: u32 = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) => (j.allocated_slots as u32).max(MIN_SLOTS_PER_JOB),
        _ => SLOTS_PER_JOB,
    };
    match nasrudin_pg::query::conjecture_jobs::release_paid_claim(
        pg,
        id,
        Some(&worker_id),
        "queued",
    )
    .await
    {
        Ok(0) => (StatusCode::FORBIDDEN, "not_your_lease").into_response(),
        Ok(_) => {
            state.capacity.release_paid_slots(allocated_slots);
            crate::handlers::research_jobs::emit_job_event(
                &state,
                id,
                JobEvent::JobState {
                    state: "queued".into(),
                },
            );
            StatusCode::OK.into_response()
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

#[derive(Deserialize)]
pub struct MarkProvedBody {
    pub theorem_id_hex: String,
    #[serde(default)]
    pub statement_latex: Option<String>,
}

/// `POST /api/jobs/{id}/mark_proved` — worker reports a verified
/// theorem whose canonical matches the conjecture target.
pub async fn mark_proved(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
    Json(body): Json<MarkProvedBody>,
) -> impl IntoResponse {
    let worker_id = auth.0.worker_handle.clone();
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    let allocated_slots: u32 = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) => (j.allocated_slots as u32).max(MIN_SLOTS_PER_JOB),
        _ => SLOTS_PER_JOB,
    };
    match nasrudin_pg::query::conjecture_jobs::mark_paid_proved(
        pg,
        id,
        &worker_id,
        &body.theorem_id_hex,
    )
    .await
    {
        Ok(0) => (StatusCode::FORBIDDEN, "not_your_lease").into_response(),
        Ok(_) => {
            state.capacity.release_paid_slots(allocated_slots);
            crate::handlers::research_jobs::emit_job_event(
                &state,
                id,
                JobEvent::TheoremVerified {
                    theorem_id_hex: body.theorem_id_hex.clone(),
                    statement_latex: body.statement_latex.unwrap_or_default(),
                },
            );
            crate::handlers::research_jobs::emit_job_event(
                &state,
                id,
                JobEvent::Proved {
                    lean_url: format!("/api/theorems/{}/lean", body.theorem_id_hex),
                },
            );
            StatusCode::OK.into_response()
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}
