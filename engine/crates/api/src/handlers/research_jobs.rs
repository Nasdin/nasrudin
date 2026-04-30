//! User-facing paid Researcher endpoints + the per-job SSE bus.
//!
//!   POST   /api/research/jobs              create job (decrements credits)
//!   GET    /api/research/jobs              list user's jobs
//!   GET    /api/research/jobs/{id}         detail
//!   GET    /api/research/jobs/{id}/events  SSE progress stream
//!   POST   /api/research/jobs/{id}/cancel  cancel + maybe-refund
//!
//! `emit_job_event` is the shared helper called from `jobs_claim.rs`
//! (heartbeat / claim / release / mark_proved) and from the user-side
//! cancel handler so SSE subscribers see the full lifecycle.

use std::convert::Infallible;
use std::sync::Arc;

use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::sse::{Event, KeepAlive, Sse},
    response::IntoResponse,
    Json,
};
use futures::Stream;
use serde::Deserialize;
use tokio_stream::wrappers::BroadcastStream;
use tokio_stream::StreamExt;
use uuid::Uuid;

use crate::auth::AuthOrApiKey;
use crate::jobs::JobEvent;
use crate::state::AppState;

/// Send a JobEvent on the per-job broadcast channel, lazily creating
/// it the first time anyone subscribes or emits. No-op on send error
/// (broadcast channels return Err when there are no receivers — the
/// user simply hasn't opened the SSE yet).
pub fn emit_job_event(state: &AppState, job_id: Uuid, ev: JobEvent) {
    let entry = state.job_events.entry(job_id).or_insert_with(|| {
        tokio::sync::broadcast::channel(64).0
    });
    let _ = entry.value().send(ev);
}

#[derive(Deserialize)]
pub struct CreateBody {
    pub hunch: String,
    #[serde(default)]
    pub domain_hint: Option<String>,
}

/// `POST /api/research/jobs` — atomically decrement the user's
/// `research_credits` and queue a paid conjecture.
pub async fn create(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Json(body): Json<CreateBody>,
) -> impl IntoResponse {
    if body.hunch.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "hunch_required" })),
        )
            .into_response();
    }
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    let user_id = auth.user.id;

    // Atomic credit-decrement-or-no-op.
    let decremented = nasrudin_pg::query::users::try_decrement_research_credits(pg, user_id)
        .await
        .unwrap_or(false);
    if !decremented {
        return (
            StatusCode::PAYMENT_REQUIRED,
            Json(serde_json::json!({ "error": "no_research_credits" })),
        )
            .into_response();
    }

    // Insert the job in `queued` state with the default 96 lake-slot-
    // hour quota.
    use nasrudin_pg::sea_orm::*;
    let id = Uuid::new_v4();
    let am = nasrudin_pg::entity::conjecture_jobs::ActiveModel {
        id: Set(id),
        owner_id: Set(user_id),
        state: Set("queued".into()),
        outcome: Set(None),
        hunch: Set(body.hunch),
        domain_hint: Set(body.domain_hint),
        provider: Set("internal".into()),
        model: Set("ga".into()),
        suggestions: Set(None),
        chosen_index: Set(None),
        seed: Set(None),
        budget: Set(serde_json::json!({
            "wall_seconds": 86400,
            "max_candidates": 10_000_000,
        })),
        claimed_by: Set(None),
        claimed_at: Set(None),
        lease_expires_at: Set(None),
        last_heartbeat_at: Set(None),
        candidates_attempted: Set(0),
        candidates_verified: Set(0),
        verified_theorem_ids: Set(None),
        created_at: Set(chrono::Utc::now().into()),
        completed_at: Set(None),
        paper_draft: Set(None),
        lake_slot_hours_quota: Set(96),
        lake_slot_hours_consumed: Set(0.0),
        slice_priority: Set(5),
        tier: Set("researcher".into()),
        // Default 4 — `atomic_claim_paid` overwrites this with the
        // claiming worker's reported available_lake_slots.
        allocated_slots: Set(4),
    };
    if let Err(e) = am.insert(pg).await {
        // Refund the credit we just took so the user isn't charged
        // for a phantom row.
        let _ = nasrudin_pg::query::users::refund_research_credit(pg, user_id).await;
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response();
    }

    (
        StatusCode::CREATED,
        Json(serde_json::json!({ "job_id": id, "state": "queued" })),
    )
        .into_response()
}

/// `GET /api/research/jobs` — newest-first list of the user's jobs.
pub async fn list(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    use nasrudin_pg::sea_orm::*;
    let rows = nasrudin_pg::entity::conjecture_jobs::Entity::find()
        .filter(nasrudin_pg::entity::conjecture_jobs::Column::OwnerId.eq(auth.user.id))
        .filter(nasrudin_pg::entity::conjecture_jobs::Column::Tier.eq("researcher"))
        .order_by_desc(nasrudin_pg::entity::conjecture_jobs::Column::CreatedAt)
        .limit(200)
        .all(pg)
        .await
        .unwrap_or_default();
    (StatusCode::OK, Json(serde_json::json!({ "jobs": rows }))).into_response()
}

/// `GET /api/research/jobs/{id}` — detail. 404 on miss, 403 on
/// non-owner.
pub async fn detail(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) if j.owner_id == auth.user.id => {
            (StatusCode::OK, Json(j)).into_response()
        }
        Ok(Some(_)) => (StatusCode::FORBIDDEN, "not_owner").into_response(),
        Ok(None) => (StatusCode::NOT_FOUND, "not_found").into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

/// `GET /api/research/jobs/{id}/events` — SSE stream of JobEvents
/// scoped to a single job. The user must own the job.
pub async fn events(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Path(id): Path<Uuid>,
) -> Result<Sse<impl Stream<Item = Result<Event, Infallible>>>, StatusCode> {
    let pg = state.pg.as_ref().ok_or(StatusCode::SERVICE_UNAVAILABLE)?;
    let job = nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        .ok_or(StatusCode::NOT_FOUND)?;
    if job.owner_id != auth.user.id {
        return Err(StatusCode::FORBIDDEN);
    }
    let entry = state.job_events.entry(id).or_insert_with(|| {
        tokio::sync::broadcast::channel(64).0
    });
    let rx = entry.value().subscribe();
    let stream = BroadcastStream::new(rx).filter_map(|r| {
        let ev = r.ok()?;
        let json = serde_json::to_string(&ev).unwrap_or_else(|_| "{}".into());
        Some(Ok(Event::default().data(json)))
    });
    Ok(Sse::new(stream).keep_alive(KeepAlive::default()))
}

/// `POST /api/research/jobs/{id}/cancel` — terminal-ish. Refund rule:
/// full refund only if the run had zero verified results AND fewer
/// than 1000 candidates attempted. Anything past those thresholds is
/// "value delivered" and the credit stays consumed.
pub async fn cancel(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    let job = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) if j.owner_id == auth.user.id => j,
        // (cancel handler — owner-only path)
        Ok(Some(_)) => return (StatusCode::FORBIDDEN, "not_owner").into_response(),
        Ok(None) => return (StatusCode::NOT_FOUND, "not_found").into_response(),
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };
    if matches!(
        job.state.as_str(),
        "proved" | "budget_exhausted" | "cancelled" | "Complete"
    ) {
        return (StatusCode::CONFLICT, "terminal_state").into_response();
    }

    let was_in_flight = matches!(job.state.as_str(), "claimed" | "running" | "Running");
    // Release the actual slot count this job had committed, not a
    // fixed 4. `allocated_slots` is set at claim time from the
    // worker's reported available_lake_slots.
    let allocated_slots = (job.allocated_slots as u32).max(1);
    let _ = nasrudin_pg::query::conjecture_jobs::release_paid_claim(
        pg,
        id,
        None, // bypass worker check; cancel is owner-driven
        "cancelled",
    )
    .await;
    if was_in_flight {
        state.capacity.release_paid_slots(allocated_slots);
    }

    let refund_eligible =
        job.candidates_verified == 0 && job.candidates_attempted < 1000;
    if refund_eligible {
        let _ = nasrudin_pg::query::users::refund_research_credit(pg, auth.user.id).await;
    }

    emit_job_event(&state, id, JobEvent::Cancelled);
    (
        StatusCode::OK,
        Json(serde_json::json!({
            "cancelled": true,
            "refunded": refund_eligible,
        })),
    )
        .into_response()
}
