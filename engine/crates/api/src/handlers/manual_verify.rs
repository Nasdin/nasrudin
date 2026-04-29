//! Manual user-triggered "Verify with Lake" endpoint (P-Task 4).
//!
//! Lazy lake-promotion (P-Task 2) handles auto-promotion on
//! consumption (download, /api/seed inclusion) and via the background
//! crawler. This endpoint adds the **user-demand** path: a logged-in
//! user clicks "Verify with Lake" on a theorem detail page, which
//! enqueues at priority 0 (head of queue) and synchronously waits up
//! to `wait_seconds` for the lake-build outcome.
//!
//! Auth: cookie session OR `nsk_live_*` Bearer (the `AuthOrApiKey`
//! extractor already supports both).
//!
//! Rate limit: a separate `tower_governor` bucket is wired in main.rs
//! (10 req/hour per IP/user). The endpoint also dedups via the queue
//! itself — concurrent requests on the same theorem_id share the same
//! Notify wakeup, so only one lake build runs.
//!
//! Audit: every manual verify is recorded in the `manual_verifications`
//! table for ops + abuse detection. Schema lives in a migration in
//! engine/crates/pg/src/migrator.

use axum::{
    Json,
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
};
use serde::Deserialize;
use std::sync::Arc;
use std::time::Duration;

use crate::auth::AuthOrApiKey;
use crate::state::AppState;

#[derive(Deserialize, Default)]
pub struct VerifyBody {
    /// Synchronous wait timeout. `0` = enqueue and return 202 immediately.
    /// Default 30s. Capped at 120s.
    #[serde(default)]
    pub wait_seconds: Option<u64>,
}

/// `POST /api/theorems/{id}/verify` — force lake-promotion of a
/// specific theorem. Auth-gated (any logged-in user or live api-key).
///
/// Outcomes:
/// - 200 + `{ "status": "lake_verified", ... }` — already LakeVerified or just promoted
/// - 410 + `{ "status": "rejected", "reason": "..." }` — lake build failed (cascade ran)
/// - 202 + `Retry-After: 60` — synchronous wait timed out, promotion in flight
/// - 404 — unknown theorem id
/// - 503 — `pg_unavailable` or `lake_promotion_unavailable`
pub async fn verify(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Path(id_hex): Path<String>,
    Json(body): Json<VerifyBody>,
) -> impl IntoResponse {
    // Auth: any logged-in user / live key. We log who triggered it
    // for audit.
    let actor_id = auth.user.id.to_string();

    // Parse 16-char hex theorem id.
    let id_bytes = match hex::decode(&id_hex) {
        Ok(b) if b.len() == 8 => {
            let mut a = [0u8; 8];
            a.copy_from_slice(&b);
            a
        }
        _ => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": "bad_theorem_id" })),
            )
                .into_response();
        }
    };

    // Look up the theorem first — 404 if unknown.
    let theorem = match state.db.get_theorem(&id_bytes).ok().flatten() {
        Some(t) => t,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({ "error": "theorem_not_found" })),
            )
                .into_response();
        }
    };

    // Already LakeVerified? Audit + 200 no-op.
    if let nasrudin_core::VerificationStatus::Verified { tactic_used, .. } = &theorem.verified {
        if tactic_used == "lake_build" {
            log_manual_verify(&state, &actor_id, &id_bytes, "already_lake_verified", 0).await;
            return (
                StatusCode::OK,
                Json(serde_json::json!({
                    "status": "lake_verified",
                    "theorem_id": id_hex,
                    "note": "already kernel-verified; no-op"
                })),
            )
                .into_response();
        }
    }
    if let nasrudin_core::VerificationStatus::Rejected { reason } = &theorem.verified {
        log_manual_verify(&state, &actor_id, &id_bytes, "already_rejected", 0).await;
        return (
            StatusCode::GONE,
            Json(serde_json::json!({
                "status": "rejected",
                "theorem_id": id_hex,
                "reason": reason,
            })),
        )
            .into_response();
    }

    // Need a promotion drain to act on. If unwired (no PG), 503.
    let promotion = match state.lake_promotion.as_ref() {
        Some(p) => p.clone(),
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({ "error": "lake_promotion_unavailable" })),
            )
                .into_response();
        }
    };

    let wait = body
        .wait_seconds
        .unwrap_or(30)
        .min(120);
    let started_at = std::time::Instant::now();
    let outcome = promotion
        .await_promotion(id_bytes, Duration::from_secs(wait))
        .await
        .ok()
        .flatten();
    let duration_ms = started_at.elapsed().as_millis() as u32;

    match outcome {
        Some(nasrudin_core::VerificationStatus::Verified { tactic_used, .. })
            if tactic_used == "lake_build" =>
        {
            log_manual_verify(&state, &actor_id, &id_bytes, "lake_verified", duration_ms).await;
            (
                StatusCode::OK,
                Json(serde_json::json!({
                    "status": "lake_verified",
                    "theorem_id": id_hex,
                    "duration_ms": duration_ms,
                })),
            )
                .into_response()
        }
        Some(nasrudin_core::VerificationStatus::Rejected { reason }) => {
            log_manual_verify(&state, &actor_id, &id_bytes, "rejected", duration_ms).await;
            (
                StatusCode::GONE,
                Json(serde_json::json!({
                    "status": "rejected",
                    "theorem_id": id_hex,
                    "reason": reason,
                    "duration_ms": duration_ms,
                })),
            )
                .into_response()
        }
        _ => {
            log_manual_verify(&state, &actor_id, &id_bytes, "in_flight_timeout", duration_ms).await;
            (
                StatusCode::ACCEPTED,
                [(axum::http::header::RETRY_AFTER, "60".to_string())],
                Json(serde_json::json!({
                    "status": "in_flight",
                    "theorem_id": id_hex,
                    "note": "still building; poll /api/theorems/{id}/verify-status",
                })),
            )
                .into_response()
        }
    }
}

/// `GET /api/theorems/{id}/verify-status` — return current
/// verification state + lake-promotion queue depth. Used by the
/// frontend to poll while a manual verify is in flight (alternative
/// to subscribing to `/api/events/discoveries` SSE).
pub async fn verify_status(
    State(state): State<Arc<AppState>>,
    Path(id_hex): Path<String>,
) -> impl IntoResponse {
    let id_bytes = match hex::decode(&id_hex) {
        Ok(b) if b.len() == 8 => {
            let mut a = [0u8; 8];
            a.copy_from_slice(&b);
            a
        }
        _ => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": "bad_theorem_id" })),
            )
                .into_response();
        }
    };
    let theorem = match state.db.get_theorem(&id_bytes).ok().flatten() {
        Some(t) => t,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({ "error": "theorem_not_found" })),
            )
                .into_response();
        }
    };
    let (status_str, tactic) = match &theorem.verified {
        nasrudin_core::VerificationStatus::Pending => ("pending".to_string(), None),
        nasrudin_core::VerificationStatus::Verified { tactic_used, .. } => {
            let s = if tactic_used == "lake_build" {
                "lake_verified"
            } else {
                "chain_verified"
            };
            (s.to_string(), Some(tactic_used.clone()))
        }
        nasrudin_core::VerificationStatus::Rejected { reason } => {
            return (
                StatusCode::OK,
                Json(serde_json::json!({
                    "status": "rejected",
                    "reason": reason,
                })),
            )
                .into_response();
        }
        nasrudin_core::VerificationStatus::Timeout => ("timeout".to_string(), None),
    };
    let queue_depth = state.db.lake_promotion_queue_depth().unwrap_or(0);
    (
        StatusCode::OK,
        Json(serde_json::json!({
            "status": status_str,
            "tactic_used": tactic,
            "lake_promotion_queue_depth": queue_depth,
        })),
    )
        .into_response()
}

/// Best-effort audit logging into the `manual_verifications` PG table.
/// Failures are non-fatal (log + continue) — the user shouldn't see
/// 500s for a bookkeeping write.
async fn log_manual_verify(
    state: &AppState,
    actor_id: &str,
    theorem_id: &[u8; 8],
    result: &str,
    duration_ms: u32,
) {
    let Some(pg) = &state.pg else {
        return;
    };
    use sea_orm::{ConnectionTrait, Statement};
    let stmt = Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "INSERT INTO manual_verifications \
         (actor_id, theorem_id, requested_at, result, duration_ms) \
         VALUES ($1, $2, NOW(), $3, $4)",
        vec![
            actor_id.into(),
            theorem_id.to_vec().into(),
            result.into(),
            (duration_ms as i32).into(),
        ],
    );
    if let Err(e) = pg.execute_raw(stmt).await {
        tracing::warn!(
            actor = %actor_id,
            theorem = %hex::encode(theorem_id),
            "manual_verify audit insert failed: {e}"
        );
    }
}
