//! `GET /api/admin/steering/recent` and `POST /api/admin/steering/force`.
//!
//! `recent` is a read-only listing of cluster-steerer cycles — only
//! requires `RequireAdmin`, no audit row.
//! `force` is a manual override: persists the supplied `SteeringConfig`
//! as a cycle row and hot-reloads the ArcSwap. Wrapped in
//! `perform_audited` (`FORCE_STEERING`).

use std::sync::Arc;

use axum::{
    Json,
    extract::{ConnectInfo, State},
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
};
use serde::Deserialize;
use serde_json::json;
use std::net::SocketAddr;

use crate::admin::audit::{RequestMeta, actions, perform_audited};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

fn llm_steer_interval_seconds() -> i64 {
    std::env::var("LLM_STEER_INTERVAL_SECONDS")
        .ok()
        .and_then(|s| s.parse::<i64>().ok())
        .unwrap_or(7_200)
        .max(1)
}

fn llm_steer_budget_window_seconds(interval_seconds: i64) -> i64 {
    std::env::var("LLM_STEER_ROLLING_WINDOW_SECONDS")
        .ok()
        .and_then(|s| s.parse::<i64>().ok())
        .unwrap_or(interval_seconds)
        .max(1)
}

fn llm_steer_max_total_tokens() -> i64 {
    std::env::var("LLM_STEER_MAX_TOTAL_TOKENS")
        .ok()
        .and_then(|s| s.parse::<i64>().ok())
        .unwrap_or(10_000)
        .max(1)
}

pub async fn steering_recent(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    match nasrudin_pg::query::cluster_steering::list_recent(pg, 50).await {
        Ok(rows) => (StatusCode::OK, Json(json!({"cycles": rows}))).into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": e.to_string()})),
        )
            .into_response(),
    }
}

pub async fn steering_budget(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    let interval_seconds = llm_steer_interval_seconds();
    let rolling_window_seconds = llm_steer_budget_window_seconds(interval_seconds);
    let max_total_tokens = llm_steer_max_total_tokens();
    let cutoff = chrono::Utc::now() - chrono::Duration::seconds(rolling_window_seconds);
    let used_tokens =
        match nasrudin_pg::query::cluster_steering::llm_tokens_used_since(pg, cutoff).await {
            Ok(n) => n.max(0),
            Err(e) => {
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(json!({"error": e.to_string()})),
                )
                    .into_response();
            }
        };
    let latest_strategy =
        match nasrudin_pg::query::cluster_steering::most_recent_strategy_refresh(pg).await {
            Ok(row) => row,
            Err(e) => {
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(json!({"error": e.to_string()})),
                )
                    .into_response();
            }
        };
    let now = chrono::Utc::now();
    let seconds_until_interval_open = latest_strategy
        .as_ref()
        .map(|row| {
            let elapsed = now
                .signed_duration_since(row.started_at.with_timezone(&chrono::Utc))
                .num_seconds();
            interval_seconds.saturating_sub(elapsed).max(0)
        })
        .unwrap_or(0);
    let remaining_tokens = max_total_tokens.saturating_sub(used_tokens).max(0);

    (
        StatusCode::OK,
        Json(json!({
            "llm_steering": {
                "interval_seconds": interval_seconds,
                "rolling_window_seconds": rolling_window_seconds,
                "window_started_at": cutoff.to_rfc3339(),
                "max_total_tokens": max_total_tokens,
                "used_tokens": used_tokens,
                "remaining_tokens": remaining_tokens,
                "budget_exhausted": remaining_tokens == 0,
                "seconds_until_interval_open": seconds_until_interval_open,
                "interval_open": seconds_until_interval_open == 0,
                "skip_if_rl_confident": std::env::var("LLM_STEER_SKIP_IF_RL_CONFIDENT")
                    .map(|v| !matches!(v.trim().to_lowercase().as_str(), "0" | "false" | "no" | "off"))
                    .unwrap_or(true),
                "latest_strategy_attempt": latest_strategy.map(|row| json!({
                    "id": row.id,
                    "started_at": row.started_at.with_timezone(&chrono::Utc).to_rfc3339(),
                    "scope": row.scope,
                    "model_id": row.model_id,
                    "validation_failed": row.validation_failed,
                    "prompt_tokens": row.prompt_tokens,
                    "completion_tokens": row.completion_tokens,
                }))
            }
        })),
    )
        .into_response()
}

#[derive(Deserialize)]
pub struct ForceInput {
    #[serde(flatten)]
    pub config: crate::steerer::schema::SteeringConfig,
    pub reason: String,
}

pub async fn steering_force(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<ForceInput>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(json!({"error": "pg_unavailable"})),
            )
                .into_response();
        }
    };
    if let Err(e) = body.config.validate() {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": format!("validation: {e}")})),
        )
            .into_response();
    }
    let ua = headers
        .get(axum::http::header::USER_AGENT)
        .and_then(|v| v.to_str().ok())
        .map(str::to_string);

    let value = serde_json::to_value(&body.config).unwrap_or(serde_json::Value::Null);
    let scope = body.config.scope.clone();

    // Step 1: insert the cluster_steering row outside the audit txn —
    // its query helper is scoped to `&DatabaseConnection`. The audit
    // row in step 2 references the resulting cycle_id; in the rare
    // race where the audit insert fails after step 1 succeeds, we
    // get a steering row without an audit row (logged for follow-up).
    let row = match nasrudin_pg::query::cluster_steering::insert_new_cycle(
        pg,
        &scope,
        value.clone(),
        "admin",
        false,
        None,
        None,
    )
    .await
    {
        Ok(r) => r,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({"error": e.to_string()})),
            )
                .into_response();
        }
    };

    let cycle_id = row.id;
    let value_for_log = value.clone();
    let scope_for_log = scope.clone();
    let result: Result<(), crate::admin::audit::AuditError> = perform_audited(
        pg,
        &admin.0.user,
        None,
        RequestMeta {
            ip: Some(addr.ip()),
            user_agent: ua,
        },
        None,
        actions::FORCE_STEERING,
        body.reason,
        json!({"prev_etag_hex": format!("{:016x}", state.steering.load().etag)}),
        move |_txn| {
            Box::pin(async move {
                Ok::<_, sea_orm::DbErr>((
                    (),
                    json!({
                        "cycle_id": cycle_id,
                        "scope": scope_for_log,
                        "config": value_for_log,
                    }),
                ))
            })
        },
    )
    .await;
    if let Err(e) = result {
        tracing::error!(
            cycle_id = %cycle_id,
            error = %e,
            "FORCE_STEERING audit row insert failed AFTER cluster_steering row was committed"
        );
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": e.to_string(), "cycle_id_orphaned": cycle_id})),
        )
            .into_response();
    }

    let body_bytes = serde_json::to_vec(&body.config).unwrap_or_default();
    let etag = xxhash_rust::xxh64::xxh64(&body_bytes, 0);
    state
        .steering
        .store(Arc::new(crate::state::SteeringSnapshot {
            config: serde_json::to_value(&body.config).unwrap_or(serde_json::Value::Null),
            etag,
            started_at: row.started_at.with_timezone(&chrono::Utc),
        }));
    state.invalidate_seed_cache();

    (
        StatusCode::OK,
        Json(json!({
            "cycle_id": row.id,
            "etag": format!("{etag:016x}"),
        })),
    )
        .into_response()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn llm_budget_status_defaults_match_low_spend_profile() {
        // Environment overrides are intentionally not set here; this
        // documents the local low-spend defaults surfaced by
        // /api/admin/steering/budget.
        unsafe {
            std::env::remove_var("LLM_STEER_INTERVAL_SECONDS");
            std::env::remove_var("LLM_STEER_ROLLING_WINDOW_SECONDS");
            std::env::remove_var("LLM_STEER_MAX_TOTAL_TOKENS");
        }
        let interval = llm_steer_interval_seconds();
        assert_eq!(interval, 7_200);
        assert_eq!(llm_steer_budget_window_seconds(interval), 7_200);
        assert_eq!(llm_steer_max_total_tokens(), 10_000);
    }
}
