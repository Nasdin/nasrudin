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
