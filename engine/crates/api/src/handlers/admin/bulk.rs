//! `POST /api/admin/users/bulk` — start a bulk run; returns `run_id`.
//! `GET /api/admin/users/bulk/{run_id}/stream` — SSE progress stream.

use std::convert::Infallible;
use std::sync::Arc;

use axum::{
    Json,
    extract::{Path, State},
    http::StatusCode,
    response::{
        IntoResponse,
        sse::{Event, KeepAlive, Sse},
    },
};
use futures::stream::Stream;
use serde::Deserialize;
use serde_json::json;
use uuid::Uuid;

use crate::admin::bulk_runner::{spawn_run, BulkAction};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct StartInput {
    #[serde(flatten)]
    pub action: BulkAction,
    pub user_ids: Vec<Uuid>,
    pub reason: String,
}

pub async fn start(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Json(body): Json<StartInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    if body.reason.trim().chars().count() < 10 {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "reason_too_short"})),
        )
            .into_response();
    }
    if body.user_ids.is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "user_ids_empty"})),
        )
            .into_response();
    }

    let action_label = match &body.action {
        BulkAction::SetTrust { .. } => "set_trust",
        BulkAction::SetPlan { .. } => "set_plan",
        BulkAction::AdjustCredits { .. } => "adjust_credits",
        BulkAction::SetSpotCheckRate { .. } => "set_spot_check_rate",
    };
    let run_id = match nasrudin_pg::query::bulk_runs::insert(
        pg,
        admin.0.user.id,
        action_label,
        serde_json::to_value(&body.action).unwrap_or(serde_json::Value::Null),
        body.user_ids.len() as i32,
    )
    .await
    {
        Ok(id) => id,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({"error": e.to_string()})),
            )
                .into_response();
        }
    };
    spawn_run(
        state.clone(),
        run_id,
        admin.0.user.clone(),
        body.action,
        body.user_ids,
        body.reason,
    );
    (StatusCode::OK, Json(json!({"run_id": run_id}))).into_response()
}

pub async fn stream(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(run_id): Path<Uuid>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let mut rx = state.bulk_run_progress_tx.subscribe();
    let pg = state.pg.clone();
    let s = async_stream::stream! {
        // Initial snapshot so the UI gets the current state immediately
        // even if the run is already complete by the time it subscribes.
        if let Some(pg) = &pg
            && let Ok(Some(row)) = nasrudin_pg::query::bulk_runs::find_by_id(pg, run_id).await
        {
            yield Ok(Event::default().event("snapshot").json_data(json!({
                "completed": row.completed_count,
                "failed": row.failed_count,
                "total": row.total_count,
                "status": row.status,
            })).unwrap());
            if row.status != "running" {
                // Already terminal — no progress events incoming.
                return;
            }
        }
        loop {
            match rx.recv().await {
                Ok((rid, p)) if rid == run_id => {
                    let payload = json!({
                        "completed": p.completed,
                        "failed": p.failed,
                        "last_user_id": p.last_user_id,
                        "status": p.status,
                    });
                    yield Ok(Event::default().event("progress").json_data(payload).unwrap());
                    if p.status != "running" {
                        break;
                    }
                }
                Ok(_) => continue,
                Err(_) => break,
            }
        }
    };
    Sse::new(s).keep_alive(KeepAlive::default())
}
