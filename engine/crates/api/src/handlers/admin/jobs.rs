//! `POST /api/admin/jobs/{id}/cancel` — admin force-cancels a paid
//! conjecture job. Best-effort: if the job is already terminal the
//! handler returns 200 with `no_op=true`. When `refund=true` and the
//! job was paid, one research credit is refunded to the owner.

use std::net::SocketAddr;
use std::sync::Arc;

use axum::{
    Json,
    extract::{ConnectInfo, Path, State},
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
};
use serde::Deserialize;
use serde_json::json;
use uuid::Uuid;

use crate::admin::audit::{RequestMeta, actions, perform_audited};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct CancelInput {
    pub reason: String,
    #[serde(default)]
    pub refund: bool,
}

pub async fn cancel(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<CancelInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let req_meta = RequestMeta {
        ip: Some(addr.ip()),
        user_agent: headers
            .get(axum::http::header::USER_AGENT)
            .and_then(|v| v.to_str().ok())
            .map(str::to_string),
    };
    let refund = body.refund;
    let result = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta,
        None,
        actions::CANCEL_JOB,
        body.reason,
        json!({"job_id": id, "refund_requested": refund}),
        move |txn| {
            Box::pin(async move {
                // Cancel + return user_id + previous status. Raw SQL because the
                // existing conjecture_jobs query helpers are scoped to the
                // worker-claim flow. RETURNING NULL when missing/terminal —
                // handler reports `no_op=true`.
                #[derive(Debug, sea_orm::FromQueryResult)]
                struct Row {
                    user_id: Uuid,
                    state: String,
                }
                let stmt = sea_orm::Statement::from_sql_and_values(
                    sea_orm::DatabaseBackend::Postgres,
                    "UPDATE conjecture_jobs SET state='cancelled', completed_at=now()
                     WHERE id=$1 AND state IN ('queued', 'claimed', 'Running', 'running')
                     RETURNING user_id, state",
                    [id.into()],
                );
                let row = <Row as sea_orm::FromQueryResult>::find_by_statement(stmt)
                    .one(txn)
                    .await?;
                let after = match row {
                    Some(r) => {
                        if refund {
                            nasrudin_pg::query::admin_users::adjust_credits(txn, r.user_id, 1)
                                .await
                                .ok();
                        }
                        json!({
                            "job_id": id,
                            "user_id": r.user_id,
                            "previous_state": r.state,
                            "refunded": refund,
                        })
                    }
                    None => json!({"job_id": id, "no_op": true}),
                };
                Ok::<_, sea_orm::DbErr>(((), after))
            })
        },
    )
    .await;
    match result {
        Ok(()) => (StatusCode::OK, Json(json!({"ok": true}))).into_response(),
        Err(crate::admin::audit::AuditError::ReasonTooShort) => (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "reason_too_short"})),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": e.to_string()})),
        )
            .into_response(),
    }
}
