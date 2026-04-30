//! `GET /api/admin/stats` — aggregate dashboard stats.
//!
//! Cheap read: ~5 small queries in `tokio::join!`. No cache layer for
//! now — the handler returns in <50 ms even on a busy system, and the
//! dashboard polls at 15 s intervals.

use std::sync::Arc;

use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use serde_json::json;

use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

pub async fn stats(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
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

    let users_total_fut = async {
        use sea_orm::{EntityTrait, PaginatorTrait};
        nasrudin_pg::entity::users::Entity::find()
            .count(pg)
            .await
            .unwrap_or(0)
    };
    let theorems_by_status_fut = async {
        let stmt = sea_orm::Statement::from_string(
            sea_orm::DatabaseBackend::Postgres,
            "SELECT status, count(*) AS c FROM theorems GROUP BY status".to_string(),
        );
        let mut out = serde_json::Map::new();
        if let Ok(rows) = sea_orm::ConnectionTrait::query_all_raw(pg, stmt).await {
            for r in rows {
                let s: String = r.try_get_by("status").unwrap_or_default();
                let c: i64 = r.try_get_by("c").unwrap_or(0);
                out.insert(s, json!(c));
            }
        }
        json!(out)
    };
    let trusted_users_fut = async {
        let stmt = sea_orm::Statement::from_string(
            sea_orm::DatabaseBackend::Postgres,
            "SELECT count(*) AS c FROM users WHERE is_trusted = TRUE".to_string(),
        );
        sea_orm::ConnectionTrait::query_one_raw(pg, stmt)
            .await
            .ok()
            .flatten()
            .and_then(|r| r.try_get_by::<i64, _>("c").ok())
            .unwrap_or(0)
    };
    let recent_audit_fut = async {
        nasrudin_pg::query::admin_audit_log::list_recent(pg, 10)
            .await
            .unwrap_or_default()
    };
    let admins_count_fut = async {
        nasrudin_pg::query::admin_users::count_admins(pg)
            .await
            .unwrap_or(0)
    };

    let (users_total, theorems_by_status, trusted_users, recent_audit, admins_count) = tokio::join!(
        users_total_fut,
        theorems_by_status_fut,
        trusted_users_fut,
        recent_audit_fut,
        admins_count_fut,
    );

    let reverify_depth = state.db.reverify_queue_depth().unwrap_or(0);
    let lake_depth = state.db.lake_promotion_queue_depth().unwrap_or(0);

    (
        StatusCode::OK,
        Json(json!({
            "users_total": users_total,
            "admins_count": admins_count,
            "trusted_users": trusted_users,
            "theorems_by_status": theorems_by_status,
            "reverify_queue_depth": reverify_depth,
            "lake_promotion_queue_depth": lake_depth,
            "recent_audit": recent_audit,
        })),
    )
        .into_response()
}
