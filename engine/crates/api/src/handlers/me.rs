//! Per-user stat aggregation.
use axum::{Json, http::StatusCode, response::IntoResponse};

use crate::auth::{AuthOrApiKey, AuthSess};

/// `GET /api/me/stats` — contributor counts for the authenticated user.
///
/// Returns the count of saved searches and live API keys, plus the user's
/// verified-theorem total and the 10 most-recent verified theorems
/// attributed to them. The `theorems` table stores `contributor_id` as a
/// free-form string; we map it to the user's account id (UUID) stringified.
pub async fn stats(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    let db = &auth_sess.backend.db;

    let saved_count = nasrudin_pg::query::saved_searches::list_by_user(db, auth.user.id)
        .await
        .map(|v| v.len())
        .unwrap_or(0);
    let key_count = nasrudin_pg::query::api_keys::list_by_user(db, auth.user.id)
        .await
        .map(|v| v.len())
        .unwrap_or(0);

    let contributor_id = auth.user.id.to_string();
    let theorems_total =
        nasrudin_pg::query::theorems::count_by_contributor(db, &contributor_id)
            .await
            .unwrap_or(0);
    let theorems_recent =
        nasrudin_pg::query::theorems::list_by_contributor(db, &contributor_id, 10)
            .await
            .unwrap_or_default();

    (
        StatusCode::OK,
        Json(serde_json::json!({
            "saved_searches": saved_count,
            "api_keys": key_count,
            "theorems_total": theorems_total,
            "theorems_recent": theorems_recent,
        })),
    )
}
