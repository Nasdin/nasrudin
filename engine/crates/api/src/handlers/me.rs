//! Per-user stat aggregation, profile editing, and worker ownership view.
use axum::{Json, http::StatusCode, response::IntoResponse};
use serde::Deserialize;

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

/// `PATCH /api/me/profile` — update display name, country, and academic
/// profile fields.
///
/// `display_name` (when present) is written to `users.display_name`.
/// `country_code` (when present) is validated as ISO-3166-1 alpha-2 and
/// written to `users.country_code`. The empty string clears it.
/// `profile` (when present) is shallow-merged into
/// `user_preferences.preferences.profile` so partial updates preserve other
/// fields. Recognised profile keys are `bio`, `handle`, `institution`,
/// `field`, `location`, `website`.
#[derive(Deserialize)]
pub struct UpdateProfileBody {
    pub display_name: Option<String>,
    /// ISO-3166-1 alpha-2 (uppercase, 2 letters). Empty string clears.
    /// Server-side validation rejects anything else with 400.
    pub country_code: Option<String>,
    pub profile: Option<serde_json::Value>,
}

/// Validate the user-supplied country_code. Returns `Ok(Some(canonical))`,
/// `Ok(None)` (clear), or `Err(message)` for the client.
fn normalize_country_code(raw: &str) -> Result<Option<String>, &'static str> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return Ok(None);
    }
    if trimmed.len() != 2 || !trimmed.chars().all(|c| c.is_ascii_alphabetic()) {
        return Err("country_code must be ISO-3166-1 alpha-2 (2 letters)");
    }
    Ok(Some(trimmed.to_ascii_uppercase()))
}

pub async fn update_profile(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<UpdateProfileBody>,
) -> impl IntoResponse {
    let db = &auth_sess.backend.db;

    if let Some(name) = body.display_name.as_deref() {
        let trimmed = name.trim();
        let value = if trimmed.is_empty() { None } else { Some(trimmed) };
        if let Err(e) = nasrudin_pg::query::users::update_display_name(db, auth.user.id, value).await
        {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("display_name: {e}") })),
            );
        }
    }

    if let Some(raw) = body.country_code.as_deref() {
        let canonical = match normalize_country_code(raw) {
            Ok(v) => v,
            Err(msg) => {
                return (
                    StatusCode::BAD_REQUEST,
                    Json(serde_json::json!({ "error": msg })),
                );
            }
        };
        if let Err(e) = nasrudin_pg::query::users::update_country_code(
            db,
            auth.user.id,
            canonical.as_deref(),
        )
        .await
        {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("country_code: {e}") })),
            );
        }
    }

    if let Some(profile) = body.profile.as_ref() {
        if !profile.is_object() {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": "profile must be an object" })),
            );
        }
        // Read existing preferences, deep-merge into `.profile`, write back.
        let current = nasrudin_pg::query::user_preferences::get(db, auth.user.id)
            .await
            .unwrap_or_else(|_| serde_json::json!({}));
        let mut next = current.clone();
        let next_obj = next
            .as_object_mut()
            .expect("preferences is always an object");
        let existing_profile = next_obj
            .get("profile")
            .and_then(|v| v.as_object())
            .cloned()
            .unwrap_or_default();
        let mut merged = existing_profile;
        if let Some(patch) = profile.as_object() {
            for (k, v) in patch {
                if v.is_null() {
                    merged.remove(k);
                } else {
                    merged.insert(k.clone(), v.clone());
                }
            }
        }
        next_obj.insert(
            "profile".to_string(),
            serde_json::Value::Object(merged),
        );
        if let Err(e) =
            nasrudin_pg::query::user_preferences::set(db, auth.user.id, next).await
        {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("profile: {e}") })),
            );
        }
    }

    // Re-read so the client gets the canonical post-update view.
    let user = match nasrudin_pg::query::users::find_by_id(db, auth.user.id).await {
        Ok(Some(u)) => u,
        Ok(None) => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({ "error": "user not found" })),
            );
        }
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            );
        }
    };
    let prefs = nasrudin_pg::query::user_preferences::get(db, auth.user.id)
        .await
        .unwrap_or_else(|_| serde_json::json!({}));
    let profile = prefs
        .as_object()
        .and_then(|o| o.get("profile"))
        .cloned()
        .unwrap_or(serde_json::json!({}));

    (
        StatusCode::OK,
        Json(serde_json::json!({
            "id": user.id,
            "email": user.email,
            "display_name": user.display_name,
            "country_code": user.country_code,
            "created_at": user.created_at,
            "profile": profile,
        })),
    )
}

/// `GET /api/me/profile` — current display name + academic profile fields.
pub async fn get_profile(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    let db = &auth_sess.backend.db;
    let prefs = nasrudin_pg::query::user_preferences::get(db, auth.user.id)
        .await
        .unwrap_or_else(|_| serde_json::json!({}));
    let profile = prefs
        .as_object()
        .and_then(|o| o.get("profile"))
        .cloned()
        .unwrap_or(serde_json::json!({}));
    (
        StatusCode::OK,
        Json(serde_json::json!({
            "display_name": auth.user.display_name,
            "email": auth.user.email,
            "country_code": auth.user.country_code,
            "profile": profile,
        })),
    )
}

/// `GET /api/me/workers` — workers owned by the authenticated user.
///
/// Joined via `api_keys`: every non-revoked `kind = 'worker'` key whose
/// `user_id` matches the caller links to a worker by `name == workers.id`.
pub async fn workers(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    let db = &auth_sess.backend.db;
    match nasrudin_pg::query::me_workers::list_for_user(db, auth.user.id).await {
        Ok(rows) => (
            StatusCode::OK,
            Json(serde_json::json!({ "workers": rows })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}
