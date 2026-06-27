//! Personal library — `/api/me/library/theorems` + `/api/me/library/folders`.
//!
//! Backs the pricing-page promises:
//!   Free:        "Save up to 50 theorems"
//!   Researcher+: "Unlimited library, folders, private notes"
//!
//! Quota enforcement: `library_max` from `PlanTier::quotas()` is checked
//! before insert; over-cap returns 402 `library_full` with the limit and
//! current plan_tier so the UI can render an upgrade modal.
//!
//! Auth: cookie session OR `Authorization: Bearer nsk_live_…`.

use axum::{Json, extract::Path, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use uuid::Uuid;

use crate::auth::{AuthOrApiKey, AuthSess};
use crate::billing::PlanTier;

// ── shared helpers ─────────────────────────────────────────────────────

fn parse_theorem_id(hex_str: &str) -> Result<Vec<u8>, (StatusCode, Json<serde_json::Value>)> {
    if hex_str.len() != 16 {
        return Err((
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "theorem_id must be 16 hex chars" })),
        ));
    }
    hex::decode(hex_str).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "theorem_id must be valid hex" })),
        )
    })
}

// ── POST /api/me/library/theorems ──────────────────────────────────────

#[derive(Deserialize)]
pub struct SaveBody {
    /// 16-char hex of the 8-byte theorem id.
    pub theorem_id: String,
    pub folder_id: Option<Uuid>,
    pub note: Option<String>,
    pub label: Option<String>,
}

pub async fn save_theorem(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<SaveBody>,
) -> impl IntoResponse {
    let id_bytes = match parse_theorem_id(&body.theorem_id) {
        Ok(b) => b,
        Err(e) => return e.into_response(),
    };
    let db = &auth_sess.backend.db;

    // Idempotent: if already saved, return existing record without re-counting.
    if let Ok(true) = nasrudin_pg::query::library::is_saved(db, auth.user.id, &id_bytes).await {
        return (
            StatusCode::OK,
            Json(serde_json::json!({ "saved": true, "already_saved": true })),
        )
            .into_response();
    }

    // Quota check (Free: 50, Researcher+: u32::MAX).
    let plan_tier = PlanTier::from_db(&auth.user.plan_tier);
    let limit = plan_tier.quotas().library_max;
    let count = match nasrudin_pg::query::library::count_saved(db, auth.user.id).await {
        Ok(c) => c,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("count: {e}") })),
            )
                .into_response();
        }
    };
    if count >= limit as u64 {
        return (
            StatusCode::PAYMENT_REQUIRED,
            Json(serde_json::json!({
                "error": "library_full",
                "limit": limit,
                "saved": count,
                "plan_tier": plan_tier.as_db(),
                "upgrade_to": "researcher",
            })),
        )
            .into_response();
    }

    match nasrudin_pg::query::library::save_theorem(
        db,
        auth.user.id,
        &id_bytes,
        body.folder_id,
        body.note.as_deref(),
        body.label.as_deref(),
    )
    .await
    {
        Ok(row) => (
            StatusCode::OK,
            Json(serde_json::json!({ "saved": true, "row": row, "saved_count": count + 1, "limit": limit })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("save: {e}") })),
        )
            .into_response(),
    }
}

// ── GET /api/me/library/theorems ───────────────────────────────────────

#[derive(Deserialize)]
pub struct ListSavedQuery {
    pub folder_id: Option<String>, // "ungrouped" | uuid | absent (= all)
    pub limit: Option<u64>,
    pub offset: Option<u64>,
}

pub async fn list_saved(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    axum::extract::Query(q): axum::extract::Query<ListSavedQuery>,
) -> impl IntoResponse {
    let db = &auth_sess.backend.db;
    let folder = match q.folder_id.as_deref() {
        None => nasrudin_pg::query::library::FolderFilter::All,
        Some("ungrouped") => nasrudin_pg::query::library::FolderFilter::Ungrouped,
        Some(s) => match Uuid::parse_str(s) {
            Ok(id) => nasrudin_pg::query::library::FolderFilter::Specific(id),
            Err(_) => {
                return (
                    StatusCode::BAD_REQUEST,
                    Json(serde_json::json!({ "error": "folder_id must be 'ungrouped' or a uuid" })),
                )
                    .into_response();
            }
        },
    };
    let limit = q.limit.unwrap_or(50).min(200);
    let offset = q.offset.unwrap_or(0);

    let plan_tier = PlanTier::from_db(&auth.user.plan_tier);
    let limit_max = plan_tier.quotas().library_max;
    let count = nasrudin_pg::query::library::count_saved(db, auth.user.id)
        .await
        .unwrap_or(0);

    match nasrudin_pg::query::library::list_saved(db, auth.user.id, folder, limit, offset).await {
        Ok(rows) => (
            StatusCode::OK,
            Json(serde_json::json!({
                "saved": rows,
                "count": count,
                "limit": limit_max,
                "plan_tier": plan_tier.as_db(),
            })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        )
            .into_response(),
    }
}

// ── DELETE /api/me/library/theorems/:id ────────────────────────────────

pub async fn unsave_theorem(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id_hex): Path<String>,
) -> impl IntoResponse {
    let id_bytes = match parse_theorem_id(&id_hex) {
        Ok(b) => b,
        Err(e) => return e.into_response(),
    };
    match nasrudin_pg::query::library::unsave_theorem(
        &auth_sess.backend.db,
        auth.user.id,
        &id_bytes,
    )
    .await
    {
        Ok(res) if res.rows_affected > 0 => {
            (StatusCode::OK, Json(serde_json::json!({ "deleted": true }))).into_response()
        }
        Ok(_) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not_saved" })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        )
            .into_response(),
    }
}

// ── PATCH /api/me/library/theorems/:id ─────────────────────────────────

#[derive(Deserialize)]
pub struct PatchSavedBody {
    /// Use `Some(None)` (JSON null) to clear, `Some(Some(uuid))` to set,
    /// omit field entirely to leave unchanged.
    pub folder_id: Option<Option<Uuid>>,
    pub note: Option<Option<String>>,
    pub label: Option<Option<String>>,
}

pub async fn patch_saved(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id_hex): Path<String>,
    Json(body): Json<PatchSavedBody>,
) -> impl IntoResponse {
    let id_bytes = match parse_theorem_id(&id_hex) {
        Ok(b) => b,
        Err(e) => return e.into_response(),
    };
    match nasrudin_pg::query::library::patch_saved(
        &auth_sess.backend.db,
        auth.user.id,
        &id_bytes,
        body.folder_id,
        body.note,
        body.label,
    )
    .await
    {
        Ok(Some(row)) => (StatusCode::OK, Json(serde_json::to_value(row).unwrap())).into_response(),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not_saved" })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        )
            .into_response(),
    }
}

// ── folder CRUD ────────────────────────────────────────────────────────

#[derive(Deserialize)]
pub struct CreateFolderBody {
    pub name: String,
    pub color: Option<String>,
}

pub async fn create_folder(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<CreateFolderBody>,
) -> impl IntoResponse {
    let trimmed = body.name.trim();
    if trimmed.is_empty() || trimmed.len() > 100 {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "name must be 1-100 chars" })),
        )
            .into_response();
    }
    match nasrudin_pg::query::library::create_folder(
        &auth_sess.backend.db,
        auth.user.id,
        trimmed,
        body.color.as_deref(),
    )
    .await
    {
        Ok(row) => (StatusCode::OK, Json(serde_json::to_value(row).unwrap())).into_response(),
        Err(DbErr::RecordNotInserted) => (
            StatusCode::CONFLICT,
            Json(serde_json::json!({ "error": "folder name already exists" })),
        )
            .into_response(),
        Err(e) => {
            let msg = e.to_string();
            // Postgres unique-violation surfaces as "duplicate key value".
            if msg.contains("duplicate key") || msg.contains("unique") {
                (
                    StatusCode::CONFLICT,
                    Json(serde_json::json!({ "error": "folder name already exists" })),
                )
                    .into_response()
            } else {
                (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(serde_json::json!({ "error": msg })),
                )
                    .into_response()
            }
        }
    }
}

pub async fn list_folders(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    match nasrudin_pg::query::library::list_folders(&auth_sess.backend.db, auth.user.id).await {
        Ok(rows) => (StatusCode::OK, Json(serde_json::json!({ "folders": rows }))).into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        )
            .into_response(),
    }
}

#[derive(Deserialize)]
pub struct PatchFolderBody {
    pub name: Option<String>,
    pub color: Option<Option<String>>,
}

pub async fn patch_folder(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
    Json(body): Json<PatchFolderBody>,
) -> impl IntoResponse {
    if let Some(n) = &body.name {
        if n.trim().is_empty() || n.trim().len() > 100 {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": "name must be 1-100 chars" })),
            )
                .into_response();
        }
    }
    // The borrow chain `body.color.map(|c| c.as_deref()…)` is unsound:
    // `c` is moved by-value into the closure, dropped at closure end,
    // so the `&str` returned would dangle. Bind via `as_ref()` so the
    // owning String stays alive in body.color and we hand out borrows
    // that live for the call site's lifetime instead.
    let color_arg = body.color.as_ref().map(|c| c.as_deref().map(|s| s.trim()));
    match nasrudin_pg::query::library::patch_folder(
        &auth_sess.backend.db,
        auth.user.id,
        id,
        body.name.as_deref().map(|s| s.trim()),
        color_arg,
    )
    .await
    {
        Ok(Some(row)) => (StatusCode::OK, Json(serde_json::to_value(row).unwrap())).into_response(),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "folder not found" })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        )
            .into_response(),
    }
}

pub async fn delete_folder(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    match nasrudin_pg::query::library::delete_folder(&auth_sess.backend.db, auth.user.id, id).await
    {
        Ok(res) if res.rows_affected > 0 => {
            (StatusCode::OK, Json(serde_json::json!({ "deleted": true }))).into_response()
        }
        Ok(_) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "folder not found" })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        )
            .into_response(),
    }
}

// Re-export DbErr so the unique-violation match works without an extra use.
use sea_orm::DbErr;
