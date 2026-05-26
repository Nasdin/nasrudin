//! `POST /api/admin/theorems/backfill_names?limit=100` —
//! synchronously walk Verified theorems with NULL `display_name` and
//! run LLM-naming. Concurrency capped via `AppState.naming_semaphore`
//! (default 3) so this can't starve the steerer of Gradient
//! bandwidth.
//!
//! Gated by [`RequireAdmin`]. Returns `{ named: N, errors: N,
//! skipped: N }` once the in-flight batch completes. Skips imported
//! rows (their Lean qualifier is already a usable name) and rows
//! that match the curated headline registry (they get the headline
//! name without an LLM call).

use std::sync::Arc;

use axum::{
    Json,
    extract::{Query, State},
    http::StatusCode,
    response::IntoResponse,
};
use serde::{Deserialize, Serialize};
use serde_json::json;

use crate::admin::require_admin::RequireAdmin;
use crate::reverify::{naming_action, NamingAction};
use crate::state::AppState;

#[derive(Deserialize, Default)]
pub struct BackfillParams {
    #[serde(default)]
    pub limit: Option<u64>,
}

#[derive(Serialize, Default)]
pub struct BackfillResponse {
    pub named: u64,
    pub errors: u64,
    pub skipped: u64,
}

const DEFAULT_LIMIT: u64 = 100;
const MAX_LIMIT: u64 = 500;

pub async fn backfill_names(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Query(params): Query<BackfillParams>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p.clone(),
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(json!({ "error": "pg_unavailable" })),
            )
                .into_response();
        }
    };
    let Some(client) = state.naming_client.clone() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(json!({ "error": "naming_client_unconfigured" })),
        )
            .into_response();
    };
    let limit = params.limit.unwrap_or(DEFAULT_LIMIT).min(MAX_LIMIT);

    let rows = match nasrudin_pg::query::theorems::list_unnamed_verified(&pg, limit).await
    {
        Ok(r) => r,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };

    let sem = Arc::clone(&state.naming_semaphore);
    let mut handles = Vec::with_capacity(rows.len());
    for row in rows {
        let action = naming_action(&row);
        let pg2 = pg.clone();
        let client2 = Arc::clone(&client);
        let sem2 = Arc::clone(&sem);
        handles.push(tokio::spawn(async move {
            match action {
                NamingAction::Skip => Outcome::Skipped,
                NamingAction::UseHeadline { name, description } => {
                    match nasrudin_pg::query::theorems::set_display_name(
                        &pg2,
                        &row.id,
                        &name,
                        &description,
                    )
                    .await
                    {
                        Ok(()) => Outcome::Named,
                        Err(e) => {
                            tracing::warn!(
                                error = %e,
                                theorem_id = %hex::encode(&row.id),
                                "backfill: headline write failed"
                            );
                            Outcome::Error
                        }
                    }
                }
                NamingAction::CallLlm => {
                    let _permit = match sem2.acquire_owned().await {
                        Ok(p) => p,
                        Err(_) => return Outcome::Error,
                    };
                    match client2
                        .name_theorem(
                            &row.canonical_statement,
                            &row.lean_source,
                            &row.axioms_used,
                            &row.domain,
                        )
                        .await
                    {
                        Ok(named) => {
                            match nasrudin_pg::query::theorems::set_display_name(
                                &pg2,
                                &row.id,
                                &named.display_name,
                                &named.description,
                            )
                            .await
                            {
                                Ok(()) => Outcome::Named,
                                Err(e) => {
                                    tracing::warn!(
                                        error = %e,
                                        theorem_id = %hex::encode(&row.id),
                                        "backfill: write failed"
                                    );
                                    Outcome::Error
                                }
                            }
                        }
                        Err(e) => {
                            tracing::warn!(
                                error = %e,
                                theorem_id = %hex::encode(&row.id),
                                "backfill: llm call failed"
                            );
                            Outcome::Error
                        }
                    }
                }
            }
        }));
    }

    let mut resp = BackfillResponse::default();
    for h in handles {
        match h.await {
            Ok(Outcome::Named) => resp.named += 1,
            Ok(Outcome::Skipped) => resp.skipped += 1,
            Ok(Outcome::Error) | Err(_) => resp.errors += 1,
        }
    }

    (StatusCode::OK, Json(resp)).into_response()
}

#[derive(Debug)]
enum Outcome {
    Named,
    Skipped,
    Error,
}
