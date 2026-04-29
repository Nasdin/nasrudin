//! `/api/conjecture/*` handlers. Phase D launches with provider locked to
//! `anthropic` per spec §13. OpenAI / Ollama remain in `nasrudin_llm`'s
//! Registry so they unlock by deleting the provider check.

use std::sync::Arc;

use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use uuid::Uuid;

use crate::auth::{AuthOrApiKey, AuthSess};
use crate::conjecture::orchestrate::{run_llm_phase, OrchestrateError};
use crate::conjecture::{
    types::*, ConjectureEvent,
};
use crate::state::AppState;

fn err(status: StatusCode, code: &str) -> Response {
    (status, Json(serde_json::json!({ "error": code }))).into_response()
}

pub async fn create(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<CreateConjectureRequest>,
) -> Response {
    if state.llm_encrypt_key.is_none() {
        return err(StatusCode::SERVICE_UNAVAILABLE, "key_encrypt_unset");
    }
    if body.hunch.trim().is_empty() {
        return err(StatusCode::BAD_REQUEST, "empty_hunch");
    }
    // Phase D ships anthropic-only. OpenAI / Ollama land in a follow-up
    // (the Registry already supports them; just drop this check).
    if body.provider != "anthropic" {
        return err(StatusCode::BAD_REQUEST, "unsupported_provider");
    }

    let pg = &auth_sess.backend.db;
    let user_id = auth.user.id;

    let job_id = match nasrudin_pg::query::conjecture_jobs::create(
        pg,
        nasrudin_pg::query::conjecture_jobs::CreateInput {
            owner_id: user_id,
            hunch: body.hunch.clone(),
            domain_hint: body.domain_hint.clone(),
            provider: body.provider.clone(),
            model: body.model.clone(),
            budget: serde_json::to_value(&body.budget).unwrap_or(serde_json::Value::Null),
        },
    )
    .await
    {
        Ok(id) => id,
        Err(e) => {
            tracing::warn!("create conjecture row failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };

    let suggestions = match run_llm_phase(
        &state,
        user_id,
        &body.hunch,
        body.domain_hint.as_deref(),
        &body.provider,
        &body.model,
    )
    .await
    {
        Ok(s) => s,
        Err(OrchestrateError::NoProviderKey(_)) => {
            let _ = nasrudin_pg::query::conjecture_jobs::mark_failed(pg, job_id, "no_provider_key")
                .await;
            return err(StatusCode::BAD_REQUEST, "no_provider_key");
        }
        Err(OrchestrateError::UnknownProvider(_)) => {
            return err(StatusCode::BAD_REQUEST, "unsupported_provider");
        }
        Err(OrchestrateError::KeyEncryptUnset) => {
            return err(StatusCode::SERVICE_UNAVAILABLE, "key_encrypt_unset");
        }
        Err(OrchestrateError::DecryptFailed) => {
            tracing::warn!("decrypt failed for user {user_id} provider {}", body.provider);
            let _ = nasrudin_pg::query::conjecture_jobs::mark_failed(pg, job_id, "decrypt_failed")
                .await;
            return err(StatusCode::INTERNAL_SERVER_ERROR, "decrypt_failed");
        }
        Err(OrchestrateError::InvalidLlmJson(msg)) => {
            tracing::warn!("llm returned non-json for job {job_id}: {msg}");
            let _ = nasrudin_pg::query::conjecture_jobs::mark_failed(
                pg,
                job_id,
                "llm_invalid_json",
            )
            .await;
            return err(StatusCode::BAD_GATEWAY, "llm_invalid_json");
        }
        Err(e) => {
            tracing::warn!("llm phase failed for job {job_id}: {e}");
            let _ =
                nasrudin_pg::query::conjecture_jobs::mark_failed(pg, job_id, "llm_call_failed")
                    .await;
            return err(StatusCode::BAD_GATEWAY, "llm_call_failed");
        }
    };

    let suggestions_json = serde_json::to_value(&suggestions).unwrap_or(serde_json::Value::Null);
    if let Err(e) =
        nasrudin_pg::query::conjecture_jobs::set_suggestions(pg, job_id, suggestions_json).await
    {
        tracing::warn!("persist suggestions failed: {e}");
        return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
    }

    let event_payload = serde_json::json!({"from": "Created", "to": "LlmComplete"});
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        job_id,
        "state_change",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(ConjectureEvent {
            id: event_id,
            job_id,
            kind: "state_change".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    Json(CreateConjectureResponse {
        job_id,
        state: "LlmComplete".into(),
        suggestions,
    })
    .into_response()
}

pub async fn start(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
    Json(body): Json<StartConjectureRequest>,
) -> Response {
    let pg = &auth_sess.backend.db;
    let user_id = auth.user.id;

    let row = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(r)) => r,
        Ok(None) => return err(StatusCode::NOT_FOUND, "not_found"),
        Err(e) => {
            tracing::warn!("get conjecture failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if row.owner_id != user_id {
        // Don't leak existence to non-owners.
        return err(StatusCode::NOT_FOUND, "not_found");
    }
    if row.state != "LlmComplete" {
        return err(StatusCode::CONFLICT, "wrong_state");
    }

    let suggestions: Vec<LlmSuggestion> = row
        .suggestions
        .as_ref()
        .and_then(|v| serde_json::from_value(v.clone()).ok())
        .unwrap_or_default();
    if body.chosen_index < 0 || (body.chosen_index as usize) >= suggestions.len() {
        return err(StatusCode::BAD_REQUEST, "chosen_index_out_of_range");
    }

    let chosen = &suggestions[body.chosen_index as usize];
    let seed = body
        .seed_overrides
        .clone()
        .unwrap_or_else(|| serde_json::to_value(chosen).unwrap_or(serde_json::Value::Null));

    if let Err(e) = nasrudin_pg::query::conjecture_jobs::set_chosen_seed(
        pg,
        id,
        body.chosen_index,
        seed,
    )
    .await
    {
        tracing::warn!("set chosen seed failed: {e}");
        return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
    }

    let event_payload = serde_json::json!({"from": "LlmComplete", "to": "QueuedForWorker"});
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        id,
        "state_change",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(ConjectureEvent {
            id: event_id,
            job_id: id,
            kind: "state_change".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    (
        StatusCode::OK,
        Json(serde_json::json!({"id": id, "state": "QueuedForWorker"})),
    )
        .into_response()
}

pub async fn get_one(
    State(_state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
) -> Response {
    let pg = &auth_sess.backend.db;
    let user_id = auth.user.id;

    let row = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(r)) => r,
        Ok(None) => return err(StatusCode::NOT_FOUND, "not_found"),
        Err(e) => {
            tracing::warn!("get conjecture failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if row.owner_id != user_id {
        return err(StatusCode::NOT_FOUND, "not_found");
    }
    Json(view_from_row(&row)).into_response()
}

pub async fn list_mine(
    State(_state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
) -> Response {
    let pg = &auth_sess.backend.db;
    let user_id = auth.user.id;
    match nasrudin_pg::query::conjecture_jobs::list_for_user(pg, user_id, 50).await {
        Ok(rows) => Json(ConjectureListResponse {
            conjectures: rows.iter().map(view_from_row).collect(),
        })
        .into_response(),
        Err(e) => {
            tracing::warn!("list conjectures failed: {e}");
            err(StatusCode::INTERNAL_SERVER_ERROR, "db_error")
        }
    }
}

/// SSE stream for one conjecture job. Replays the full event log from
/// `conjecture_events` first, then subscribes to the in-process broadcast
/// for live events. Filters by `job_id` so a single broadcast feeds many
/// concurrent SSE streams.
pub async fn sse(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
) -> Response {
    use axum::response::sse::{Event, KeepAlive, Sse};
    use futures::stream::{self, StreamExt};
    use std::convert::Infallible;
    use std::time::Duration;
    use tokio_stream::wrappers::BroadcastStream;

    let pg = &auth_sess.backend.db;
    let user_id = auth.user.id;

    let row = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(r)) => r,
        Ok(None) => return err(StatusCode::NOT_FOUND, "not_found"),
        Err(e) => {
            tracing::warn!("get conjecture failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if row.owner_id != user_id {
        return err(StatusCode::NOT_FOUND, "not_found");
    }

    let history = nasrudin_pg::query::conjecture_jobs::events_after(pg, id, 0, 1024)
        .await
        .unwrap_or_default();
    let history_stream = stream::iter(history.into_iter().map(move |e| {
        let payload = serde_json::json!({
            "id": e.id,
            "kind": e.kind,
            "payload": e.payload,
            "at": e.at,
        });
        Ok::<Event, Infallible>(Event::default().event(&e.kind).data(payload.to_string()))
    }));

    let rx = state.conjecture_event_tx.subscribe();
    let live = BroadcastStream::new(rx).filter_map(move |r| {
        let job_id = id;
        async move {
            match r {
                Ok(e) if e.job_id == job_id => {
                    let payload = serde_json::json!({
                        "id": e.id,
                        "kind": e.kind,
                        "payload": e.payload,
                        "at": e.at,
                    });
                    Some(Ok::<Event, Infallible>(
                        Event::default().event(&e.kind).data(payload.to_string()),
                    ))
                }
                _ => None,
            }
        }
    });

    let merged = history_stream.chain(live);
    Sse::new(merged)
        .keep_alive(
            KeepAlive::new()
                .interval(Duration::from_secs(15))
                .text("ping"),
        )
        .into_response()
}

fn view_from_row(row: &nasrudin_pg::entity::conjecture_jobs::Model) -> ConjectureView {
    let budget: BudgetSpec = serde_json::from_value(row.budget.clone()).unwrap_or(BudgetSpec {
        wall_seconds: 0,
        max_candidates: 0,
    });
    let suggestions: Option<Vec<LlmSuggestion>> = row
        .suggestions
        .as_ref()
        .and_then(|v| serde_json::from_value(v.clone()).ok());
    let verified_theorem_ids: Vec<String> = row
        .verified_theorem_ids
        .clone()
        .unwrap_or_default()
        .iter()
        .map(|b| b.iter().map(|x| format!("{x:02x}")).collect::<String>())
        .collect();
    ConjectureView {
        id: row.id,
        state: row.state.clone(),
        outcome: row.outcome.clone(),
        hunch: row.hunch.clone(),
        domain_hint: row.domain_hint.clone(),
        provider: row.provider.clone(),
        model: row.model.clone(),
        suggestions,
        chosen_index: row.chosen_index,
        budget,
        candidates_attempted: row.candidates_attempted,
        candidates_verified: row.candidates_verified,
        verified_theorem_ids,
        created_at: row.created_at.with_timezone(&chrono::Utc),
        completed_at: row.completed_at.map(|t| t.with_timezone(&chrono::Utc)),
    }
}
