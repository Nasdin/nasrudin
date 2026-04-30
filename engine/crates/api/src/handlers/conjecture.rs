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

use crate::auth::{AuthOrApiKey, AuthSess, WorkerAuth};
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

    // Targeted-search quota gate. Free tier gets 0; paid tiers get the
    // ceiling from PlanTier::quotas(). Counted against the user's current
    // billing period (Stripe cycle) or the calendar month for free users.
    let plan_tier = crate::billing::PlanTier::from_db(&auth.user.plan_tier);
    let quota = plan_tier.quotas().targeted_searches_per_period;
    let now = chrono::Utc::now();
    let cycle_start = auth
        .user
        .plan_cycle_start
        .map(|d| d.with_timezone(&chrono::Utc));
    let period_start = crate::billing::period_start(cycle_start, now);
    let used = nasrudin_pg::query::targeted_search_usage::count_in_period(
        pg,
        user_id,
        period_start,
    )
    .await
    .unwrap_or(0);
    if used >= quota as u64 {
        return (
            StatusCode::PAYMENT_REQUIRED,
            Json(serde_json::json!({
                "error": "targeted_search_quota_exhausted",
                "limit_per_period": quota,
                "plan_tier": plan_tier.as_db(),
            })),
        )
            .into_response();
    }

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

    // Record usage immediately after the row exists so re-issued requests
    // reflect the new count. Best-effort: a record-failure won't undo the
    // already-created job — we'd rather double-count than refund silently.
    if let Err(e) = nasrudin_pg::query::targeted_search_usage::record(
        pg,
        user_id,
        job_id,
        period_start,
    )
    .await
    {
        tracing::warn!("targeted_search_usage record failed for job {job_id}: {e}");
    }

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
        claimed_by: row.claimed_by.clone(),
        last_heartbeat_at: row.last_heartbeat_at.map(|t| t.with_timezone(&chrono::Utc)),
        lease_expires_at: row.lease_expires_at.map(|t| t.with_timezone(&chrono::Utc)),
        created_at: row.created_at.with_timezone(&chrono::Utc),
        completed_at: row.completed_at.map(|t| t.with_timezone(&chrono::Utc)),
    }
}

// ===========================================================================
// Phase E: worker-side endpoints (claim / heartbeat / submit / complete)
// ===========================================================================

/// Per-conjecture lease in seconds. Heartbeat extends by the same.
const LEASE_SECONDS: u32 = 300;

#[derive(serde::Serialize)]
pub struct ClaimResponse {
    pub job_id: Uuid,
    pub seed: serde_json::Value,
    pub budget: serde_json::Value,
    pub hunch: String,
    pub provider: String,
    pub model: String,
    pub lease_seconds: u32,
}

/// `POST /api/conjecture/claim` — atomic worker dequeue.
pub async fn claim(State(state): State<Arc<AppState>>, auth: WorkerAuth) -> Response {
    let worker_id = auth.0.worker_handle.clone();
    if state
        .worker_rate_limiter
        .check_and_consume(&worker_id, 1)
        .is_err()
    {
        return err(StatusCode::TOO_MANY_REQUESTS, "rate_limited");
    }
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    let claimed =
        match nasrudin_pg::query::conjecture_jobs::claim_next(pg, &worker_id).await {
            Ok(Some(c)) => c,
            Ok(None) => return (StatusCode::NO_CONTENT, "").into_response(),
            Err(e) => {
                tracing::warn!("conjecture claim_next failed: {e}");
                return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
            }
        };

    let event_payload = serde_json::json!({
        "from": "QueuedForWorker",
        "to": "Running",
        "claimed_by": worker_id,
    });
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        claimed.id,
        "state_change",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(ConjectureEvent {
            id: event_id,
            job_id: claimed.id,
            kind: "state_change".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    Json(ClaimResponse {
        job_id: claimed.id,
        seed: claimed.seed,
        budget: claimed.budget,
        hunch: claimed.hunch,
        provider: claimed.provider,
        model: claimed.model,
        lease_seconds: LEASE_SECONDS,
    })
    .into_response()
}

#[derive(serde::Deserialize)]
pub struct HeartbeatBody {
    pub candidates_attempted: i32,
    pub candidates_verified: i32,
    pub time_elapsed_s: u32,
}

/// `POST /api/conjecture/{id}/heartbeat` — extend lease + bump counters.
pub async fn heartbeat(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
    Json(body): Json<HeartbeatBody>,
) -> Response {
    let worker_id = auth.0.worker_handle.clone();
    if state
        .worker_rate_limiter
        .check_and_consume(&worker_id, 1)
        .is_err()
    {
        return err(StatusCode::TOO_MANY_REQUESTS, "rate_limited");
    }
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    let n = match nasrudin_pg::query::conjecture_jobs::update_heartbeat_progress(
        pg,
        id,
        &worker_id,
        body.candidates_attempted,
        body.candidates_verified,
    )
    .await
    {
        Ok(n) => n,
        Err(e) => {
            tracing::warn!("conjecture heartbeat update failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if n == 0 {
        return err(StatusCode::FORBIDDEN, "not_lease_owner");
    }

    let event_payload = serde_json::json!({
        "candidates_attempted": body.candidates_attempted,
        "candidates_verified": body.candidates_verified,
        "time_elapsed_s": body.time_elapsed_s,
    });
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        id,
        "progress",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(ConjectureEvent {
            id: event_id,
            job_id: id,
            kind: "progress".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    (
        StatusCode::OK,
        Json(serde_json::json!({"lease_extended_seconds": LEASE_SECONDS})),
    )
        .into_response()
}

#[derive(serde::Deserialize)]
pub struct SubmitBody {
    pub engine_git_sha: String,
    pub lean_version: String,
    pub theorem: crate::handlers::ingest::IngestTheorem,
}

/// `POST /api/conjecture/{id}/submit` — one verified theorem, delegated
/// to the existing ingest pipeline. Appends the theorem id to the row's
/// verified_theorem_ids, bumps candidates_verified, and broadcasts
/// `candidate_verified`.
pub async fn submit(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
    Json(body): Json<SubmitBody>,
) -> Response {
    let worker_id = auth.0.worker_handle.clone();
    if state
        .worker_rate_limiter
        .check_and_consume(&worker_id, 1)
        .is_err()
    {
        return err(StatusCode::TOO_MANY_REQUESTS, "rate_limited");
    }
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    // Pre-flight ownership + lease. Defends against submit-without-claim.
    let row = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(r)) => r,
        Ok(None) => return err(StatusCode::NOT_FOUND, "not_found"),
        Err(e) => {
            tracing::warn!("get conjecture failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if row.claimed_by.as_deref() != Some(worker_id.as_str()) || row.state != "Running" {
        return err(StatusCode::FORBIDDEN, "not_lease_owner");
    }

    // Conjecture-loop submission path: trust-bypass not applicable here
    // (the conjecture flow runs its own paid lifecycle), so we pass an
    // explicit "untrusted, env default rate" decision so the row gets a
    // sane default in the worker_trusted/worker_spot_check_rate columns.
    let decision = crate::trust::TrustDecision {
        trusted: false,
        spot_check_rate: state.trusted_spot_check_rate,
        source: crate::trust::TrustSource::Default,
    };
    let result = crate::handlers::ingest::ingest_one_theorem(
        &state,
        &worker_id,
        &body.engine_git_sha,
        &body.lean_version,
        &body.theorem,
        &decision,
    )
    .await;

    // Only Pending items count as "candidates verified" — the ingest
    // helper queues for reverify; we tally + emit the event here.
    if matches!(result.status, crate::handlers::ingest::IngestStatus::Pending) {
        let bytes = match hex::decode(&result.theorem_id) {
            Ok(b) => b,
            Err(_) => {
                tracing::warn!("ingest helper returned invalid theorem_id hex");
                return err(StatusCode::INTERNAL_SERVER_ERROR, "bad_theorem_id");
            }
        };
        let _ = nasrudin_pg::query::conjecture_jobs::append_verified_theorem(
            pg,
            id,
            &worker_id,
            bytes,
        )
        .await;

        let event_payload = serde_json::json!({
            "theorem_id": result.theorem_id,
            "canonical_hash": result.canonical_hash,
            "worker_id": worker_id,
        });
        if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
            pg,
            id,
            "candidate_verified",
            event_payload.clone(),
        )
        .await
        {
            let _ = state.conjecture_event_tx.send(ConjectureEvent {
                id: event_id,
                job_id: id,
                kind: "candidate_verified".into(),
                payload: event_payload,
                at: chrono::Utc::now(),
            });
        }
    }

    (StatusCode::OK, Json(result)).into_response()
}

// ===========================================================================
// Phase F: paper draft generation (LLM streaming + persisted markdown)
// ===========================================================================

#[derive(serde::Serialize)]
pub struct StartPaperResponse {
    pub job_id: Uuid,
    pub state: &'static str,
}

const PAPER_SYSTEM_PROMPT: &str = "You are a scientific writer drafting a 1-2 page \
research-paper-style summary of a freshly discovered theorem. The reader is a \
researcher who proposed the original conjecture. Output Markdown with sections: \
Title, Abstract, Introduction (motivate the conjecture from the original hunch), \
Statement (with LaTeX), Proof outline (translate the Lean proof into prose; do not \
copy-paste Lean), Implications, References (cite corpus theorems by id). Be \
concise and rigorous. Do not invent citations.";

fn build_paper_user_prompt(view: &ConjectureView) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    writeln!(out, "# Original conjecture\n\n{}\n", view.hunch).ok();
    if let Some(d) = &view.domain_hint {
        writeln!(out, "Domain hint: {d}\n").ok();
    }
    if let Some(suggestions) = &view.suggestions {
        if let Some(idx) = view.chosen_index {
            if let Some(s) = suggestions.get(idx as usize) {
                writeln!(out, "## LLM-supplied derivation seed\n\n{}\n", s.rationale).ok();
                if let Some(target) = &s.target_shape {
                    writeln!(out, "Target shape: `{target}`").ok();
                }
                writeln!(out, "Axiom subset: {:?}\n", s.axiom_set).ok();
            }
        }
    }
    writeln!(
        out,
        "## Verified theorems from this run\n\n{} theorem(s) verified:",
        view.verified_theorem_ids.len()
    )
    .ok();
    for id in &view.verified_theorem_ids {
        writeln!(out, "- `{id}`").ok();
    }
    writeln!(
        out,
        "\n## Run metadata\n\nProvider: {} / {}\nCandidates attempted: {}\nVerified: {}",
        view.provider, view.model, view.candidates_attempted, view.candidates_verified,
    )
    .ok();
    out
}

/// `POST /api/conjecture/{id}/paper` — kick off async LLM streaming. The
/// handler returns 202 immediately; the actual draft generation runs as
/// a background task that appends each chunk to `paper_draft` and emits
/// `paper_chunk` events on the conjecture SSE channel.
pub async fn start_paper_draft(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
) -> Response {
    if state.llm_encrypt_key.is_none() {
        return err(StatusCode::SERVICE_UNAVAILABLE, "key_encrypt_unset");
    }
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
    if row.state != "Complete" {
        return err(StatusCode::CONFLICT, "not_complete");
    }
    if row.outcome.as_deref() != Some("Verified") {
        return err(StatusCode::CONFLICT, "no_verified_theorems");
    }

    // Reset the column so the SSE stream sees only fresh chunks.
    let _ = nasrudin_pg::query::conjecture_jobs::clear_paper_draft(pg, id).await;

    let view = view_from_row(&row);
    let provider = row.provider.clone();
    let model = row.model.clone();
    let state_arc = Arc::clone(&state);
    let pg_arc = pg.clone();

    tokio::spawn(async move {
        if let Err(e) = run_paper_stream(state_arc, pg_arc, id, user_id, view, provider, model)
            .await
        {
            tracing::warn!("paper stream for {id} failed: {e}");
        }
    });

    (
        StatusCode::ACCEPTED,
        Json(StartPaperResponse {
            job_id: id,
            state: "PaperGenerating",
        }),
    )
        .into_response()
}

/// Background driver: decrypts the user's LLM key, opens a streaming
/// connection, and forwards each chunk to PG + the SSE channel.
async fn run_paper_stream(
    state: Arc<AppState>,
    pg: nasrudin_pg::sea_orm::DatabaseConnection,
    job_id: Uuid,
    user_id: Uuid,
    view: ConjectureView,
    provider: String,
    model: String,
) -> Result<(), String> {
    use futures::StreamExt;
    use nasrudin_llm::{
        encryption::{decrypt, EncryptedKey},
        AnthropicProvider, CompletionRequest, LlmProvider, OllamaProvider, OpenAiProvider,
        ResponseFormat,
    };

    let encrypt_key = state
        .llm_encrypt_key
        .as_ref()
        .ok_or_else(|| "key_encrypt_unset".to_string())?;
    let cipher = nasrudin_pg::query::user_llm_keys::get_ciphertext(&pg, user_id, &provider)
        .await
        .map_err(|e| format!("db: {e}"))?
        .ok_or_else(|| "no_provider_key".to_string())?;
    let api_key = decrypt(&EncryptedKey(cipher), encrypt_key)
        .map_err(|_| "decrypt_failed".to_string())?;

    let req = CompletionRequest {
        model: model.clone(),
        system_prompt: PAPER_SYSTEM_PROMPT.to_string(),
        user_prompt: build_paper_user_prompt(&view),
        max_tokens: 4096,
        temperature: 0.5,
        stop_sequences: vec![],
        response_format: ResponseFormat::Free,
    };

    // The Registry doesn't expose stream() yet (paper draft is the only
    // caller and Anthropic is the only provider with a real impl), so
    // build the provider directly here. Keep the provider owned in scope
    // for the lifetime of the stream — `stream<'a>(&'a self, …)` borrows
    // from self.
    let provider_box: Box<dyn LlmProvider> = match provider.as_str() {
        "anthropic" => Box::new(AnthropicProvider::new(api_key)),
        "openai" => Box::new(OpenAiProvider::new(api_key)),
        "ollama" => Box::new(OllamaProvider::new()),
        _ => return Err(format!("unknown_provider: {provider}")),
    };
    let mut stream_box = provider_box
        .stream(req)
        .await
        .map_err(|e| format!("stream: {e}"))?;

    while let Some(item) = stream_box.next().await {
        match item {
            Ok(chunk) => {
                if !chunk.text.is_empty() {
                    let _ = nasrudin_pg::query::conjecture_jobs::append_paper_chunk(
                        &pg, job_id, &chunk.text,
                    )
                    .await;
                    let payload = serde_json::json!({"text": chunk.text});
                    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
                        &pg,
                        job_id,
                        "paper_chunk",
                        payload.clone(),
                    )
                    .await
                    {
                        let _ = state.conjecture_event_tx.send(crate::conjecture::ConjectureEvent {
                            id: event_id,
                            job_id,
                            kind: "paper_chunk".into(),
                            payload,
                            at: chrono::Utc::now(),
                        });
                    }
                }
                if chunk.finish_reason.is_some() {
                    let payload = serde_json::json!({"final": true});
                    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
                        &pg,
                        job_id,
                        "paper_done",
                        payload.clone(),
                    )
                    .await
                    {
                        let _ = state.conjecture_event_tx.send(crate::conjecture::ConjectureEvent {
                            id: event_id,
                            job_id,
                            kind: "paper_done".into(),
                            payload,
                            at: chrono::Utc::now(),
                        });
                    }
                    break;
                }
            }
            Err(e) => {
                let payload = serde_json::json!({"error": e.to_string()});
                let _ = nasrudin_pg::query::conjecture_jobs::insert_event(
                    &pg,
                    job_id,
                    "paper_error",
                    payload.clone(),
                )
                .await;
                let _ = state.conjecture_event_tx.send(crate::conjecture::ConjectureEvent {
                    id: 0,
                    job_id,
                    kind: "paper_error".into(),
                    payload,
                    at: chrono::Utc::now(),
                });
                return Err(e.to_string());
            }
        }
    }
    Ok(())
}

/// `GET /api/conjecture/{id}/paper.md` — returns the persisted draft as
/// `text/markdown`. 404 when no draft has been generated yet.
pub async fn get_paper(
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
    let Some(draft) = row.paper_draft else {
        return err(StatusCode::NOT_FOUND, "no_paper_draft");
    };
    (
        StatusCode::OK,
        [(axum::http::header::CONTENT_TYPE, "text/markdown; charset=utf-8")],
        draft,
    )
        .into_response()
}

#[derive(serde::Deserialize)]
pub struct CompleteBody {
    /// One of: "Verified" | "NoResult" | "TimedOut" | "Cancelled".
    pub outcome: String,
    #[serde(default)]
    pub reason: Option<String>,
}

/// `POST /api/conjecture/{id}/complete` — final state transition.
pub async fn complete_handler(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
    Json(body): Json<CompleteBody>,
) -> Response {
    let worker_id = auth.0.worker_handle.clone();
    if state
        .worker_rate_limiter
        .check_and_consume(&worker_id, 1)
        .is_err()
    {
        return err(StatusCode::TOO_MANY_REQUESTS, "rate_limited");
    }
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    let valid = matches!(
        body.outcome.as_str(),
        "Verified" | "NoResult" | "TimedOut" | "Cancelled"
    );
    if !valid {
        return err(StatusCode::BAD_REQUEST, "invalid_outcome");
    }

    let n = match nasrudin_pg::query::conjecture_jobs::complete(pg, id, &worker_id, &body.outcome)
        .await
    {
        Ok(n) => n,
        Err(e) => {
            tracing::warn!("conjecture complete failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if n == 0 {
        return err(StatusCode::FORBIDDEN, "not_lease_owner");
    }

    let event_payload = serde_json::json!({
        "outcome": body.outcome,
        "reason": body.reason,
    });
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        id,
        "complete",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(ConjectureEvent {
            id: event_id,
            job_id: id,
            kind: "complete".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    (
        StatusCode::OK,
        Json(serde_json::json!({"id": id, "state": "Complete"})),
    )
        .into_response()
}
