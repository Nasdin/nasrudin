//! User-facing paid Researcher endpoints + the per-job SSE bus.
//!
//!   POST   /api/research/jobs              create job (decrements credits)
//!   GET    /api/research/jobs              list user's jobs
//!   GET    /api/research/jobs/{id}         detail
//!   GET    /api/research/jobs/{id}/events  SSE progress stream
//!   POST   /api/research/jobs/{id}/cancel  cancel + maybe-refund
//!
//! `emit_job_event` is the shared helper called from `jobs_claim.rs`
//! (heartbeat / claim / release / mark_proved) and from the user-side
//! cancel handler so SSE subscribers see the full lifecycle.

use std::convert::Infallible;
use std::sync::Arc;

use axum::{
    Json,
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
    response::sse::{Event, KeepAlive, Sse},
};
use futures::Stream;
use serde::Deserialize;
use serde_json::Value;
use tokio_stream::StreamExt;
use tokio_stream::wrappers::BroadcastStream;
use uuid::Uuid;

use nasrudin_ga::chain_ga::{MUTATION_OPS, PHYSICS_ATOM_NAMES};

use crate::auth::AuthOrApiKey;
use crate::jobs::JobEvent;
use crate::state::AppState;

/// `GET /api/research/steering_options` — read-only metadata the
/// `/research` submit form needs to render the Custom Steering disclosure:
/// the validated atom names (the same `PHYSICS_ATOM_NAMES` table the
/// server checks against), the mutation-operator names the GA recognises,
/// the snake_case domain keys the validator accepts inside `atom_pool`,
/// and the clamp bounds the server applies. Returning this from the API
/// (instead of hardcoding in the frontend) means adding a new atom is a
/// one-line backend change — no FE redeploy.
pub async fn steering_options() -> impl IntoResponse {
    // Domain keys mirror `Domain::Display` (snake_case). Listed in the
    // same order as the form's domain-hint dropdown so the UI's
    // ordering stays consistent.
    let domains = [
        "special_relativity",
        "electromagnetism",
        "classical_mechanics",
        "thermodynamics",
        "quantum_mechanics",
        "general_relativity",
        "pure_math",
    ];
    (
        StatusCode::OK,
        Json(serde_json::json!({
            "atom_names": PHYSICS_ATOM_NAMES,
            "operator_names": MUTATION_OPS,
            "domains": domains,
            "bounds": {
                "atom_weight": { "min": 0.0, "max": 4.0 },
                "mutation_prior": { "min": 0.0, "max": 2.0 },
                "mutation_knobs": {
                    "rate": { "min": 0.05, "max": 0.30 },
                    "population_size": { "min": 32, "max": 512, "step": 32 },
                    "suffix_bias": { "min": 0.0, "max": 1.0 },
                    "elitism_fraction": { "min": 0.0, "max": 0.2 }
                }
            }
        })),
    )
        .into_response()
}

/// Send a JobEvent on the per-job broadcast channel, lazily creating
/// it the first time anyone subscribes or emits. No-op on send error
/// (broadcast channels return Err when there are no receivers — the
/// user simply hasn't opened the SSE yet).
pub fn emit_job_event(state: &AppState, job_id: Uuid, ev: JobEvent) {
    let entry = state
        .job_events
        .entry(job_id)
        .or_insert_with(|| tokio::sync::broadcast::channel(64).0);
    let _ = entry.value().send(ev);
}

#[derive(Deserialize)]
pub struct CreateBody {
    pub hunch: String,
    #[serde(default)]
    pub domain_hint: Option<String>,
    /// Number of credits worth of cluster compute to spend on this job
    /// (1 credit = 96 lake-slot-hours). Default 1 reproduces the
    /// legacy single-credit behavior.
    #[serde(default = "default_credits_budget")]
    pub credits_budget: i32,
    /// When true, costs +1 credit and bumps `slice_priority` to 6 so
    /// the job claims ahead of normal-priority work.
    #[serde(default)]
    pub rush: bool,
    /// Optional per-job steering overrides applied to the GA's
    /// DiscoveryConfig at chunk-prepare time. Shape mirrors the
    /// LLM-emitted cluster steering payload so the same applier
    /// (`apply_steering_knobs_for_domain`) can consume it:
    ///
    /// ```jsonc
    /// {
    ///   "mutation_knobs": { "rate": 0.20, "population_size": 128,
    ///                        "suffix_bias": 0.6, "elitism_fraction": 0.1 },
    ///   "mutation_priors": { "append_productive_suffix": 2.0 },
    ///   "atom_pool": { "special_relativity": [
    ///     { "name": "m_c_sq", "weight": 4.0 } ]}
    /// }
    /// ```
    ///
    /// Costs +1 credit (signals intent + revenue). Validated server-
    /// side: atom names must be in PHYSICS_ATOM_NAMES, weights /
    /// priors / rates bounded to the same ranges the LLM-applier
    /// already clamps. Persisted to `conjecture_jobs.seed` JSONB and
    /// surfaced to the worker via the claim response.
    #[serde(default)]
    pub steering: Option<Value>,
}

fn default_credits_budget() -> i32 {
    1
}

/// Validate the researcher-supplied steering payload. Returns
/// `Ok(canonical_value)` on success — the canonical form is what we
/// persist to `seed` JSONB and what the worker re-applies (atom names
/// outside PHYSICS_ATOM_NAMES are stripped, weights clamped). On any
/// shape violation returns `Err(error_message)` for the 400 response.
///
/// Why canonicalise here instead of trusting `apply_steering_knobs`
/// to clamp at apply-time: we want the researcher to *see* what
/// they actually bought — when they steer with weight=99 and we
/// silently clamp to 4.0, the response payload + the persisted seed
/// both reflect the clamped value. No surprise discovery on next
/// chunk.
pub fn validate_and_canonicalize_steering(v: &Value) -> Result<Value, String> {
    let obj = v
        .as_object()
        .ok_or_else(|| "steering must be a JSON object".to_string())?;
    let mut out = serde_json::Map::new();

    if let Some(knobs) = obj.get("mutation_knobs") {
        let mut canon_knobs = serde_json::Map::new();
        let k = knobs
            .as_object()
            .ok_or_else(|| "steering.mutation_knobs must be an object".to_string())?;
        if let Some(r) = k.get("rate").and_then(Value::as_f64) {
            if !r.is_finite() {
                return Err("steering.mutation_knobs.rate must be finite".into());
            }
            canon_knobs.insert("rate".into(), serde_json::json!(r.clamp(0.05, 0.30)));
        }
        if let Some(p) = k.get("population_size").and_then(Value::as_u64) {
            canon_knobs.insert(
                "population_size".into(),
                serde_json::json!(p.clamp(32, 512)),
            );
        }
        if let Some(b) = k.get("suffix_bias").and_then(Value::as_f64) {
            if !b.is_finite() {
                return Err("steering.mutation_knobs.suffix_bias must be finite".into());
            }
            canon_knobs.insert("suffix_bias".into(), serde_json::json!(b.clamp(0.0, 1.0)));
        }
        if let Some(e) = k.get("elitism_fraction").and_then(Value::as_f64) {
            if !e.is_finite() {
                return Err("steering.mutation_knobs.elitism_fraction must be finite".into());
            }
            canon_knobs.insert(
                "elitism_fraction".into(),
                serde_json::json!(e.clamp(0.0, 0.2)),
            );
        }
        if !canon_knobs.is_empty() {
            out.insert("mutation_knobs".into(), Value::Object(canon_knobs));
        }
    }

    if let Some(priors) = obj.get("mutation_priors") {
        let p = priors
            .as_object()
            .ok_or_else(|| "steering.mutation_priors must be an object".to_string())?;
        let mut canon = serde_json::Map::new();
        for (op_name, w) in p {
            let f = w
                .as_f64()
                .ok_or_else(|| format!("mutation_priors.{op_name} must be a number"))?;
            if !f.is_finite() {
                return Err(format!("mutation_priors.{op_name} must be finite"));
            }
            canon.insert(op_name.clone(), serde_json::json!(f.clamp(0.0, 2.0)));
        }
        if !canon.is_empty() {
            out.insert("mutation_priors".into(), Value::Object(canon));
        }
    }

    if let Some(pool) = obj.get("atom_pool") {
        let p = pool
            .as_object()
            .ok_or_else(|| "steering.atom_pool must be an object keyed by domain".to_string())?;
        let mut canon_pool = serde_json::Map::new();
        for (domain, entries) in p {
            let arr = entries
                .as_array()
                .ok_or_else(|| format!("atom_pool.{domain} must be an array of {{name,weight}}"))?;
            let mut canon_arr = Vec::with_capacity(arr.len());
            for entry in arr {
                let name = entry
                    .get("name")
                    .and_then(Value::as_str)
                    .ok_or_else(|| format!("atom_pool.{domain}[].name is required"))?;
                if !PHYSICS_ATOM_NAMES.contains(&name) {
                    return Err(format!(
                        "atom_pool.{domain}: unknown atom `{name}` (allowed: {})",
                        PHYSICS_ATOM_NAMES.join(", ")
                    ));
                }
                let weight = entry
                    .get("weight")
                    .and_then(Value::as_f64)
                    .ok_or_else(|| format!("atom_pool.{domain}[{name}].weight is required"))?;
                if !weight.is_finite() {
                    return Err(format!("atom_pool.{domain}[{name}].weight must be finite"));
                }
                canon_arr.push(serde_json::json!({
                    "name": name,
                    "weight": weight.clamp(0.0, 4.0),
                }));
            }
            if !canon_arr.is_empty() {
                canon_pool.insert(domain.clone(), Value::Array(canon_arr));
            }
        }
        if !canon_pool.is_empty() {
            out.insert("atom_pool".into(), Value::Object(canon_pool));
        }
    }

    if out.is_empty() {
        return Err("steering is present but contains no recognised fields".into());
    }
    Ok(Value::Object(out))
}

#[cfg(test)]
mod tests {
    use super::validate_and_canonicalize_steering;
    use serde_json::json;

    #[test]
    fn rejects_non_object_root() {
        assert!(validate_and_canonicalize_steering(&json!("hi")).is_err());
        assert!(validate_and_canonicalize_steering(&json!([1, 2])).is_err());
    }

    #[test]
    fn rejects_unknown_atom_name() {
        let v = json!({
            "atom_pool": {
                "special_relativity": [
                    { "name": "not_an_atom", "weight": 1.0 }
                ]
            }
        });
        let err = validate_and_canonicalize_steering(&v).unwrap_err();
        assert!(err.contains("not_an_atom"), "got: {err}");
    }

    #[test]
    fn clamps_weight_to_max_four() {
        let v = json!({
            "atom_pool": {
                "special_relativity": [ { "name": "m_c_sq", "weight": 99.0 } ]
            }
        });
        let out = validate_and_canonicalize_steering(&v).unwrap();
        let w = out["atom_pool"]["special_relativity"][0]["weight"]
            .as_f64()
            .unwrap();
        assert!((w - 4.0).abs() < 1e-9);
    }

    #[test]
    fn rejects_nan_weight() {
        let v = json!({
            "atom_pool": {
                "sr": [ { "name": "m_c_sq", "weight": f64::NAN } ]
            }
        });
        assert!(validate_and_canonicalize_steering(&v).is_err());
    }

    #[test]
    fn rejects_empty_steering_object() {
        assert!(validate_and_canonicalize_steering(&json!({})).is_err());
    }

    #[test]
    fn round_trips_realistic_payload() {
        let v = json!({
            "mutation_knobs": { "rate": 0.2, "population_size": 128 },
            "mutation_priors": { "append_productive_suffix": 1.5 },
            "atom_pool": {
                "special_relativity": [ { "name": "m_c_sq", "weight": 4.0 } ]
            }
        });
        let out = validate_and_canonicalize_steering(&v).expect("valid");
        assert!(out["mutation_knobs"]["rate"].as_f64().unwrap() > 0.0);
        assert_eq!(
            out["atom_pool"]["special_relativity"][0]["name"].as_str(),
            Some("m_c_sq")
        );
    }
}

/// `POST /api/research/jobs` — atomically debit
/// `credits_budget + (rush ? 1 : 0)` research_credits and queue a
/// paid conjecture, both inside one Postgres transaction. On any
/// downstream failure the rollback automatically restores the credits
/// — no separate refund call needed.
pub async fn create(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Json(body): Json<CreateBody>,
) -> impl IntoResponse {
    if body.hunch.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "hunch_required" })),
        )
            .into_response();
    }
    if body.credits_budget < 1 {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "invalid_credits_budget" })),
        )
            .into_response();
    }

    // Validate optional steering payload before charging the user. We
    // canonicalise here so the persisted seed and the response body
    // show the actual clamped values the worker will apply — no
    // silent renegotiation at apply-time.
    let canonical_steering = match body.steering.as_ref() {
        Some(s) => match validate_and_canonicalize_steering(s) {
            Ok(v) => Some(v),
            Err(e) => {
                return (
                    StatusCode::BAD_REQUEST,
                    Json(serde_json::json!({ "error": "invalid_steering", "detail": e })),
                )
                    .into_response();
            }
        },
        None => None,
    };

    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    let user_id = auth.user.id;
    // Steering carries a +1 credit premium on top of any rush charge —
    // signals real intent (random tinkerers don't pay) and prices the
    // higher-quality outcome appropriately. Mirrors the rush surcharge
    // pattern so the surface is consistent.
    let steering_surcharge: i32 = if canonical_steering.is_some() { 1 } else { 0 };
    let total_cost: i32 = body.credits_budget + if body.rush { 1 } else { 0 } + steering_surcharge;
    let quota: i32 = 96 * body.credits_budget;
    let priority: i32 = 5 + if body.rush { 1 } else { 0 };

    use nasrudin_pg::sea_orm::*;
    let txn = match pg.begin().await {
        Ok(t) => t,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };

    // Atomic decrement. `>= total_cost` predicate makes this safe
    // under concurrent submissions — only one wins when there isn't
    // enough headroom.
    let decrement_result =
        nasrudin_pg::query::users::try_decrement_research_credits_n(&txn, user_id, total_cost)
            .await;
    let new_remaining = match decrement_result {
        Ok(Some(r)) => r,
        Ok(None) => {
            // Read fresh remaining for the 402 body, then rollback.
            let remaining =
                nasrudin_pg::query::users::try_decrement_research_credits_n(&txn, user_id, 0)
                    .await
                    .ok()
                    .flatten()
                    .unwrap_or(0);
            let _ = txn.rollback().await;
            return (
                StatusCode::PAYMENT_REQUIRED,
                Json(serde_json::json!({
                    "error": "insufficient_research_credits",
                    "required": total_cost,
                    "remaining": remaining,
                })),
            )
                .into_response();
        }
        Err(e) => {
            let _ = txn.rollback().await;
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };

    let id = Uuid::new_v4();
    let am = nasrudin_pg::entity::conjecture_jobs::ActiveModel {
        id: Set(id),
        owner_id: Set(user_id),
        state: Set("queued_for_llm".into()),
        outcome: Set(None),
        hunch: Set(body.hunch.clone()),
        domain_hint: Set(body.domain_hint.clone()),
        provider: Set("internal".into()),
        model: Set("ga".into()),
        suggestions: Set(None),
        chosen_index: Set(None),
        // Persist the canonical steering blob (post-clamp). The
        // worker reads this back via the claim response and feeds it
        // straight to `apply_steering_knobs_for_domain` each chunk.
        seed: Set(canonical_steering.clone()),
        budget: Set(serde_json::json!({
            "wall_seconds": 86400,
            "max_candidates": 10_000_000,
        })),
        claimed_by: Set(None),
        claimed_at: Set(None),
        lease_expires_at: Set(None),
        last_heartbeat_at: Set(None),
        candidates_attempted: Set(0),
        candidates_verified: Set(0),
        verified_theorem_ids: Set(None),
        created_at: Set(chrono::Utc::now().into()),
        completed_at: Set(None),
        paper_draft: Set(None),
        lake_slot_hours_quota: Set(quota),
        lake_slot_hours_consumed: Set(0.0),
        slice_priority: Set(priority),
        tier: Set("researcher".into()),
        // Default 4 — `atomic_claim_paid` overwrites this with the
        // claiming worker's reported available_lake_slots.
        allocated_slots: Set(4),
    };
    if let Err(e) = am.insert(&txn).await {
        // Transaction rollback restores the credits automatically.
        let _ = txn.rollback().await;
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response();
    }
    if let Err(e) = txn.commit().await {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response();
    }

    // Spawn background task to autonomously run the LLM Curation / Seeding Phase
    let state_for_task = state.clone();
    let id_for_task = id;
    let hunch_for_task = body.hunch.clone();
    let domain_hint_for_task = body.domain_hint.clone();
    
    tokio::spawn(async move {
        tracing::info!(job = %id_for_task, "Spawned autonomous LLM steering task for research job");
        let pg = match &state_for_task.pg {
            Some(p) => p,
            None => return,
        };
        
        // 1. Call the global system LLM phase
        let suggestions = crate::conjecture::orchestrate::run_system_llm_phase(
            &state_for_task,
            &hunch_for_task,
            domain_hint_for_task.as_deref(),
        )
        .await;
        
        let mut final_seed = None;
        let mut final_suggestions = None;
        
        match suggestions {
            Ok(s_list) if !s_list.is_empty() => {
                tracing::info!(job = %id_for_task, s_count = s_list.len(), "LLM generated steering suggestions");
                // Take the first suggestion
                let s = &s_list[0];
                let seed_json = serde_json::json!({
                    "axiom_set": s.axiom_set,
                    "initial_population": s.initial_population,
                    "mutation_priors": s.mutation_priors,
                    "target_shape": s.target_shape,
                    "rationale": s.rationale,
                });
                
                final_seed = Some(seed_json);
                final_suggestions = Some(serde_json::to_value(&s_list).unwrap_or(serde_json::Value::Null));
            }
            Ok(_) => {
                tracing::warn!(job = %id_for_task, "LLM returned empty suggestions");
            }
            Err(e) => {
                tracing::error!(job = %id_for_task, error = %e, "LLM steering failed");
            }
        }
        
        // 2. Update the job in PostgreSQL and activate it by transitioning state to "queued"
        use nasrudin_pg::entity::conjecture_jobs::ActiveModel;
        use nasrudin_pg::sea_orm::*;
        
        let mut am = ActiveModel {
            id: Set(id_for_task),
            state: Set("queued".into()), // Transition to queued so worker can claim it!
            ..Default::default()
        };
        
        if let Some(seed) = final_seed {
            am.seed = Set(Some(seed));
        }
        if let Some(sug) = final_suggestions {
            am.suggestions = Set(Some(sug));
        }
        
        if let Err(e) = am.update(pg).await {
            tracing::error!(job = %id_for_task, error = %e, "Failed to activate steered job in DB");
        } else {
            tracing::info!(job = %id_for_task, "Job successfully steered and activated ('queued')");
            // Emit JobEvent so SSE subscribers see the state transition from queued_for_llm to queued!
            crate::handlers::research_jobs::emit_job_event(
                &state_for_task,
                id_for_task,
                JobEvent::JobState {
                    state: "queued".into(),
                },
            );
        }
    });

    tracing::info!(
        user = %user_id,
        job = %id,
        credits = total_cost,
        budget = body.credits_budget,
        rush = body.rush,
        steered = canonical_steering.is_some(),
        remaining = new_remaining,
        "submit_decremented",
    );

    (
        StatusCode::CREATED,
        Json(serde_json::json!({
            "job_id": id,
            "state": "queued_for_llm",
            "credits_spent": total_cost,
            "credits_remaining": new_remaining,
            "steering_applied": canonical_steering,
            "price_breakdown": {
                "base": body.credits_budget,
                "rush": if body.rush { 1 } else { 0 },
                "steering": steering_surcharge,
            },
        })),
    )
        .into_response()
}

/// `GET /api/research/jobs` — newest-first list of the user's jobs.
pub async fn list(State(state): State<Arc<AppState>>, auth: AuthOrApiKey) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    use nasrudin_pg::sea_orm::*;
    let rows = nasrudin_pg::entity::conjecture_jobs::Entity::find()
        .filter(nasrudin_pg::entity::conjecture_jobs::Column::OwnerId.eq(auth.user.id))
        .filter(nasrudin_pg::entity::conjecture_jobs::Column::Tier.eq("researcher"))
        .order_by_desc(nasrudin_pg::entity::conjecture_jobs::Column::CreatedAt)
        .limit(200)
        .all(pg)
        .await
        .unwrap_or_default();
    (StatusCode::OK, Json(serde_json::json!({ "jobs": rows }))).into_response()
}

/// `GET /api/research/jobs/{id}` — detail. 404 on miss, 403 on
/// non-owner.
pub async fn detail(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) if j.owner_id == auth.user.id => (StatusCode::OK, Json(j)).into_response(),
        Ok(Some(_)) => (StatusCode::FORBIDDEN, "not_owner").into_response(),
        Ok(None) => (StatusCode::NOT_FOUND, "not_found").into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

/// `GET /api/research/jobs/{id}/events` — SSE stream of JobEvents
/// scoped to a single job. The user must own the job.
pub async fn events(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Path(id): Path<Uuid>,
) -> Result<Sse<impl Stream<Item = Result<Event, Infallible>>>, StatusCode> {
    let pg = state.pg.as_ref().ok_or(StatusCode::SERVICE_UNAVAILABLE)?;
    let job = nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        .ok_or(StatusCode::NOT_FOUND)?;
    if job.owner_id != auth.user.id {
        return Err(StatusCode::FORBIDDEN);
    }
    let entry = state
        .job_events
        .entry(id)
        .or_insert_with(|| tokio::sync::broadcast::channel(64).0);
    let rx = entry.value().subscribe();
    let stream = BroadcastStream::new(rx).filter_map(|r| {
        let ev = r.ok()?;
        let json = serde_json::to_string(&ev).unwrap_or_else(|_| "{}".into());
        Some(Ok(Event::default().data(json)))
    });
    Ok(Sse::new(stream).keep_alive(KeepAlive::default()))
}

/// `POST /api/research/jobs/{id}/cancel` — single-transaction terminal
/// transition + proportional refund. Idempotent against double-clicks:
/// a second call after the row is terminal returns 409.
pub async fn cancel(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };

    let outcome =
        match nasrudin_pg::query::conjecture_jobs::cancel_paid_with_refund(pg, id, auth.user.id)
            .await
        {
            Ok(o) => o,
            Err(e) => {
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(serde_json::json!({ "error": e.to_string() })),
                )
                    .into_response();
            }
        };

    if !outcome.row_was_cancelled {
        // Either the row was already terminal, doesn't exist, or the
        // owner mismatched. Collapse to 409 — the user can refresh to
        // see the current state. (404/403 fan-out is reserved for
        // cases where we want to distinguish; the cancel button on
        // the UI doesn't.)
        return (
            StatusCode::CONFLICT,
            Json(serde_json::json!({ "error": "terminal_state" })),
        )
            .into_response();
    }

    // Release in-memory cluster capacity outside the transaction —
    // ONLY for jobs that were actually in-flight. For a queued job
    // no slots were ever reserved, and unconditional release would
    // credit phantom slots to the pool.
    if outcome.was_in_flight {
        let allocated = (outcome.allocated_slots as u32).max(1);
        state.capacity.release_paid_slots(allocated);
    }

    tracing::info!(
        user = %auth.user.id,
        job = %id,
        refund = outcome.refunded_credits,
        was_in_flight = outcome.was_in_flight,
        "cancel_refunded",
    );

    emit_job_event(
        &state,
        id,
        JobEvent::Cancelled {
            refunded_credits: outcome.refunded_credits,
        },
    );
    (
        StatusCode::OK,
        Json(serde_json::json!({
            "cancelled": true,
            "refunded_credits": outcome.refunded_credits,
        })),
    )
        .into_response()
}
