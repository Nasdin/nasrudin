//! One cycle of the cluster steerer.
//!
//! Sequence:
//!  1. Determine `scope` = "B" if any paid `conjecture_jobs` row is
//!     `claimed`/`running` with a live lease, else "C".
//!  2. Close the previous cycle by computing its outcome JSON and
//!     stamping `ended_at`.
//!  3. Build the prompt: schema hint + recent history + demand
//!     snapshot + active-job summaries.
//!  4. Call the LLM through the trait-object `LlmCaller` (so tests
//!     can swap a fake).
//!  5. Parse + validate the response. On any failure, fall back to
//!     the most recent successfully-validated config and persist the
//!     row with `validation_failed=true`.
//!  6. Return the persisted row's id.
//!
//! The caller (a tokio task spawned in `main.rs`) ticks this every
//! `STEERER_CADENCE_SECONDS`.

use async_trait::async_trait;
use chrono::Utc;
use sea_orm::*;
use std::sync::Arc;
use thiserror::Error;
use uuid::Uuid;

use crate::state::AppState;
use crate::steerer::demand::aggregate_demand;
use crate::steerer::outcome::compute_outcome;
use crate::steerer::prompt::{build_prompt, ActiveJobSummary, HistoryEntry, SYSTEM_PROMPT};
use crate::steerer::schema::{default_config, SteeringConfig, SteeringValidationError};

const HISTORY_N: u64 = 10;
const DEMAND_WINDOW: std::time::Duration = std::time::Duration::from_secs(3600);

#[derive(Debug, Error)]
pub enum CycleError {
    #[error("db: {0}")]
    Db(#[from] sea_orm::DbErr),
    #[error("llm: {0}")]
    Llm(String),
    #[error("validation: {0}")]
    Validation(#[from] SteeringValidationError),
    #[error("parse: {0}")]
    Parse(String),
}

/// LLM dispatch surface used by the cycle. Production wires this to
/// `GradientCaller`; tests can wire a fake that returns canned JSON.
#[async_trait]
pub trait LlmCaller: Send + Sync {
    async fn call(
        &self,
        system: &str,
        user: &str,
    ) -> Result<(String, Option<i32>, Option<i32>), CycleError>;
}

pub async fn run_one_cycle(
    state: &Arc<AppState>,
    db: &DatabaseConnection,
    caller: &dyn LlmCaller,
    model_id: &str,
) -> Result<Uuid, CycleError> {
    // 1. Mode.
    let active_paid_count = active_paid_jobs(db).await?;
    let scope = if active_paid_count > 0 { "B" } else { "C" };

    // 2. Close previous cycle (if there's an open one).
    if let Ok(Some(prev)) = nasrudin_pg::query::cluster_steering::most_recent(db).await {
        if prev.ended_at.is_none() {
            let started: chrono::DateTime<Utc> = prev.started_at.with_timezone(&Utc);
            let now = Utc::now();
            let outcome = compute_outcome(db, started, now).await.unwrap_or_default();
            let _ = nasrudin_pg::query::cluster_steering::close_cycle(
                db,
                prev.id,
                serde_json::to_value(&outcome).unwrap_or(serde_json::Value::Null),
            )
            .await;
        }
    }

    // 3. Build prompt.
    let history = load_history(db, HISTORY_N).await?;
    let demand = aggregate_demand(db, DEMAND_WINDOW).await.unwrap_or_default();
    let active_jobs = active_job_summaries(db).await?;
    let user_prompt = build_prompt(scope, &history, &demand, &active_jobs);

    // 4. Call LLM.
    let (text, ptok, ctok) = caller.call(SYSTEM_PROMPT, &user_prompt).await?;

    // 5. Parse + validate. On any failure fall back to LKG.
    let (config, validation_failed) = match parse_and_validate(&text, scope) {
        Ok(c) => (c, false),
        Err(e) => {
            tracing::warn!(error=%e, scope=%scope,
                "steerer reply failed validation; falling back to last-known-good");
            let lkg = last_known_good(db).await?.unwrap_or_else(|| {
                let mut c = default_config();
                c.scope = scope.into();
                c
            });
            (lkg, true)
        }
    };

    // 6. Persist + push to ArcSwap.
    let row = nasrudin_pg::query::cluster_steering::insert_new_cycle(
        db,
        scope,
        serde_json::to_value(&config).unwrap_or(serde_json::Value::Null),
        model_id,
        validation_failed,
        ptok,
        ctok,
    )
    .await?;

    // Hot-reload the in-process snapshot. Workers see the new config
    // on their next `/api/seed` poll. Seed cache is invalidated
    // explicitly so they don't see a stale pairing of axioms+config.
    let body = serde_json::to_vec(&config).unwrap_or_default();
    let etag = xxhash_rust::xxh64::xxh64(&body, 0);
    state.steering.store(Arc::new(crate::state::SteeringSnapshot {
        config: serde_json::to_value(&config).unwrap_or(serde_json::Value::Null),
        etag,
        started_at: row.started_at.with_timezone(&Utc),
    }));
    state.invalidate_seed_cache();

    Ok(row.id)
}

fn parse_and_validate(text: &str, expected_scope: &str) -> Result<SteeringConfig, CycleError> {
    // Allow markdown-fenced replies as well as raw JSON. Strip a
    // leading ```json fence if present — small models do this even
    // when told not to.
    let trimmed = strip_code_fence(text.trim());
    let mut c: SteeringConfig =
        serde_json::from_str(trimmed).map_err(|e| CycleError::Parse(e.to_string()))?;
    if c.scope != expected_scope {
        c.scope = expected_scope.into();
    }
    // Enforce mode-B invariants before validate so we don't reject
    // for knobs/targets the model emitted in C-shape.
    if c.scope == "B" {
        c.hard_targets.clear();
        c.mutation_knobs = None;
    }
    c.validate()?;
    Ok(c)
}

fn strip_code_fence(s: &str) -> &str {
    let s = s.strip_prefix("```json").unwrap_or(s);
    let s = s.strip_prefix("```").unwrap_or(s);
    let s = s.strip_suffix("```").unwrap_or(s);
    s.trim()
}

async fn active_paid_jobs(db: &DatabaseConnection) -> Result<u64, sea_orm::DbErr> {
    use nasrudin_pg::entity::conjecture_jobs::{Column, Entity};
    Entity::find()
        .filter(Column::State.is_in(["claimed", "running", "Running"]))
        .filter(Column::LeaseExpiresAt.gt(Utc::now().fixed_offset()))
        .count(db)
        .await
}

async fn active_job_summaries(
    db: &DatabaseConnection,
) -> Result<Vec<ActiveJobSummary>, sea_orm::DbErr> {
    use nasrudin_pg::entity::conjecture_jobs::{Column, Entity};
    let rows = Entity::find()
        .filter(Column::State.is_in(["claimed", "running", "Running"]))
        .filter(Column::LeaseExpiresAt.gt(Utc::now().fixed_offset()))
        .all(db)
        .await?;
    Ok(rows
        .into_iter()
        .map(|r| ActiveJobSummary {
            domain: r.domain_hint.unwrap_or_else(|| "unknown".into()),
            conjecture_summary: r.hunch.chars().take(120).collect(),
        })
        .collect())
}

async fn load_history(
    db: &DatabaseConnection,
    n: u64,
) -> Result<Vec<HistoryEntry>, sea_orm::DbErr> {
    let rows = nasrudin_pg::query::cluster_steering::list_recent(db, n).await?;
    Ok(rows
        .into_iter()
        .map(|r| HistoryEntry {
            config: r.config_json,
            outcome: r.outcome_json,
            scope: r.scope,
            started_at: r.started_at.to_rfc3339(),
            validation_failed: r.validation_failed,
        })
        .collect())
}

async fn last_known_good(
    db: &DatabaseConnection,
) -> Result<Option<SteeringConfig>, sea_orm::DbErr> {
    let row = nasrudin_pg::query::cluster_steering::last_validated(db).await?;
    Ok(row.and_then(|r| serde_json::from_value(r.config_json).ok()))
}

/// Adapter that calls the Gradient provider through the `LlmCaller`
/// trait. Lives here next to the trait so it can stay a private impl
/// detail of the cycle module.
pub struct GradientCaller {
    provider: nasrudin_llm::GradientProvider,
    model: String,
}

impl GradientCaller {
    pub fn new(provider: nasrudin_llm::GradientProvider, model: String) -> Self {
        Self { provider, model }
    }
}

#[async_trait]
impl LlmCaller for GradientCaller {
    async fn call(
        &self,
        system: &str,
        user: &str,
    ) -> Result<(String, Option<i32>, Option<i32>), CycleError> {
        use nasrudin_llm::{CompletionRequest, LlmProvider, ResponseFormat};
        // Kimi K2.5 (and other reasoning models on Gradient) burn
        // tokens on `reasoning_content` before producing the actual
        // SteeringConfig JSON in `content`. 8192 is a generous
        // ceiling that keeps a SteeringConfig (~1500 token JSON) +
        // a long chain-of-thought comfortably below the wall. If the
        // model truncates anyway, the parse will fail and the cycle
        // falls back to last-known-good — see parse_and_validate.
        let req = CompletionRequest {
            model: self.model.clone(),
            system_prompt: system.to_owned(),
            user_prompt: user.to_owned(),
            max_tokens: 8192,
            temperature: 0.4,
            stop_sequences: vec![],
            response_format: ResponseFormat::Json {
                schema: serde_json::json!({}),
            },
        };
        let r = self
            .provider
            .complete(req)
            .await
            .map_err(|e| CycleError::Llm(e.to_string()))?;
        Ok((
            r.text,
            Some(r.input_tokens as i32),
            Some(r.output_tokens as i32),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::steerer::schema::default_config;

    #[test]
    fn parse_strips_markdown_fence() {
        let cfg = default_config();
        let json = serde_json::to_string(&cfg).unwrap();
        let fenced = format!("```json\n{}\n```", json);
        let r = parse_and_validate(&fenced, "C").unwrap();
        assert_eq!(r.version, 1);
    }

    #[test]
    fn parse_rejects_garbage() {
        let r = parse_and_validate("{not json", "C");
        assert!(matches!(r, Err(CycleError::Parse(_))));
    }

    #[test]
    fn parse_overrides_scope() {
        let mut cfg = default_config();
        cfg.scope = "C".into();
        let json = serde_json::to_string(&cfg).unwrap();
        let r = parse_and_validate(&json, "B").unwrap();
        assert_eq!(r.scope, "B");
        // B mode auto-clears mutation_knobs + hard_targets.
        assert!(r.mutation_knobs.is_none());
        assert!(r.hard_targets.is_empty());
    }
}
