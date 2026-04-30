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

use crate::state::{AppState, ClusterConfigSnapshot};
use crate::steerer::bandit;
use crate::steerer::demand::aggregate_demand;
use crate::steerer::outcome::compute_outcome;
use crate::steerer::prompt::{build_prompt, ActiveJobSummary, HistoryEntry, SYSTEM_PROMPT};
use crate::steerer::schema::{default_config, SteeringConfig, SteeringValidationError};

const HISTORY_N: u64 = 10;
const DEMAND_WINDOW: std::time::Duration = std::time::Duration::from_secs(3600);
const BANDIT_REWARD_WINDOW_SECS: i64 = 600;

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

    // 3. Bandit step: for each island, attribute the previous chunk's
    //    cluster_reports to the K we asked for last cycle, compute
    //    reward, persist the pull, then UCB1-select K_next. The bandit
    //    runs independently of the LLM — no LLM call needed for this
    //    structural decision.
    let prev_cc = state.cluster_config.load();
    let now = Utc::now();
    let reward_window_start =
        now - chrono::Duration::seconds(BANDIT_REWARD_WINDOW_SECS);
    let mut next_k_per_island: std::collections::HashMap<String, u32> =
        std::collections::HashMap::new();
    let mut bandit_state = serde_json::Map::new();
    for &domain in bandit::ISLAND_DOMAINS {
        // Reward the previous K (if any).
        if let Some(&prev_k) = prev_cc.k_per_island.get(domain) {
            match bandit::extract_reward_inputs(
                db,
                domain,
                prev_k as i16,
                reward_window_start,
            )
            .await
            {
                Ok(inputs) => {
                    let r = bandit::compute_reward(inputs);
                    if let Err(e) = nasrudin_pg::query::cluster_bandit_arms::record_pull(
                        db,
                        domain,
                        prev_k as i16,
                        r,
                    )
                    .await
                    {
                        tracing::warn!(domain, prev_k, error=%e,
                            "bandit record_pull failed");
                    }
                }
                Err(e) => tracing::warn!(domain, prev_k, error=%e,
                    "bandit reward extraction failed"),
            }
        }
        // Select K_next via UCB1 over the (now-updated) arm state.
        let arms = bandit::load_arms(db, domain).await.unwrap_or_default();
        let chosen = if arms.is_empty() {
            bandit::DEFAULT_K
        } else {
            bandit::select_k_ucb1(&arms) as u32
        };
        next_k_per_island.insert(domain.into(), chosen);
        let arms_json: Vec<serde_json::Value> = arms
            .iter()
            .map(|a| {
                serde_json::json!({
                    "k": a.k,
                    "pulls": a.pulls,
                    "mean_reward": if a.pulls > 0 { a.total_reward / a.pulls as f64 } else { 0.0 },
                })
            })
            .collect();
        bandit_state.insert(domain.into(), serde_json::Value::Array(arms_json));
    }

    // Push the new cluster_config snapshot before the prompt is built
    // so workers polling /api/seed see the new K immediately. Seed
    // cache is invalidated below alongside the steering update.
    let cc_body = serde_json::to_vec(&next_k_per_island).unwrap_or_default();
    let cc_etag = xxhash_rust::xxh64::xxh64(&cc_body, 0);
    state.cluster_config.store(Arc::new(ClusterConfigSnapshot {
        k_per_island: next_k_per_island.clone(),
        etag: cc_etag,
    }));

    // Snapshot the directive-bandit arm table for the next chunk of
    // workers. ~600 rows, full read each cycle. Worker-side bandits
    // would lose cluster-wide learning, so we keep this server-side.
    let arm_rows = nasrudin_pg::query::cluster_directive_arms::snapshot_all(db)
        .await
        .unwrap_or_default();
    let directive_rows: Vec<crate::state::DirectiveArmRow> = arm_rows
        .into_iter()
        .map(|m| crate::state::DirectiveArmRow {
            island_domain: m.island_domain,
            action: m.action,
            strength_bucket: m.strength_bucket,
            multiplier_choice: m.multiplier_choice,
            pulls: m.pulls,
            total_reward: m.total_reward,
        })
        .collect();
    let directive_etag = {
        let mut hasher_input = Vec::with_capacity(directive_rows.len() * 32);
        for r in &directive_rows {
            hasher_input.extend_from_slice(r.island_domain.as_bytes());
            hasher_input.extend_from_slice(r.action.as_bytes());
            hasher_input.extend_from_slice(&r.strength_bucket.to_le_bytes());
            hasher_input.extend_from_slice(&r.multiplier_choice.to_le_bytes());
            hasher_input.extend_from_slice(&r.pulls.to_le_bytes());
            hasher_input.extend_from_slice(&r.total_reward.to_le_bytes());
        }
        xxhash_rust::xxh64::xxh64(&hasher_input, 0)
    };
    state
        .directive_arms
        .store(Arc::new(crate::state::DirectiveArmsSnapshot {
            arms: directive_rows,
            etag: directive_etag,
        }));

    // Compute-scaling bandit snapshot. Same pattern as the directive
    // arms; ~150 rows so the full read each cycle is cheap.
    let compute_rows_raw = nasrudin_pg::query::cluster_compute_arms::snapshot_all(db)
        .await
        .unwrap_or_default();
    let compute_rows: Vec<crate::state::ComputeArmRow> = compute_rows_raw
        .into_iter()
        .map(|m| crate::state::ComputeArmRow {
            island_domain: m.island_domain,
            strength_bucket: m.strength_bucket,
            multiplier_choice: m.multiplier_choice,
            pulls: m.pulls,
            total_reward: m.total_reward,
        })
        .collect();
    let compute_etag = {
        let mut buf = Vec::with_capacity(compute_rows.len() * 32);
        for r in &compute_rows {
            buf.extend_from_slice(r.island_domain.as_bytes());
            buf.extend_from_slice(&r.strength_bucket.to_le_bytes());
            buf.extend_from_slice(&r.multiplier_choice.to_le_bytes());
            buf.extend_from_slice(&r.pulls.to_le_bytes());
            buf.extend_from_slice(&r.total_reward.to_le_bytes());
        }
        xxhash_rust::xxh64::xxh64(&buf, 0)
    };
    state
        .compute_arms
        .store(Arc::new(crate::state::ComputeArmsSnapshot {
            arms: compute_rows,
            etag: compute_etag,
        }));

    // 4. Build prompt.
    let history = load_history(db, HISTORY_N).await?;
    let demand = aggregate_demand(db, DEMAND_WINDOW).await.unwrap_or_default();
    let active_jobs = active_job_summaries(db).await?;

    // Most-recent ClusterSummaries per island for the LLM prompt.
    let mut cluster_summaries: Vec<serde_json::Value> = Vec::new();
    for &domain in bandit::ISLAND_DOMAINS {
        if let Ok(rows) =
            nasrudin_pg::query::cluster_reports::recent_for_island(db, domain, 12).await
        {
            for r in rows {
                cluster_summaries.push(r.summary);
            }
        }
    }

    let user_prompt = build_prompt(
        scope,
        &history,
        &demand,
        &active_jobs,
        &cluster_summaries,
        &serde_json::Value::Object(bandit_state),
        &next_k_per_island,
    );

    // 5. Call LLM.
    let (text, ptok, ctok) = caller.call(SYSTEM_PROMPT, &user_prompt).await?;

    // 6. Parse + validate. On any failure fall back to LKG.
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

    // 7. Persist + push to ArcSwap.
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
        c.cluster_directives.clear();
        c.compute_directives.clear();
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
