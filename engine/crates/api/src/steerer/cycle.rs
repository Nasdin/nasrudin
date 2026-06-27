//! One cycle of the cluster steerer.
//!
//! Sequence:
//!  1. Determine `scope` = "B" if any paid `conjecture_jobs` row is
//!     `claimed`/`running` with a live lease, else "C".
//!  2. Close the previous cycle by computing its outcome JSON and
//!     stamping `ended_at`.
//!  3. Run RL-only worker-facing updates: K-bandit, arm snapshots,
//!     and reward attribution.
//!  4. When a strategy refresh is due, call the LLM through the
//!     trait-object `LlmCaller` (so tests can swap a fake).
//!  5. Parse + validate the response. On any failure, fall back to
//!     the most recent successfully-validated config and persist the
//!     row with `validation_failed=true`.
//!  6. If no strategy refresh is needed, reuse the cached steering
//!     config and persist an RL-only cycle.
//!  7. Return the persisted row's id.
//!
//! The caller (a tokio task spawned in `main.rs`) ticks this every
//! `STEERER_CADENCE_SECONDS`. LLM strategy updates can be throttled
//! further with `LLM_STEER_INTERVAL_SECONDS`.

use async_trait::async_trait;
use chrono::{DateTime, Utc};
use sea_orm::*;
use std::sync::Arc;
use thiserror::Error;
use uuid::Uuid;

use crate::state::{AppState, ClusterConfigSnapshot};
use crate::steerer::bandit;
use crate::steerer::demand::aggregate_demand;
use crate::steerer::outcome::compute_outcome;
use crate::steerer::prompt::{ActiveJobSummary, HistoryEntry, SYSTEM_PROMPT, build_prompt};
use crate::steerer::schema::{SteeringConfig, SteeringValidationError, default_config};

const HISTORY_N: u64 = 10;
const DEMAND_WINDOW: std::time::Duration = std::time::Duration::from_secs(3600);
const BANDIT_REWARD_WINDOW_SECS: i64 = 600;
const CLUSTER_SUMMARIES_PER_ISLAND_FOR_LLM: u64 = 4;
const MIN_STEERER_COMPLETION_TOKENS: u32 = 512;

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
        max_total_tokens: u32,
    ) -> Result<(String, Option<i32>, Option<i32>), CycleError>;
}

pub async fn run_one_cycle(
    state: &Arc<AppState>,
    db: &DatabaseConnection,
    caller: &dyn LlmCaller,
    model_id: &str,
    refresh_strategy: bool,
) -> Result<Uuid, CycleError> {
    run_one_cycle_inner(state, db, caller, model_id, refresh_strategy, None).await
}

pub async fn run_one_cycle_with_refresh_interval(
    state: &Arc<AppState>,
    db: &DatabaseConnection,
    caller: &dyn LlmCaller,
    model_id: &str,
    refresh_strategy: bool,
    min_strategy_refresh_interval_secs: i64,
) -> Result<Uuid, CycleError> {
    run_one_cycle_inner(
        state,
        db,
        caller,
        model_id,
        refresh_strategy,
        Some(min_strategy_refresh_interval_secs),
    )
    .await
}

async fn run_one_cycle_inner(
    state: &Arc<AppState>,
    db: &DatabaseConnection,
    caller: &dyn LlmCaller,
    model_id: &str,
    refresh_strategy: bool,
    min_strategy_refresh_interval_secs: Option<i64>,
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
    let reward_window_start = now - chrono::Duration::seconds(BANDIT_REWARD_WINDOW_SECS);
    let mut next_k_per_island: std::collections::HashMap<String, u32> =
        std::collections::HashMap::new();
    let mut bandit_state = serde_json::Map::new();
    for &domain in bandit::ISLAND_DOMAINS {
        // Reward the previous K (if any).
        if let Some(&prev_k) = prev_cc.k_per_island.get(domain) {
            match bandit::extract_reward_inputs(db, domain, prev_k as i16, reward_window_start)
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
    // Load LinUCB sufficient stats once per cycle and build a
    // (island, action) → (a_flat, b_vec, pulls) map. Then for each
    // arm row, compute its LinUCB score at snapshot time so workers
    // don't need the matrix data shipped to them.
    let linucb_rows = nasrudin_pg::query::cluster_directive_linucb::snapshot_all(db)
        .await
        .unwrap_or_default();
    let mut linucb_map: std::collections::HashMap<(String, String), (Vec<f64>, Vec<f64>, i64)> =
        std::collections::HashMap::new();
    for r in linucb_rows {
        linucb_map.insert(
            (r.island_domain, r.action),
            (r.a_matrix, r.b_vector, r.pulls),
        );
    }
    let max_choice: u8 = std::cmp::min(
        crate::steerer::directive_bandit::MAX_MULTIPLIER_CHOICES - 1,
        8,
    );
    let directive_rows: Vec<crate::state::DirectiveArmRow> = arm_rows
        .into_iter()
        .map(|m| {
            // Strength bucket midpoint (0.1, 0.3, 0.5, 0.7, 0.9).
            let strength_mid = (m.strength_bucket as f64 + 0.5) / 5.0;
            let linucb_score = linucb_map
                .get(&(m.island_domain.clone(), m.action.clone()))
                .filter(|(_, _, pulls)| *pulls >= crate::steerer::linucb::LINUCB_WARMUP_PULLS)
                .and_then(|(a, b, _)| {
                    crate::steerer::linucb::score(
                        a,
                        b,
                        strength_mid,
                        m.multiplier_choice as u8,
                        max_choice,
                    )
                });
            crate::state::DirectiveArmRow {
                island_domain: m.island_domain,
                action: m.action,
                strength_bucket: m.strength_bucket,
                multiplier_choice: m.multiplier_choice,
                pulls: m.pulls,
                total_reward: m.total_reward,
                linucb_score,
            }
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

    // Online action expansion: for each (island, action, bucket)
    // slot whose outer multiplier_choice has dominated long enough,
    // materialise the next-finer-grained arm so the bandit can
    // explore beyond the initial 5-choice range. Cheap: a few PG
    // round-trips at most, only fires when a slot actually merits
    // expansion. AlphaProof-style adaptive action-space growth.
    let expanded = crate::steerer::directive_bandit::expand_dominant_arms(db)
        .await
        .unwrap_or(0);
    if expanded > 0 {
        tracing::info!(expanded, "directive bandit: arms materialised by expansion");
    }
    let expanded_compute = crate::steerer::directive_bandit::expand_dominant_compute_arms(db)
        .await
        .unwrap_or(0);
    if expanded_compute > 0 {
        tracing::info!(
            expanded_compute,
            "compute bandit: arms materialised by expansion"
        );
    }

    // Compute-scaling bandit snapshot. Same pattern as the directive
    // arms; ~150 rows so the full read each cycle is cheap.
    let compute_rows_raw = nasrudin_pg::query::cluster_compute_arms::snapshot_all(db)
        .await
        .unwrap_or_default();
    let compute_linucb_rows = nasrudin_pg::query::cluster_compute_linucb::snapshot_all(db)
        .await
        .unwrap_or_default();
    let mut compute_linucb_map: std::collections::HashMap<String, (Vec<f64>, Vec<f64>, i64)> =
        std::collections::HashMap::new();
    for r in compute_linucb_rows {
        compute_linucb_map.insert(r.island_domain, (r.a_matrix, r.b_vector, r.pulls));
    }
    let compute_rows: Vec<crate::state::ComputeArmRow> = compute_rows_raw
        .into_iter()
        .map(|m| {
            let strength_mid = (m.strength_bucket as f64 + 0.5) / 5.0;
            let linucb_score = compute_linucb_map
                .get(&m.island_domain)
                .filter(|(_, _, pulls)| *pulls >= crate::steerer::linucb::LINUCB_WARMUP_PULLS)
                .and_then(|(a, b, _)| {
                    crate::steerer::linucb::score(
                        a,
                        b,
                        strength_mid,
                        m.multiplier_choice as u8,
                        max_choice,
                    )
                });
            crate::state::ComputeArmRow {
                island_domain: m.island_domain,
                strength_bucket: m.strength_bucket,
                multiplier_choice: m.multiplier_choice,
                pulls: m.pulls,
                total_reward: m.total_reward,
                linucb_score,
            }
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

    let mut refresh_strategy = refresh_strategy;
    if refresh_strategy && llm_evidence_gate_enabled() {
        let evidence_window_secs =
            llm_strategy_budget_window_secs(min_strategy_refresh_interval_secs);
        let evidence_cutoff = Utc::now() - chrono::Duration::seconds(evidence_window_secs);
        let cluster_report_count =
            nasrudin_pg::query::cluster_reports::count_since(db, evidence_cutoff).await?;
        let verified_count =
            nasrudin_pg::query::theorems::count_verified_since(db, evidence_cutoff)
                .await
                .unwrap_or(0);
        let min_cluster_reports = llm_min_cluster_reports_for_refresh();
        let min_verified_theorems = llm_min_verified_theorems_for_refresh();
        let enough_evidence = strategy_refresh_has_enough_evidence(
            active_paid_count,
            cluster_report_count,
            verified_count,
            min_cluster_reports,
            min_verified_theorems,
        );
        if !enough_evidence {
            tracing::info!(
                evidence_window_secs,
                cluster_report_count,
                verified_count,
                min_cluster_reports,
                min_verified_theorems,
                "LLM strategy refresh skipped: insufficient new RL/GA evidence"
            );
            refresh_strategy = false;
        } else if active_paid_count == 0 && llm_skip_if_rl_confident_enabled() {
            let confident = recent_rl_policy_evidence_is_confident(db, evidence_cutoff).await;
            if confident {
                tracing::info!(
                    evidence_window_secs,
                    cluster_report_count,
                    verified_count,
                    "LLM strategy refresh skipped: local RL policy evidence is confident"
                );
                refresh_strategy = false;
            }
        }
    }

    let claimed_strategy_cycle = if refresh_strategy {
        if let Some(interval_secs) = min_strategy_refresh_interval_secs {
            let claim_config = steering_from_state_cache(state, scope)?;
            let claim_json = serde_json::to_value(&claim_config).unwrap_or(serde_json::Value::Null);
            let claimed = nasrudin_pg::query::cluster_steering::try_claim_strategy_refresh(
                db,
                scope,
                claim_json,
                model_id,
                interval_secs,
            )
            .await?;
            if claimed.is_none() {
                tracing::info!(
                    interval_secs,
                    "LLM strategy refresh already claimed inside interval; running RL-only cycle"
                );
            }
            claimed
        } else {
            None
        }
    } else {
        None
    };
    let refresh_strategy = refresh_strategy
        && (min_strategy_refresh_interval_secs.is_none() || claimed_strategy_cycle.is_some());

    let (config, ptok, ctok, validation_failed) = if refresh_strategy {
        // 4. Build prompt.
        let history = load_history(db, HISTORY_N).await?;
        let demand = aggregate_demand(db, DEMAND_WINDOW)
            .await
            .unwrap_or_default();
        let active_jobs = active_job_summaries(db).await?;

        // Most-recent ClusterSummaries per island for the LLM prompt.
        let mut cluster_summaries: Vec<serde_json::Value> = Vec::new();
        for &domain in bandit::ISLAND_DOMAINS {
            if let Ok(rows) = nasrudin_pg::query::cluster_reports::recent_for_island(
                db,
                domain,
                CLUSTER_SUMMARIES_PER_ISLAND_FOR_LLM,
            )
            .await
            {
                for r in rows {
                    cluster_summaries.push(r.summary);
                }
            }
        }

        // Self-curriculum: show the LLM its in-flight proposed targets so
        // it can mark them proved/abandoned in this cycle's emission.
        let in_flight_targets: Vec<serde_json::Value> =
            nasrudin_pg::query::llm_proposed_targets::in_flight(db, 30)
                .await
                .unwrap_or_default()
                .into_iter()
                .map(|t| {
                    serde_json::json!({
                        "target_id": t.target_id,
                        "latex": t.latex,
                        "domain": t.domain,
                        "status": t.status,
                        "proposed_at": t.proposed_at.to_rfc3339(),
                    })
                })
                .collect();

        // Rolling indefinite-horizon LLM memory: the LLM rewrites
        // `lessons_learned` each strategy cycle by replacing the prior
        // version.
        let previous_lessons = last_known_good(db)
            .await
            .ok()
            .flatten()
            .map(|c| c.lessons_learned)
            .unwrap_or_default();

        let platform_target_states = load_platform_target_states(db).await.unwrap_or_default();

        let user_prompt = build_prompt(
            scope,
            &history,
            &demand,
            &active_jobs,
            &cluster_summaries,
            &serde_json::Value::Object(bandit_state),
            &next_k_per_island,
            &in_flight_targets,
            &previous_lessons,
            &platform_target_states,
        );

        // 5. Call LLM. Provider outages and local token-budget
        // refusals must not stop the RL/GA workhorse loop; fall back to
        // the last validated strategic config and persist the cycle as
        // validation_failed so operators can see the skipped refresh.
        let approx_input_tokens =
            approximate_tokens(SYSTEM_PROMPT) + approximate_tokens(&user_prompt);
        let rolling_window_secs =
            llm_strategy_budget_window_secs(min_strategy_refresh_interval_secs);
        let cutoff = Utc::now() - chrono::Duration::seconds(rolling_window_secs);
        let used_tokens =
            nasrudin_pg::query::cluster_steering::llm_tokens_used_since(db, cutoff).await?;
        let window_max_tokens = llm_strategy_window_max_tokens();
        let (config, ptok, ctok, validation_failed) = match budgeted_call_max_total_tokens(
            used_tokens,
            window_max_tokens,
            approx_input_tokens,
        ) {
            Ok(call_max_total_tokens) => {
                match caller
                    .call(SYSTEM_PROMPT, &user_prompt, call_max_total_tokens)
                    .await
                {
                    Ok((text, ptok, ctok)) => {
                        // 6. Parse + validate. On any failure fall back to LKG.
                        match parse_and_validate(&text, scope) {
                            Ok(c) => (c, ptok, ctok, false),
                            Err(e) => {
                                tracing::warn!(error=%e, scope=%scope,
                                    "steerer reply failed validation; falling back to last-known-good");
                                (fallback_config(db, scope).await?, ptok, ctok, true)
                            }
                        }
                    }
                    Err(e) => {
                        tracing::warn!(error=%e, scope=%scope,
                            "steerer LLM call failed; falling back to last-known-good");
                        (fallback_config(db, scope).await?, None, None, true)
                    }
                }
            }
            Err(reason) => {
                tracing::warn!(
                    used_tokens,
                    window_max_tokens,
                    approx_input_tokens,
                    rolling_window_secs,
                    reason = %reason,
                    "steerer rolling LLM budget exhausted; reusing cached strategy"
                );
                (fallback_config(db, scope).await?, None, None, true)
            }
        };
        (config, ptok, ctok, validation_failed)
    } else {
        (steering_from_state_cache(state, scope)?, None, None, false)
    };

    // 7. Persist + push to ArcSwap.
    let config_json = serde_json::to_value(&config).unwrap_or(serde_json::Value::Null);
    let row = if let Some(claimed) = claimed_strategy_cycle {
        nasrudin_pg::query::cluster_steering::update_strategy_refresh_result(
            db,
            claimed.id,
            config_json,
            validation_failed,
            ptok,
            ctok,
        )
        .await?
    } else {
        nasrudin_pg::query::cluster_steering::insert_new_cycle(
            db,
            scope,
            config_json,
            model_id,
            validation_failed,
            ptok,
            ctok,
        )
        .await?
    };

    if refresh_strategy {
        // Self-curriculum bookkeeping only updates on strategy cycles.
        // Idempotent on re-emission:
        // upsert_open is a no-op for existing rows, so the LLM can keep
        // emitting the same target across cycles without resetting its
        // lifecycle.
        for st in &config.soft_targets {
            if let Some(tid) = &st.target_id {
                let _ = nasrudin_pg::query::llm_proposed_targets::upsert_open(
                    db,
                    tid,
                    &st.latex,
                    &st.domain,
                    st.weight as f64,
                )
                .await;
            }
        }
        for upd in &config.target_status_updates {
            let allowed = matches!(
                upd.new_status.as_str(),
                "open" | "proving" | "proved" | "abandoned"
            );
            if !allowed {
                tracing::warn!(
                    target_id = %upd.target_id,
                    bad_status = %upd.new_status,
                    "rejecting target_status_update with invalid status"
                );
                continue;
            }
            let _ = nasrudin_pg::query::llm_proposed_targets::set_status(
                db,
                &upd.target_id,
                &upd.new_status,
            )
            .await;
        }

        if !config.proposed_targets.is_empty() {
            let (accepted, dropped) = crate::platform_targets::enqueue_proposed_targets(
                db,
                &config.proposed_targets,
                model_id,
            )
            .await;
            tracing::info!(
                accepted,
                dropped,
                "applied proposed_targets from steerer cycle"
            );
        }
    }

    // Hot-reload the in-process snapshot. Workers see the new config
    // on their next `/api/seed` poll. Seed cache is invalidated
    // explicitly so they don't see a stale pairing of axioms+config.
    let body = serde_json::to_vec(&config).unwrap_or_default();
    let etag = xxhash_rust::xxh64::xxh64(&body, 0);
    state
        .steering
        .store(Arc::new(crate::state::SteeringSnapshot {
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

fn steering_from_state_cache(
    state: &Arc<AppState>,
    expected_scope: &str,
) -> Result<SteeringConfig, CycleError> {
    let snapshot = state.steering.load();
    let mut config =
        serde_json::from_value(snapshot.config.clone()).unwrap_or_else(|_| default_config());
    if let Err(err) = config.validate() {
        tracing::warn!(error=%err, "cached steering config invalid; using default_config");
        config = default_config();
    }
    config.scope = expected_scope.into();
    if config.scope == "B" {
        config.hard_targets.clear();
        config.mutation_knobs = None;
        config.cluster_directives.clear();
        config.compute_directives.clear();
    }
    config.validate()?;
    Ok(config)
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

async fn fallback_config(
    db: &DatabaseConnection,
    scope: &str,
) -> Result<SteeringConfig, sea_orm::DbErr> {
    let mut c = last_known_good(db).await?.unwrap_or_else(|| {
        let mut c = default_config();
        c.scope = scope.into();
        c
    });
    c.scope = scope.into();
    if c.scope == "B" {
        c.hard_targets.clear();
        c.mutation_knobs = None;
        c.cluster_directives.clear();
        c.compute_directives.clear();
    }
    Ok(c)
}

/// Pull every `tier='platform'` conjecture_jobs row's (hunch, state)
/// pair into a tiny JSON list the LLM uses to decide whether to emit
/// `proposed_targets`. Returning [] means "platform queue empty" —
/// the LLM treats that case as "skip the proposed_targets lever
/// because the seeder hasn't run yet" rather than "all proved."
async fn load_platform_target_states(
    db: &DatabaseConnection,
) -> Result<Vec<serde_json::Value>, sea_orm::DbErr> {
    use nasrudin_pg::entity::conjecture_jobs::{Column, Entity};
    let rows = Entity::find()
        .filter(Column::Tier.eq("platform"))
        .all(db)
        .await?;
    Ok(rows
        .into_iter()
        .map(|r| {
            serde_json::json!({
                "hunch": r.hunch,
                "domain_hint": r.domain_hint,
                "state": r.state,
                "candidates_verified": r.candidates_verified,
            })
        })
        .collect())
}

/// Adapter that calls the Gradient provider through the `LlmCaller`
/// trait. Lives here next to the trait so it can stay a private impl
/// detail of the cycle module.
///
/// Schema-mode behaviour. The caller starts in **strict json_schema
/// mode**: every request includes the full `SteeringConfig` JSON
/// Schema with `strict: true`, and Kimi K2.6 / Gradient enforce the
/// shape via constrained decoding. Missing required fields, wrong
/// types, and out-of-enum values become impossible at the token
/// level. If Gradient ever returns a 400 (e.g. a future model on the
/// catalog doesn't accept the strict variant), the caller flips an
/// internal flag and falls back permanently to plain `json_object`
/// mode — `parse_and_validate` then catches shape errors post-hoc as
/// before. The flag persists for the lifetime of the daemon so we
/// don't pay the failed-request cost every cycle.
pub struct GradientCaller {
    provider: nasrudin_llm::GradientProvider,
    model: String,
    max_completion_tokens: u32,
    max_total_tokens: u32,
    /// Atomic so the fallback can flip without `&mut self`.
    strict_failed: std::sync::atomic::AtomicBool,
}

impl GradientCaller {
    pub fn new(
        provider: nasrudin_llm::GradientProvider,
        model: String,
        max_completion_tokens: u32,
        max_total_tokens: u32,
    ) -> Self {
        let max_total_tokens = std::cmp::max(max_total_tokens, MIN_STEERER_COMPLETION_TOKENS);
        let max_completion_tokens = std::cmp::max(
            std::cmp::min(max_completion_tokens, max_total_tokens),
            MIN_STEERER_COMPLETION_TOKENS,
        );
        Self {
            provider,
            model,
            max_completion_tokens,
            max_total_tokens,
            strict_failed: std::sync::atomic::AtomicBool::new(false),
        }
    }

    /// Build the `SteeringConfig` JSON Schema for strict-mode
    /// requests. Derived via `schemars` from the Rust struct so the
    /// schema stays in sync automatically as fields are added /
    /// renamed. The `extension` field is `#[schemars(skip)]` so it
    /// is absent from this schema — strict mode requires concrete
    /// types and the extension is "any JSON" by design.
    fn steering_config_schema() -> serde_json::Value {
        // schemars 1.x: `Schema` wraps `serde_json::Value` directly; previous
        // 0.8 API exposed an inner `.schema` field that no longer exists.
        let schema = schemars::schema_for!(crate::steerer::schema::SteeringConfig);
        schema.to_value()
    }
}

#[async_trait]
impl LlmCaller for GradientCaller {
    async fn call(
        &self,
        system: &str,
        user: &str,
        max_total_tokens: u32,
    ) -> Result<(String, Option<i32>, Option<i32>), CycleError> {
        use nasrudin_llm::{CompletionRequest, LlmProvider, ResponseFormat};
        let effective_max_total_tokens = std::cmp::min(self.max_total_tokens, max_total_tokens);
        if effective_max_total_tokens < MIN_STEERER_COMPLETION_TOKENS {
            return Err(CycleError::Llm(format!(
                "steerer rolling budget refusal: remaining_total_tokens={} below minimum {}",
                effective_max_total_tokens, MIN_STEERER_COMPLETION_TOKENS
            )));
        }
        let approx_input_tokens = approximate_tokens(system) + approximate_tokens(user);
        let Some(available_completion_tokens) =
            effective_max_total_tokens.checked_sub(approx_input_tokens)
        else {
            return Err(CycleError::Llm(format!(
                "steerer prompt budget refusal: approx_input_tokens={} exceeds max_total_tokens={}",
                approx_input_tokens, effective_max_total_tokens
            )));
        };
        if available_completion_tokens < MIN_STEERER_COMPLETION_TOKENS {
            return Err(CycleError::Llm(format!(
                "steerer prompt budget refusal: approx_input_tokens={} leaves only {} completion tokens below minimum {}",
                approx_input_tokens, available_completion_tokens, MIN_STEERER_COMPLETION_TOKENS
            )));
        }
        let request_max_tokens =
            std::cmp::min(self.max_completion_tokens, available_completion_tokens);

        let response_format = if self
            .strict_failed
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            // We've already learned this provider/model doesn't
            // accept json_schema mode. Stay on the soft path; the
            // post-hoc validator catches shape errors.
            ResponseFormat::Json {
                schema: serde_json::json!({}),
            }
        } else {
            ResponseFormat::JsonSchema {
                name: "SteeringConfig".into(),
                schema: Self::steering_config_schema(),
            }
        };
        let req = CompletionRequest {
            model: self.model.clone(),
            system_prompt: system.to_owned(),
            user_prompt: user.to_owned(),
            max_tokens: request_max_tokens,
            temperature: 0.4,
            stop_sequences: vec![],
            response_format: response_format.clone(),
        };
        match self.provider.complete(req).await {
            Ok(r) => {
                let total_tokens = r.input_tokens.saturating_add(r.output_tokens);
                if total_tokens > effective_max_total_tokens {
                    tracing::warn!(
                        input_tokens = r.input_tokens,
                        output_tokens = r.output_tokens,
                        max_total_tokens = effective_max_total_tokens,
                        "steerer LLM call exceeded configured token budget according to provider usage"
                    );
                }
                Ok((
                    r.text,
                    Some(r.input_tokens as i32),
                    Some(r.output_tokens as i32),
                ))
            }
            Err(e) => {
                // If we tried strict mode and got an HTTP 400, the
                // provider doesn't accept json_schema. Flip the
                // fallback flag and retry once with plain json_object.
                let was_strict = matches!(response_format, ResponseFormat::JsonSchema { .. });
                let is_400 = matches!(&e, nasrudin_llm::LlmError::Http { status: 400, .. });
                if was_strict && is_400 {
                    self.strict_failed
                        .store(true, std::sync::atomic::Ordering::Relaxed);
                    tracing::warn!(
                        error=%e,
                        "Gradient rejected json_schema response_format; \
                         falling back to json_object for the rest of the daemon's lifetime"
                    );
                    let retry_req = CompletionRequest {
                        model: self.model.clone(),
                        system_prompt: system.to_owned(),
                        user_prompt: user.to_owned(),
                        max_tokens: request_max_tokens,
                        temperature: 0.4,
                        stop_sequences: vec![],
                        response_format: ResponseFormat::Json {
                            schema: serde_json::json!({}),
                        },
                    };
                    let r = self
                        .provider
                        .complete(retry_req)
                        .await
                        .map_err(|e2| CycleError::Llm(e2.to_string()))?;
                    let total_tokens = r.input_tokens.saturating_add(r.output_tokens);
                    if total_tokens > effective_max_total_tokens {
                        tracing::warn!(
                            input_tokens = r.input_tokens,
                            output_tokens = r.output_tokens,
                            max_total_tokens = effective_max_total_tokens,
                            "steerer LLM retry exceeded configured token budget according to provider usage"
                        );
                    }
                    Ok((
                        r.text,
                        Some(r.input_tokens as i32),
                        Some(r.output_tokens as i32),
                    ))
                } else {
                    Err(CycleError::Llm(e.to_string()))
                }
            }
        }
    }
}

fn approximate_tokens(s: &str) -> u32 {
    // Conservative enough for budget gating without pulling tokenizer
    // assets into the API hot path. English/JSON prompts are usually
    // around 3-4 chars/token; using 3 overestimates and refuses early.
    ((s.len() as u32).saturating_add(2)) / 3
}

fn llm_strategy_window_max_tokens() -> u32 {
    std::env::var("LLM_STEER_MAX_TOTAL_TOKENS")
        .ok()
        .and_then(|s| s.parse::<u32>().ok())
        .unwrap_or(10_000)
}

fn llm_strategy_budget_window_secs(min_strategy_refresh_interval_secs: Option<i64>) -> i64 {
    let window = std::env::var("LLM_STEER_ROLLING_WINDOW_SECONDS")
        .ok()
        .and_then(|s| s.parse::<i64>().ok())
        .unwrap_or_else(|| min_strategy_refresh_interval_secs.unwrap_or(7_200));
    std::cmp::max(window, 1)
}

fn llm_evidence_gate_enabled() -> bool {
    std::env::var("LLM_STEER_REQUIRE_NEW_EVIDENCE")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true)
}

fn llm_min_cluster_reports_for_refresh() -> u64 {
    std::env::var("LLM_STEER_MIN_CLUSTER_REPORTS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1)
}

fn llm_min_verified_theorems_for_refresh() -> u64 {
    std::env::var("LLM_STEER_MIN_VERIFIED_THEOREMS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0)
}

fn llm_skip_if_rl_confident_enabled() -> bool {
    std::env::var("LLM_STEER_SKIP_IF_RL_CONFIDENT")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true)
}

fn llm_rl_confident_min_reports() -> usize {
    std::env::var("LLM_STEER_RL_CONFIDENT_MIN_REPORTS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(3)
}

fn llm_rl_confident_min_episodes() -> u64 {
    std::env::var("LLM_STEER_RL_CONFIDENT_MIN_EPISODES")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(8)
}

fn llm_rl_confident_min_score() -> f64 {
    std::env::var("LLM_STEER_RL_CONFIDENT_MIN_SCORE")
        .ok()
        .and_then(|s| s.parse::<f64>().ok())
        .unwrap_or(0.45)
}

fn llm_rl_confident_min_lake_pass_rate() -> f64 {
    std::env::var("LLM_STEER_RL_CONFIDENT_MIN_LAKE_PASS_RATE")
        .ok()
        .and_then(|s| s.parse::<f64>().ok())
        .unwrap_or(0.25)
}

async fn recent_rl_policy_evidence_is_confident(
    db: &sea_orm::DatabaseConnection,
    cutoff: DateTime<Utc>,
) -> bool {
    let min_reports = llm_rl_confident_min_reports();
    if min_reports == 0 {
        return false;
    }
    let min_episodes = llm_rl_confident_min_episodes();
    let min_score = llm_rl_confident_min_score();
    let min_lake_pass_rate = llm_rl_confident_min_lake_pass_rate();
    let mut confident_reports = 0usize;
    for &domain in bandit::ISLAND_DOMAINS {
        let Ok(rows) = nasrudin_pg::query::cluster_reports::recent_for_island(db, domain, 8).await
        else {
            continue;
        };
        for row in rows {
            if row.received_at.with_timezone(&Utc) < cutoff {
                continue;
            }
            if rl_policy_evidence_is_confident(
                &row.summary,
                min_episodes,
                min_score,
                min_lake_pass_rate,
            ) {
                confident_reports += 1;
                if confident_reports >= min_reports {
                    return true;
                }
            }
        }
    }
    false
}

fn rl_policy_evidence_is_confident(
    summary: &serde_json::Value,
    min_episodes: u64,
    min_score: f64,
    min_lake_pass_rate: f64,
) -> bool {
    let Some(evidence) = summary.get("rl_policy_evidence") else {
        return false;
    };
    let episodes = evidence
        .get("episodes")
        .and_then(|v| v.as_u64())
        .unwrap_or_default();
    if episodes < min_episodes {
        return false;
    }
    let ga_low_sample = evidence
        .get("ga_policy_low_sample")
        .and_then(|v| v.as_bool())
        .unwrap_or(true);
    let target_low_sample = evidence
        .get("target_policy_low_sample")
        .and_then(|v| v.as_bool())
        .unwrap_or(true);
    if ga_low_sample || target_low_sample {
        return false;
    }
    let ga_score = evidence
        .get("ga_policy_conservative_score")
        .and_then(|v| v.as_f64())
        .unwrap_or(f64::NEG_INFINITY);
    let target_score = evidence
        .get("target_policy_conservative_score")
        .and_then(|v| v.as_f64())
        .unwrap_or(f64::NEG_INFINITY);
    let ga_lake = evidence
        .get("ga_policy_lake_pass_rate")
        .and_then(|v| v.as_f64())
        .unwrap_or(0.0);
    let target_lake = evidence
        .get("target_policy_lake_pass_rate")
        .and_then(|v| v.as_f64())
        .unwrap_or(0.0);
    ga_score >= min_score
        && target_score >= min_score
        && ga_lake >= min_lake_pass_rate
        && target_lake >= min_lake_pass_rate
}

fn strategy_refresh_has_enough_evidence(
    active_paid_count: u64,
    cluster_report_count: u64,
    verified_count: u64,
    min_cluster_reports: u64,
    min_verified_theorems: u64,
) -> bool {
    if active_paid_count > 0 {
        return true;
    }
    if min_cluster_reports == 0 {
        return true;
    }
    if cluster_report_count >= min_cluster_reports {
        return true;
    }
    min_verified_theorems > 0 && verified_count >= min_verified_theorems
}

fn budgeted_call_max_total_tokens(
    used_tokens: i64,
    max_window_tokens: u32,
    approx_input_tokens: u32,
) -> Result<u32, String> {
    if used_tokens < 0 {
        return Ok(max_window_tokens);
    }
    let used = used_tokens as u64;
    let max = max_window_tokens as u64;
    if used >= max {
        return Err(format!(
            "used_tokens {used} >= max_window_tokens {max_window_tokens}"
        ));
    }
    let remaining = std::cmp::min(max - used, u32::MAX as u64) as u32;
    let min_required = approx_input_tokens.saturating_add(MIN_STEERER_COMPLETION_TOKENS);
    if remaining < min_required {
        return Err(format!(
            "remaining_tokens {remaining} < approx_input_tokens {approx_input_tokens} + min_completion_tokens {MIN_STEERER_COMPLETION_TOKENS}"
        ));
    }
    Ok(remaining)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::steerer::schema::default_config;

    #[test]
    fn steering_config_schema_has_required_fields() {
        let schema = GradientCaller::steering_config_schema();
        let s = serde_json::to_string(&schema).unwrap();
        // The strict-mode schema must declare every load-bearing
        // field so the LLM is constrained to emit them.
        for field in [
            "scope",
            "domain_weights",
            "fitness_weights",
            "mutation_knobs",
            "cluster_directives",
            "compute_directives",
            "lessons_learned",
            "rationale",
        ] {
            assert!(
                s.contains(&format!("\"{field}\"")),
                "schema missing field: {field}; full schema: {s}"
            );
        }
        // The cluster action enum must enumerate all four variants.
        for variant in ["boost", "exploit", "diversify", "kill"] {
            assert!(
                s.contains(variant),
                "schema missing ClusterAction::{variant}"
            );
        }
    }

    #[test]
    fn steering_config_schema_skips_extension_field() {
        let schema = GradientCaller::steering_config_schema();
        let s = serde_json::to_string(&schema).unwrap();
        // `extension` is `serde_json::Value` (any JSON), incompatible
        // with strict mode's concrete-types requirement. Skipped from
        // the schema by design — strict guarantees on every other
        // field, extension stays available via soft fallback.
        assert!(
            !s.contains("\"extension\""),
            "extension field must be skipped from strict schema; got {s}"
        );
    }

    #[test]
    fn budgeted_call_allows_remaining_window() {
        let remaining = budgeted_call_max_total_tokens(2_000, 10_000, 1_000).unwrap();
        assert_eq!(remaining, 8_000);
    }

    #[test]
    fn budgeted_call_refuses_full_window() {
        let err = budgeted_call_max_total_tokens(10_000, 10_000, 1).unwrap_err();
        assert!(err.contains("used_tokens 10000"));
    }

    #[test]
    fn budgeted_call_refuses_when_completion_floor_cannot_fit() {
        let err = budgeted_call_max_total_tokens(9_200, 10_000, 400).unwrap_err();
        assert!(err.contains("remaining_tokens 800"));
        assert!(err.contains("min_completion_tokens"));
    }

    #[test]
    fn evidence_gate_requires_worker_signal_by_default() {
        assert!(!strategy_refresh_has_enough_evidence(0, 0, 0, 1, 0));
        assert!(strategy_refresh_has_enough_evidence(0, 1, 0, 1, 0));
    }

    #[test]
    fn evidence_gate_allows_paid_jobs_and_verified_theorem_signal() {
        assert!(strategy_refresh_has_enough_evidence(1, 0, 0, 1, 0));
        assert!(strategy_refresh_has_enough_evidence(0, 0, 2, 10, 2));
    }

    #[test]
    fn evidence_gate_can_be_disabled_by_zero_cluster_report_requirement() {
        assert!(strategy_refresh_has_enough_evidence(0, 0, 0, 0, 0));
    }

    #[test]
    fn rl_policy_evidence_confidence_accepts_sampled_productive_policy() {
        let summary = serde_json::json!({
            "rl_policy_evidence": {
                "episodes": 12,
                "ga_policy_low_sample": false,
                "target_policy_low_sample": false,
                "ga_policy_conservative_score": 0.70,
                "target_policy_conservative_score": 0.62,
                "ga_policy_lake_pass_rate": 0.40,
                "target_policy_lake_pass_rate": 0.35
            }
        });

        assert!(rl_policy_evidence_is_confident(&summary, 8, 0.45, 0.25));
    }

    #[test]
    fn rl_policy_evidence_confidence_rejects_low_sample() {
        let summary = serde_json::json!({
            "rl_policy_evidence": {
                "episodes": 12,
                "ga_policy_low_sample": false,
                "target_policy_low_sample": true,
                "ga_policy_conservative_score": 0.70,
                "target_policy_conservative_score": 0.62,
                "ga_policy_lake_pass_rate": 0.40,
                "target_policy_lake_pass_rate": 0.35
            }
        });

        assert!(!rl_policy_evidence_is_confident(&summary, 8, 0.45, 0.25));
    }

    #[test]
    fn rl_policy_evidence_confidence_requires_both_policy_families() {
        let summary = serde_json::json!({
            "rl_policy_evidence": {
                "episodes": 12,
                "ga_policy_low_sample": false,
                "ga_policy_conservative_score": 0.70,
                "ga_policy_lake_pass_rate": 0.40
            }
        });

        assert!(!rl_policy_evidence_is_confident(&summary, 8, 0.45, 0.25));
    }

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

    /// Acceptance test for the LLM-as-chain-synthesizer wire-up: a
    /// mocked Kimi K2.6 reply carrying a `proposed_chains` map must
    /// round-trip through `parse_and_validate` and emit `Vec<RuleStep>`
    /// values the worker can deserialise. This is the contract surface
    /// between the steerer cycle (this crate) and the worker
    /// (nasrudin-ga). If it breaks, no LLM-curated elites ever reach
    /// the GA.
    #[test]
    fn parse_accepts_proposed_chains_payload() {
        use nasrudin_derive::RuleStep;
        let mut cfg = default_config();
        cfg.proposed_chains.insert(
            "sr_rest_energy".into(),
            vec![
                RuleStep::IntroduceAxiom {
                    axiom_name: "four_momentum_time_component".into(),
                },
                RuleStep::IntroduceAxiom {
                    axiom_name: "minkowski_invariant_def".into(),
                },
                RuleStep::IntroduceAxiom {
                    axiom_name: "invariant_mass_postulate".into(),
                },
                RuleStep::AlgebraicSimplify,
            ],
        );
        let json = serde_json::to_string(&cfg).unwrap();
        // This is exactly the path a Kimi K2.6 reply takes once
        // stripped of any markdown fence: raw JSON → parse_and_validate.
        let parsed = parse_and_validate(&json, "C").expect("must accept proposed_chains");
        assert_eq!(parsed.proposed_chains.len(), 1);
        let chain = parsed
            .proposed_chains
            .get("sr_rest_energy")
            .expect("target key must round-trip");
        assert_eq!(chain.len(), 4);
        // The worker side does `serde_json::from_value::<Vec<RuleStep>>(…)`
        // against `steering.config.proposed_chains[<target>]`. Replay
        // that exact deserialisation here so the test fails loudly the
        // moment the wire shape diverges from the worker's expectation.
        let wire_val = serde_json::to_value(&parsed.proposed_chains).unwrap();
        let entry = wire_val.get("sr_rest_energy").unwrap().clone();
        let steps: Vec<RuleStep> =
            serde_json::from_value(entry).expect("worker-side deserialisation");
        assert!(matches!(steps[0], RuleStep::IntroduceAxiom { .. }));
        assert!(matches!(steps[3], RuleStep::AlgebraicSimplify));
    }

    /// Markdown-fenced JSON is the dominant Kimi K2.6 reply shape — the
    /// strict-mode JSON Schema reduces this but the fallback
    /// `json_object` path still ships fences. Cover the union:
    /// proposed_chains must survive both raw and fenced parses.
    #[test]
    fn parse_accepts_fenced_proposed_chains_payload() {
        use nasrudin_derive::RuleStep;
        let mut cfg = default_config();
        cfg.proposed_chains
            .insert("sr_rest_energy".into(), vec![RuleStep::AlgebraicSimplify]);
        let json = serde_json::to_string(&cfg).unwrap();
        let fenced = format!("```json\n{}\n```", json);
        let parsed = parse_and_validate(&fenced, "C").unwrap();
        assert_eq!(parsed.proposed_chains["sr_rest_energy"].len(), 1);
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
