//! Generic theorem-discovery worker.
//!
//! Pulls axioms + peer-verified theorems from `/api/seed`, runs the
//! chain-based GA over them, lake-verifies promising chains, and POSTs
//! verified results to `/api/ingest`. Multiple workers compound off
//! each other via the platform — every verified theorem becomes a new
//! `IntroduceAxiom`-able building block on the next chunk's seed-sync.
//!
//! No headline result is privileged: the GA evolves chains under a
//! composite fitness (novelty + depth + connectivity) with no target
//! direction by default. If E=mc², photon dispersion, or any other
//! famous identity ever falls out of a chain, the canonical-form
//! audit catches it server-side and Lake verifies it like any other
//! discovery. (Legacy: this binary was previously named `discover_emc2`
//! when the project's first POC was a hand-targeted SR run.)
//!
//! Usage:
//!   worker --domain pure-math                  # patient compute, all axioms
//!   worker --domain sr                         # SR upstream postulates only
//!   worker --verify <prover_root>              # lake-verify top candidates
//!   worker --verify <prover_root> --no-submit  # local verification smoke
//!   worker --gens N --pop M                    # tune scale
//!
//! The driver is designed for *long-horizon* runs. With max_lake_verifications
//! at single digits per run, a fresh invocation usually finishes in seconds
//! (dry) or minutes (with lake). To genuinely *find* E=mc² spontaneously,
//! expect to run for hours-to-days of GA evolution and dozens of lake
//! verifications. This binary is the apparatus for that experiment.
//!
//! ## Phase 9 / Task 7.1
//!
//! Verified discoveries are submitted via HTTP POST to `/api/ingest` on
//! the running `physics-api` daemon, NOT written to disk as
//! `prover/PhysicsGenerator/Derived/Discover*.lean` files. The lake build
//! still writes the .lean file *temporarily* (lake requires a file on
//! disk to compile), but we delete it immediately after successful
//! submission so no `Discover*.lean` files persist on disk going forward.
//!
//! Required env vars:
//!   * `NASRUDIN_WORKER_KEY` — bearer token (`nsk_worker_…`). Required.
//!   * `NASRUDIN_API_URL`    — base URL. Defaults to `http://localhost:3001`.
//!   * `NASRUDIN_WORKER_ID`  — worker handle. Defaults to `in-proc-worker-1`.

use nasrudin_derive::axiom_store::AxiomStore;
use nasrudin_derive::{Chain, RuleStep};
use nasrudin_ga::chain_engine::{DiscoveryConfig, VerifiedDiscovery};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

const DEFAULT_API_URL: &str = "http://localhost:3001";
const DEFAULT_WORKER_ID: &str = "in-proc-worker-1";
const DEFAULT_RL_HALF_LIFE_HOURS: f64 = 168.0;

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct WorkerRlState {
    version: u32,
    scopes: std::collections::BTreeMap<String, WorkerRlScopeState>,
    #[serde(default)]
    target_portfolio: std::collections::BTreeMap<String, TargetPortfolioStats>,
    #[serde(default)]
    target_selector_policies: std::collections::BTreeMap<String, TargetSelectorPolicyStats>,
    #[serde(default)]
    ga_workhorse_policies: std::collections::BTreeMap<String, GaWorkhorsePolicyStats>,
}

#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
struct WorkerRlScopeState {
    #[serde(default)]
    updated_at_unix_secs: i64,
    #[serde(default)]
    corpus_len: usize,
    #[serde(default)]
    mutation_operator: nasrudin_ga::chain_engine::MutationOperatorStats,
    #[serde(default)]
    qd_archive: nasrudin_ga::chain_engine::QdArchiveStats,
    #[serde(default)]
    strategy_genomes: std::collections::BTreeMap<String, StrategyGenomeStats>,
    #[serde(default)]
    replay_elites: Vec<ReplayElite>,
}

#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
struct ReplayElite {
    canonical: String,
    chain: Vec<RuleStep>,
    #[serde(default)]
    added_at_unix_secs: i64,
    #[serde(default)]
    generation: usize,
    #[serde(default)]
    pulls: u32,
    #[serde(default)]
    total_reward: f64,
    #[serde(default)]
    last_reward: f64,
    #[serde(default)]
    best_reward: f64,
    #[serde(default)]
    reward_ema: f64,
    #[serde(default)]
    last_replayed_unix_secs: i64,
}

#[derive(Debug, Clone)]
struct ReplayEliteSelection {
    canonical: String,
    chain: Chain,
}

#[derive(Debug, Clone, serde::Serialize)]
struct WorkerRlEpisode {
    version: u32,
    at_unix_secs: i64,
    scope_key: String,
    domain: String,
    target: Option<String>,
    chunk_index: usize,
    chunks_total: usize,
    corpus_len: usize,
    target_selector_policy: Option<String>,
    ga_policy: String,
    strategy_genome_fingerprint: Option<String>,
    strategy_genome_weight: Option<f64>,
    replay_canonicals: Vec<String>,
    population_size: usize,
    generations: usize,
    mutation_rate: f64,
    crossover_rate: f64,
    tournament_size: usize,
    max_chain_len: usize,
    max_lake_verifications: usize,
    total_candidates: usize,
    unique_executable: usize,
    lake_attempts: usize,
    lake_passed: usize,
    dim_rejected: usize,
    pre_lake_rejected: usize,
    verified_count: usize,
    verified_canonicals: Vec<String>,
    reward: f64,
}

#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
struct StrategyGenomeStats {
    #[serde(default)]
    pulls: u32,
    #[serde(default)]
    total_reward: f64,
    #[serde(default)]
    weight_mean: f64,
    #[serde(default)]
    weight_sigma: f64,
    #[serde(default)]
    last_weight: f64,
    #[serde(default)]
    last_reward: f64,
    #[serde(default)]
    best_reward: f64,
}

#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
struct TargetPortfolioStats {
    #[serde(default)]
    pulls: u32,
    #[serde(default)]
    total_reward: f64,
    #[serde(default)]
    last_reward: f64,
    #[serde(default)]
    best_reward: f64,
    #[serde(default)]
    reward_ema: f64,
    #[serde(default)]
    lake_pass_ema: f64,
    #[serde(default)]
    novelty_ema: f64,
    #[serde(default)]
    failure_streak: u32,
    #[serde(default)]
    proved: bool,
    #[serde(default)]
    last_attempt_unix_secs: i64,
    #[serde(default)]
    corpus_len_at_last_attempt: usize,
}

#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
struct TargetSelectorPolicyStats {
    #[serde(default)]
    pulls: u32,
    #[serde(default)]
    total_reward: f64,
    #[serde(default)]
    last_reward: f64,
    #[serde(default)]
    best_reward: f64,
    #[serde(default)]
    reward_ema: f64,
}

#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
struct GaWorkhorsePolicyStats {
    #[serde(default)]
    pulls: u32,
    #[serde(default)]
    total_reward: f64,
    #[serde(default)]
    last_reward: f64,
    #[serde(default)]
    best_reward: f64,
    #[serde(default)]
    reward_ema: f64,
}

impl Default for WorkerRlState {
    fn default() -> Self {
        Self {
            version: 4,
            scopes: std::collections::BTreeMap::new(),
            target_portfolio: std::collections::BTreeMap::new(),
            target_selector_policies: std::collections::BTreeMap::new(),
            ga_workhorse_policies: std::collections::BTreeMap::new(),
        }
    }
}

#[derive(Debug, Clone, serde::Deserialize)]
struct LegacyWorkerRlState {
    mutation_operator: nasrudin_ga::chain_engine::MutationOperatorStats,
    qd_archive: nasrudin_ga::chain_engine::QdArchiveStats,
}

fn worker_rl_state_path() -> PathBuf {
    if let Ok(path) = std::env::var("NASRUDIN_WORKER_RL_STATE") {
        return PathBuf::from(path);
    }
    if let Ok(path) = std::env::var("NASRUDIN_MUTATION_RL_STATE") {
        return PathBuf::from(path);
    }
    let rocks = nasrudin_ga::corpus_sync::resolve_local_path();
    rocks
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join("worker_rl_state.json")
}

fn worker_rl_episode_log_enabled() -> bool {
    std::env::var("NASRUDIN_RL_EPISODE_LOG")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true)
}

fn worker_rl_episode_log_path(worker_rl_state_path: &Path) -> PathBuf {
    if let Ok(path) = std::env::var("NASRUDIN_RL_EPISODE_LOG_PATH") {
        return PathBuf::from(path);
    }
    worker_rl_state_path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join("worker_rl_episodes.jsonl")
}

fn worker_rl_episode_eval_enabled() -> bool {
    std::env::var("NASRUDIN_RL_EPISODE_EVAL")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true)
}

fn worker_rl_episode_eval_path(worker_rl_state_path: &Path) -> PathBuf {
    if let Ok(path) = std::env::var("NASRUDIN_RL_EPISODE_EVAL_PATH") {
        return PathBuf::from(path);
    }
    worker_rl_state_path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join("worker_rl_episode_eval.json")
}

fn worker_rl_episode_eval_interval_seconds() -> i64 {
    std::env::var("NASRUDIN_RL_EPISODE_EVAL_INTERVAL_SECONDS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1_800)
}

fn worker_rl_episode_eval_min_pulls() -> usize {
    std::env::var("NASRUDIN_RL_EPISODE_EVAL_MIN_PULLS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(3)
}

fn worker_rl_episode_log_max_lines() -> usize {
    std::env::var("NASRUDIN_RL_EPISODE_LOG_MAX_LINES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(100_000)
}

fn path_modified_unix_secs(path: &Path) -> Option<i64> {
    let modified = std::fs::metadata(path).ok()?.modified().ok()?;
    let duration = modified
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    Some(duration.as_secs() as i64)
}

fn maybe_refresh_worker_rl_episode_eval(
    episode_path: &Path,
    worker_rl_state_path: &Path,
    now_unix_secs: i64,
) -> anyhow::Result<Option<nasrudin_ga::rl_episode_eval::EvaluationSnapshot>> {
    if !worker_rl_episode_eval_enabled() {
        return Ok(None);
    }
    let output_path = worker_rl_episode_eval_path(worker_rl_state_path);
    let interval = worker_rl_episode_eval_interval_seconds();
    if interval > 0 {
        if let Some(modified) = path_modified_unix_secs(&output_path) {
            if now_unix_secs.saturating_sub(modified) < interval {
                return Ok(None);
            }
        }
    }
    let snapshot = nasrudin_ga::rl_episode_eval::write_evaluation_snapshot(
        episode_path,
        &output_path,
        rl_half_life_hours().unwrap_or(168.0),
        worker_rl_episode_eval_min_pulls(),
        now_unix_secs,
    )?;
    compact_worker_rl_episode_log(episode_path, worker_rl_episode_log_max_lines())?;
    Ok(Some(snapshot))
}

fn load_worker_rl_episode_eval(
    worker_rl_state_path: &Path,
) -> Option<nasrudin_ga::rl_episode_eval::EvaluationSnapshot> {
    let path = worker_rl_episode_eval_path(worker_rl_state_path);
    let body = std::fs::read_to_string(&path).ok()?;
    serde_json::from_str(&body).ok()
}

fn append_worker_rl_episode(path: &Path, episode: &WorkerRlEpisode) -> anyhow::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)?;
    serde_json::to_writer(&mut file, episode)?;
    use std::io::Write;
    file.write_all(b"\n")?;
    Ok(())
}

fn compact_worker_rl_episode_log(path: &Path, max_lines: usize) -> anyhow::Result<()> {
    if max_lines == 0 || !path.exists() {
        return Ok(());
    }
    let body = std::fs::read_to_string(path)?;
    let lines: Vec<&str> = body
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect();
    if lines.len() <= max_lines {
        return Ok(());
    }
    let keep_from = lines.len().saturating_sub(max_lines);
    let tmp_path = path.with_extension("jsonl.tmp");
    {
        let mut file = std::fs::File::create(&tmp_path)?;
        for line in &lines[keep_from..] {
            use std::io::Write;
            file.write_all(line.as_bytes())?;
            file.write_all(b"\n")?;
        }
        file.sync_all()?;
    }
    std::fs::rename(tmp_path, path)?;
    Ok(())
}

fn resolve_local_catalog_path(prover_root: Option<&Path>) -> Option<PathBuf> {
    if let Ok(path) = std::env::var("NASRUDIN_CATALOG_PATH") {
        let path = PathBuf::from(path);
        if path.exists() {
            return Some(path);
        }
    }
    if let Some(root) = prover_root {
        let path = root.join("../physlean-extract/output/catalog.json");
        if path.exists() {
            return Some(path);
        }
    }
    let local = PathBuf::from("physlean-extract/output/catalog.json");
    if local.exists() { Some(local) } else { None }
}

fn load_worker_rl_state(path: &Path) -> WorkerRlState {
    let Ok(bytes) = std::fs::read(path) else {
        return WorkerRlState::default();
    };
    if let Ok(state) = serde_json::from_slice::<WorkerRlState>(&bytes) {
        return state;
    }
    if let Ok(legacy) = serde_json::from_slice::<LegacyWorkerRlState>(&bytes) {
        let mut state = WorkerRlState::default();
        state.scopes.insert(
            "legacy-global".to_string(),
            WorkerRlScopeState {
                updated_at_unix_secs: 0,
                corpus_len: 0,
                mutation_operator: legacy.mutation_operator,
                qd_archive: legacy.qd_archive,
                strategy_genomes: std::collections::BTreeMap::new(),
                replay_elites: Vec::new(),
            },
        );
        return state;
    }
    if let Ok(stats) =
        serde_json::from_slice::<nasrudin_ga::chain_engine::MutationOperatorStats>(&bytes)
    {
        let mut state = WorkerRlState::default();
        state.scopes.insert(
            "legacy-global".to_string(),
            WorkerRlScopeState {
                updated_at_unix_secs: 0,
                corpus_len: 0,
                mutation_operator: stats,
                qd_archive: nasrudin_ga::chain_engine::QdArchiveStats::default(),
                strategy_genomes: std::collections::BTreeMap::new(),
                replay_elites: Vec::new(),
            },
        );
        return state;
    }
    tracing::warn!(
        path = %path.display(),
        "ignoring corrupt worker RL state"
    );
    WorkerRlState::default()
}

fn save_worker_rl_state(path: &Path, state: &WorkerRlState) -> anyhow::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let tmp = path.with_extension("json.tmp");
    let bytes = serde_json::to_vec_pretty(state)?;
    std::fs::write(&tmp, bytes)?;
    std::fs::rename(&tmp, path)?;
    Ok(())
}

fn worker_rl_scope_key(domain: &str, target_name: Option<&str>) -> String {
    let target = target_name
        .filter(|s| !s.is_empty())
        .unwrap_or("background");
    format!("domain={domain}|target={target}")
}

fn target_portfolio_key(domain: &str, target: &str) -> String {
    format!("domain={domain}|target={target}")
}

fn now_unix_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

fn rl_half_life_hours() -> Option<f64> {
    let h = std::env::var("NASRUDIN_RL_HALF_LIFE_HOURS")
        .ok()
        .and_then(|v| v.parse::<f64>().ok())
        .unwrap_or(DEFAULT_RL_HALF_LIFE_HOURS);
    (h.is_finite() && h > 0.0).then_some(h)
}

fn decay_worker_rl_scope_state(
    scope: &mut WorkerRlScopeState,
    now_secs: i64,
    half_life_hours: Option<f64>,
) {
    let Some(half_life_hours) = half_life_hours else {
        return;
    };
    if scope.updated_at_unix_secs <= 0 || now_secs <= scope.updated_at_unix_secs {
        return;
    }
    let age_hours = (now_secs - scope.updated_at_unix_secs) as f64 / 3600.0;
    let factor = 0.5f64.powf(age_hours / half_life_hours).clamp(0.0, 1.0);
    if factor >= 0.999_999 {
        return;
    }
    apply_worker_rl_decay_factor(scope, factor);
}

fn apply_worker_rl_decay_factor(scope: &mut WorkerRlScopeState, factor: f64) {
    let factor = factor.clamp(0.0, 1.0);
    if factor >= 0.999_999 {
        return;
    }
    for i in 0..scope.mutation_operator.pulls.len() {
        let decayed_pulls = (scope.mutation_operator.pulls[i] as f64 * factor).round() as u32;
        scope.mutation_operator.pulls[i] = decayed_pulls;
        scope.mutation_operator.total_reward[i] *= factor;
        if decayed_pulls == 0 {
            scope.mutation_operator.total_reward[i] = 0.0;
        }
    }
    for cell in &mut scope.qd_archive.cells {
        cell.best_score *= factor;
    }
    scope
        .qd_archive
        .cells
        .retain(|cell| cell.best_score.is_finite() && cell.best_score > 1e-9);
    for stats in scope.strategy_genomes.values_mut() {
        stats.pulls = (stats.pulls as f64 * factor).round() as u32;
        stats.total_reward *= factor;
        if stats.pulls == 0 {
            stats.total_reward = 0.0;
        }
    }
    scope
        .strategy_genomes
        .retain(|_, stats| stats.pulls > 0 && stats.total_reward.is_finite());
}

fn decay_worker_rl_scope_for_corpus_drift(
    scope: &mut WorkerRlScopeState,
    current_corpus_len: usize,
) {
    if scope.corpus_len == 0 || current_corpus_len == 0 || scope.corpus_len == current_corpus_len {
        return;
    }
    let old = scope.corpus_len as f64;
    let new = current_corpus_len as f64;
    let drift_ratio = ((new - old).abs() / old.max(new)).clamp(0.0, 1.0);
    let factor = 0.5f64.powf(drift_ratio * 10.0);
    apply_worker_rl_decay_factor(scope, factor);
}

fn strategy_genome_weight(stats: Option<&StrategyGenomeStats>) -> f64 {
    let Some(stats) = stats else {
        return 1.0;
    };
    if stats.pulls == 0 || !stats.total_reward.is_finite() {
        return 1.0;
    }
    (0.5 + stats.total_reward / stats.pulls as f64).clamp(0.25, 1.75)
}

fn strategy_genome_evo_mean(stats: &StrategyGenomeStats) -> f64 {
    if stats.weight_mean.is_finite() && stats.weight_mean > 0.0 {
        stats.weight_mean.clamp(0.25, 1.75)
    } else {
        strategy_genome_weight(Some(stats))
    }
}

fn strategy_genome_evo_sigma(stats: &StrategyGenomeStats) -> f64 {
    if stats.weight_sigma.is_finite() && stats.weight_sigma > 0.0 {
        stats.weight_sigma.clamp(0.05, 0.50)
    } else {
        0.25
    }
}

fn strategy_genome_eval_prior(
    fingerprint: &str,
    eval_snapshot: Option<&nasrudin_ga::rl_episode_eval::EvaluationSnapshot>,
) -> Option<f64> {
    let snapshot = eval_snapshot?;
    snapshot
        .strategy_genomes
        .iter()
        .find(|row| row.key == fingerprint)
        .map(|row| {
            let score = if row.low_sample {
                row.weighted_mean_reward
            } else {
                row.conservative_score
            };
            (0.5 + score).clamp(0.25, 1.75)
        })
}

fn strategy_genome_select_weight(
    stats: Option<&StrategyGenomeStats>,
    eval_prior: Option<f64>,
) -> f64 {
    let Some(stats) = stats else {
        return eval_prior.unwrap_or(1.0).clamp(0.25, 1.75);
    };
    if stats.pulls == 0 {
        return eval_prior.unwrap_or(1.0).clamp(0.25, 1.75);
    }
    let reward_weight = strategy_genome_weight(Some(stats));
    let mean = strategy_genome_evo_mean(stats);
    let sigma = strategy_genome_evo_sigma(stats);
    // Deterministic antithetic exploration. This gives the worker a
    // tiny local evolution-strategy population over successive chunks
    // without extra randomness, coordination, or LLM calls.
    let perturb = match stats.pulls % 4 {
        0 => 1.0,
        1 => -1.0,
        2 => 0.5,
        _ => -0.5,
    };
    let local_weight = (0.65 * mean + 0.35 * reward_weight + perturb * sigma).clamp(0.25, 1.75);
    if let Some(eval_prior) = eval_prior {
        (0.75 * local_weight + 0.25 * eval_prior.clamp(0.25, 1.75)).clamp(0.25, 1.75)
    } else {
        local_weight
    }
}

fn strategy_genome_update(stats: &mut StrategyGenomeStats, weight: f64, reward: f64) {
    if !reward.is_finite() || !weight.is_finite() {
        return;
    }
    let previous_mean_reward = if stats.pulls > 0 {
        stats.total_reward / stats.pulls as f64
    } else {
        reward
    };
    let mean = strategy_genome_evo_mean(stats);
    let sigma = strategy_genome_evo_sigma(stats);
    let advantage = (reward - previous_mean_reward).clamp(-1.0, 1.0);
    let lr = (0.35 / (stats.pulls.max(1) as f64).sqrt()).clamp(0.03, 0.35);
    let gradient = ((weight - mean) / sigma.max(0.05)).clamp(-2.0, 2.0);
    stats.weight_mean = (mean + lr * advantage * gradient).clamp(0.25, 1.75);
    stats.weight_sigma = if advantage >= 0.0 {
        (sigma * 0.97).clamp(0.05, 0.50)
    } else {
        (sigma * 1.05).clamp(0.05, 0.50)
    };
    stats.last_weight = weight.clamp(0.25, 1.75);
    stats.last_reward = reward.clamp(0.0, 1.0);
    stats.best_reward = stats.best_reward.max(stats.last_reward);
    stats.pulls = stats.pulls.saturating_add(1);
    stats.total_reward += stats.last_reward;
}

fn strategy_genome_reward(report: &nasrudin_ga::chain_engine::DiscoveryReport) -> f64 {
    let pass_rate = if report.lake_attempts > 0 {
        report.lake_passed as f64 / report.lake_attempts as f64
    } else {
        0.0
    };
    let novelty = if report.total_candidates > 0 {
        ((report.unique_executable as f64 / report.total_candidates as f64) * 8.0).clamp(0.0, 1.0)
    } else {
        0.0
    };
    let verified = if report.verified.is_empty() { 0.0 } else { 1.0 };
    (0.2 * novelty + 0.4 * pass_rate + 0.4 * verified).clamp(0.0, 1.0)
}

const FEATURED_TARGETS: &[&str] = &[
    "sr_rest_energy",
    "qm_planck_einstein",
    "qm_schrodinger",
    "thermo_boltzmann_entropy",
    "newton_second",
    "em_gauss_law",
    "gr_einstein_field_equation",
];

fn is_featured_target(target: &str) -> bool {
    FEATURED_TARGETS.contains(&target)
}

fn target_candidates_for_domain(domain: &str) -> Vec<&'static str> {
    match domain {
        "sr" | "special_relativity" => vec!["sr_rest_energy"],
        "qm" | "quantum_mechanics" => vec![
            "qm_planck_einstein",
            "qm_schrodinger",
            "qm_free_particle_dispersion",
            "qm_de_broglie",
            "qm_harmonic_oscillator_levels",
        ],
        "em" | "electromagnetism" => vec!["em_gauss_law"],
        "thermo" | "thermodynamics" => vec!["thermo_boltzmann_entropy", "thermo_carnot"],
        "classical" | "classical_mechanics" => vec!["newton_second"],
        "gr" | "general_relativity" => {
            vec!["gr_einstein_field_equation", "gr_schwarzschild_radius"]
        }
        "pure-math" | "mixed" | "all" => vec![
            "sr_rest_energy",
            "qm_planck_einstein",
            "qm_schrodinger",
            "thermo_boltzmann_entropy",
            "newton_second",
            "em_gauss_law",
            "gr_einstein_field_equation",
            "qm_free_particle_dispersion",
            "qm_de_broglie",
            "qm_harmonic_oscillator_levels",
            "thermo_carnot",
            "gr_schwarzschild_radius",
        ],
        _ => vec![],
    }
}

const TARGET_SELECTOR_POLICIES: [&str; 4] = [
    "verifier_ucb",
    "recent_verifier",
    "novelty_seeker",
    "stall_rescue",
];

fn target_selector_policy_key(domain: &str, policy: &str) -> String {
    format!("domain={domain}|policy={policy}")
}

fn select_target_selector_policy(
    domain: &str,
    stats: &std::collections::BTreeMap<String, TargetSelectorPolicyStats>,
    eval_snapshot: Option<&nasrudin_ga::rl_episode_eval::EvaluationSnapshot>,
) -> &'static str {
    for policy in TARGET_SELECTOR_POLICIES {
        let key = target_selector_policy_key(domain, policy);
        if stats.get(&key).map(|s| s.pulls).unwrap_or(0) == 0 {
            return policy;
        }
    }
    let total_pulls: u32 = TARGET_SELECTOR_POLICIES
        .iter()
        .map(|policy| {
            stats
                .get(&target_selector_policy_key(domain, policy))
                .map(|s| s.pulls)
                .unwrap_or(0)
        })
        .sum();
    let total = (total_pulls.max(1) as f64).ln();
    TARGET_SELECTOR_POLICIES
        .into_iter()
        .max_by(|a, b| {
            let score = |policy: &str| {
                let st = stats.get(&target_selector_policy_key(domain, policy));
                let pulls = st.map(|s| s.pulls).unwrap_or(1).max(1) as f64;
                let mean = st
                    .map(|s| s.total_reward / s.pulls.max(1) as f64)
                    .unwrap_or(0.0);
                let reward_ema = st.map(|s| s.reward_ema).unwrap_or(mean);
                let best = st.map(|s| s.best_reward).unwrap_or(0.0);
                let exploration = (2.0 * total / pulls).sqrt();
                let eval_prior =
                    target_selector_eval_prior(policy, eval_snapshot).unwrap_or(reward_ema);
                0.30 * mean + 0.35 * reward_ema + 0.15 * best + 0.20 * eval_prior + exploration
            };
            score(a)
                .partial_cmp(&score(b))
                .unwrap_or(std::cmp::Ordering::Equal)
        })
        .unwrap_or("verifier_ucb")
}

fn target_selector_eval_prior(
    policy: &str,
    eval_snapshot: Option<&nasrudin_ga::rl_episode_eval::EvaluationSnapshot>,
) -> Option<f64> {
    let snapshot = eval_snapshot?;
    snapshot
        .target_selector_policies
        .iter()
        .find(|row| row.key == policy)
        .map(|row| {
            if row.low_sample {
                row.weighted_mean_reward
            } else {
                row.conservative_score
            }
        })
}

fn update_target_selector_policy(stats: &mut TargetSelectorPolicyStats, reward: f64) {
    let alpha = target_portfolio_ema_alpha();
    let first_pull = stats.pulls == 0;
    stats.pulls = stats.pulls.saturating_add(1);
    stats.total_reward += reward;
    stats.last_reward = reward;
    stats.best_reward = stats.best_reward.max(reward);
    if first_pull {
        stats.reward_ema = reward;
    } else {
        stats.reward_ema = ema(stats.reward_ema, reward, alpha);
    }
}

const GA_WORKHORSE_POLICIES: [&str; 5] = [
    "steady_verify",
    "wide_explore",
    "deep_recombine",
    "mutation_sweep",
    "lake_focus",
];

fn ga_workhorse_policy_key(scope: &str, policy: &str) -> String {
    format!("scope={scope}|policy={policy}")
}

fn select_ga_workhorse_policy(
    scope: &str,
    stats: &std::collections::BTreeMap<String, GaWorkhorsePolicyStats>,
    eval_snapshot: Option<&nasrudin_ga::rl_episode_eval::EvaluationSnapshot>,
) -> &'static str {
    for policy in GA_WORKHORSE_POLICIES {
        let key = ga_workhorse_policy_key(scope, policy);
        if stats.get(&key).map(|s| s.pulls).unwrap_or(0) == 0 {
            return policy;
        }
    }
    let total_pulls: u32 = GA_WORKHORSE_POLICIES
        .iter()
        .map(|policy| {
            stats
                .get(&ga_workhorse_policy_key(scope, policy))
                .map(|s| s.pulls)
                .unwrap_or(0)
        })
        .sum();
    let total = (total_pulls.max(1) as f64).ln();
    GA_WORKHORSE_POLICIES
        .into_iter()
        .max_by(|a, b| {
            let score = |policy: &str| {
                let st = stats.get(&ga_workhorse_policy_key(scope, policy));
                let pulls = st.map(|s| s.pulls).unwrap_or(1).max(1) as f64;
                let mean = st
                    .map(|s| s.total_reward / s.pulls.max(1) as f64)
                    .unwrap_or(0.0);
                let reward_ema = st.map(|s| s.reward_ema).unwrap_or(mean);
                let best = st.map(|s| s.best_reward).unwrap_or(0.0);
                let exploration = (2.0 * total / pulls).sqrt();
                let eval_prior = ga_policy_eval_prior(policy, eval_snapshot).unwrap_or(reward_ema);
                0.25 * mean + 0.40 * reward_ema + 0.15 * best + 0.20 * eval_prior + exploration
            };
            score(a)
                .partial_cmp(&score(b))
                .unwrap_or(std::cmp::Ordering::Equal)
        })
        .unwrap_or("steady_verify")
}

fn ga_policy_eval_prior(
    policy: &str,
    eval_snapshot: Option<&nasrudin_ga::rl_episode_eval::EvaluationSnapshot>,
) -> Option<f64> {
    let snapshot = eval_snapshot?;
    snapshot
        .ga_policies
        .iter()
        .find(|row| row.key == policy)
        .map(|row| {
            if row.low_sample {
                row.weighted_mean_reward
            } else {
                row.conservative_score
            }
        })
}

fn rl_policy_evidence_for_cluster_report(
    ga_policy: &str,
    target_selector_policy: Option<&str>,
    eval_snapshot: Option<&nasrudin_ga::rl_episode_eval::EvaluationSnapshot>,
) -> serde_json::Value {
    let mut evidence = serde_json::Map::new();
    evidence.insert(
        "ga_policy".into(),
        serde_json::Value::String(ga_policy.into()),
    );
    if let Some(policy) = target_selector_policy {
        evidence.insert(
            "target_selector_policy".into(),
            serde_json::Value::String(policy.into()),
        );
    }
    let Some(snapshot) = eval_snapshot else {
        return serde_json::Value::Object(evidence);
    };
    evidence.insert("episodes".into(), serde_json::json!(snapshot.episodes));
    evidence.insert(
        "latest_unix_secs".into(),
        serde_json::json!(snapshot.latest_unix_secs),
    );
    if let Some(row) = snapshot.ga_policies.iter().find(|row| row.key == ga_policy) {
        evidence.insert("ga_policy_pulls".into(), serde_json::json!(row.stats.pulls));
        evidence.insert(
            "ga_policy_weighted_mean_reward".into(),
            serde_json::json!(row.weighted_mean_reward),
        );
        evidence.insert(
            "ga_policy_conservative_score".into(),
            serde_json::json!(row.conservative_score),
        );
        evidence.insert(
            "ga_policy_lake_pass_rate".into(),
            serde_json::json!(row.lake_pass_rate),
        );
        evidence.insert(
            "ga_policy_low_sample".into(),
            serde_json::json!(row.low_sample),
        );
    }
    if let Some(policy) = target_selector_policy {
        if let Some(row) = snapshot
            .target_selector_policies
            .iter()
            .find(|row| row.key == policy)
        {
            evidence.insert(
                "target_policy_pulls".into(),
                serde_json::json!(row.stats.pulls),
            );
            evidence.insert(
                "target_policy_weighted_mean_reward".into(),
                serde_json::json!(row.weighted_mean_reward),
            );
            evidence.insert(
                "target_policy_conservative_score".into(),
                serde_json::json!(row.conservative_score),
            );
            evidence.insert(
                "target_policy_lake_pass_rate".into(),
                serde_json::json!(row.lake_pass_rate),
            );
            evidence.insert(
                "target_policy_low_sample".into(),
                serde_json::json!(row.low_sample),
            );
        }
    }
    serde_json::Value::Object(evidence)
}

fn update_ga_workhorse_policy(stats: &mut GaWorkhorsePolicyStats, reward: f64) {
    let alpha = target_portfolio_ema_alpha();
    let first_pull = stats.pulls == 0;
    stats.pulls = stats.pulls.saturating_add(1);
    stats.total_reward += reward;
    stats.last_reward = reward;
    stats.best_reward = stats.best_reward.max(reward);
    if first_pull {
        stats.reward_ema = reward;
    } else {
        stats.reward_ema = ema(stats.reward_ema, reward, alpha);
    }
}

fn replay_elites_enabled() -> bool {
    std::env::var("NASRUDIN_REPLAY_ELITES")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true)
}

fn replay_elite_archive_limit() -> usize {
    std::env::var("NASRUDIN_REPLAY_ELITE_ARCHIVE_LIMIT")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(16)
        .clamp(1, 128)
}

fn replay_elites_per_chunk() -> usize {
    std::env::var("NASRUDIN_REPLAY_ELITES_PER_CHUNK")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(4)
        .clamp(1, 32)
}

fn replay_elite_selections(scope: &WorkerRlScopeState) -> Vec<ReplayEliteSelection> {
    if !replay_elites_enabled() {
        return Vec::new();
    }
    let total_pulls: u32 = scope.replay_elites.iter().map(|elite| elite.pulls).sum();
    let total = (total_pulls.max(1) as f64).ln();
    let mut scored: Vec<(usize, f64)> = scope
        .replay_elites
        .iter()
        .enumerate()
        .filter(|(_, elite)| !elite.chain.is_empty())
        .map(|(idx, elite)| {
            let score = if elite.pulls == 0 {
                // Try every proof-backed elite at least once before
                // exploiting. Preserve archive recency as a tiny tie-break.
                10_000.0 - idx as f64 * 1e-6
            } else {
                let pulls = elite.pulls.max(1) as f64;
                let mean = elite.total_reward / pulls;
                let exploration = (2.0 * total / pulls).sqrt();
                0.30 * mean + 0.45 * elite.reward_ema + 0.15 * elite.best_reward + exploration
                    - idx as f64 * 1e-6
            };
            (idx, score)
        })
        .collect();
    scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    scored
        .into_iter()
        .take(replay_elites_per_chunk())
        .filter_map(|(idx, _)| scope.replay_elites.get(idx))
        .map(|elite| ReplayEliteSelection {
            canonical: elite.canonical.clone(),
            chain: Chain(elite.chain.clone()),
        })
        .collect()
}

#[cfg(test)]
fn replay_elite_chains(scope: &WorkerRlScopeState) -> Vec<Chain> {
    replay_elite_selections(scope)
        .into_iter()
        .map(|selection| selection.chain)
        .collect()
}

fn update_selected_replay_elites(
    scope: &mut WorkerRlScopeState,
    selections: &[ReplayEliteSelection],
    report: &nasrudin_ga::chain_engine::DiscoveryReport,
    fallback_reward: f64,
    now_unix_secs: i64,
) {
    if selections.is_empty() || !fallback_reward.is_finite() {
        return;
    }
    let alpha = target_portfolio_ema_alpha();
    for selection in selections {
        if let Some(elite) = scope
            .replay_elites
            .iter_mut()
            .find(|elite| elite.canonical == selection.canonical)
        {
            let first_pull = elite.pulls == 0;
            let r = replay_selection_reward(selection, report, fallback_reward);
            elite.pulls = elite.pulls.saturating_add(1);
            elite.total_reward += r;
            elite.last_reward = r;
            elite.best_reward = elite.best_reward.max(r);
            elite.reward_ema = if first_pull {
                r
            } else {
                ema(elite.reward_ema, r, alpha)
            };
            elite.last_replayed_unix_secs = now_unix_secs;
        }
    }
}

fn replay_selection_reward(
    selection: &ReplayEliteSelection,
    report: &nasrudin_ga::chain_engine::DiscoveryReport,
    fallback_reward: f64,
) -> f64 {
    let fallback = fallback_reward.clamp(0.0, 1.0);
    let mut reward = 0.50 * fallback;
    for discovery in &report.verified {
        if discovery.canonical == selection.canonical || discovery.chain.0 == selection.chain.0 {
            reward = reward.max(1.0);
        } else if chain_is_prefix(&selection.chain, &discovery.chain) {
            reward = reward.max(0.90);
        } else if !report.verified.is_empty() {
            reward = reward.max(0.75 * fallback);
        }
    }
    reward.clamp(0.0, 1.0)
}

fn chain_is_prefix(prefix: &Chain, full: &Chain) -> bool {
    !prefix.is_empty()
        && prefix.len() < full.len()
        && full.0.len() >= prefix.0.len()
        && full.0[..prefix.0.len()] == prefix.0[..]
}

fn update_replay_elites_from_verified(
    scope: &mut WorkerRlScopeState,
    report: &nasrudin_ga::chain_engine::DiscoveryReport,
    now_unix_secs: i64,
) -> usize {
    if !replay_elites_enabled() {
        return 0;
    }
    let mut added = 0usize;
    for discovery in &report.verified {
        if discovery.canonical.trim().is_empty() || discovery.chain.is_empty() {
            continue;
        }
        scope
            .replay_elites
            .retain(|elite| elite.canonical != discovery.canonical);
        scope.replay_elites.insert(
            0,
            ReplayElite {
                canonical: discovery.canonical.clone(),
                chain: discovery.chain.0.clone(),
                added_at_unix_secs: now_unix_secs,
                generation: discovery.generation,
                ..Default::default()
            },
        );
        added += 1;
    }
    scope.replay_elites.truncate(replay_elite_archive_limit());
    added
}

fn apply_ga_workhorse_policy(
    cfg: &mut DiscoveryConfig,
    policy: &str,
    base_pop: usize,
    base_max_chain_len: usize,
    base_max_lake: usize,
) {
    match policy {
        "wide_explore" => {
            cfg.population_size = scaled_usize(base_pop, 1.50, 8, 512);
            cfg.mutation_rate = (cfg.mutation_rate + 0.05).clamp(0.05, 0.30);
            cfg.crossover_rate = (cfg.crossover_rate + 0.05).clamp(0.20, 0.90);
        }
        "deep_recombine" => {
            cfg.max_chain_len = base_max_chain_len.saturating_add(4).clamp(4, 24);
            cfg.crossover_rate = (cfg.crossover_rate + 0.15).clamp(0.20, 0.90);
            cfg.mutation_rate = (cfg.mutation_rate - 0.03).clamp(0.05, 0.30);
            cfg.tournament_size = cfg.tournament_size.saturating_add(1).clamp(2, 7);
        }
        "mutation_sweep" => {
            cfg.population_size = scaled_usize(base_pop, 1.20, 8, 512);
            cfg.mutation_rate = (cfg.mutation_rate + 0.10).clamp(0.05, 0.30);
            cfg.crossover_rate = (cfg.crossover_rate - 0.10).clamp(0.20, 0.90);
            cfg.tournament_size = cfg.tournament_size.saturating_sub(1).clamp(2, 7);
        }
        "lake_focus" => {
            cfg.population_size = scaled_usize(base_pop, 0.80, 8, 512);
            cfg.mutation_rate = (cfg.mutation_rate - 0.05).clamp(0.05, 0.30);
            cfg.crossover_rate = (cfg.crossover_rate + 0.05).clamp(0.20, 0.90);
            cfg.max_lake_verifications =
                scaled_usize(base_max_lake.max(1), 1.50, 1, base_max_lake.max(1) * 3);
        }
        _ => {}
    }
}

fn scaled_usize(value: usize, factor: f64, min: usize, max: usize) -> usize {
    ((value as f64 * factor).round() as usize).clamp(min, max.max(min))
}

#[cfg(test)]
fn select_auto_target<'a>(
    domain: &str,
    candidates: &'a [&'static str],
    stats: &std::collections::BTreeMap<String, TargetPortfolioStats>,
    corpus_len: usize,
    now_unix_secs: i64,
) -> Option<&'a str> {
    select_auto_target_with_policy(
        domain,
        candidates,
        stats,
        corpus_len,
        now_unix_secs,
        "verifier_ucb",
        None,
    )
}

fn select_auto_target_with_policy<'a>(
    domain: &str,
    candidates: &'a [&'static str],
    stats: &std::collections::BTreeMap<String, TargetPortfolioStats>,
    corpus_len: usize,
    now_unix_secs: i64,
    policy: &str,
    eval_snapshot: Option<&nasrudin_ga::rl_episode_eval::EvaluationSnapshot>,
) -> Option<&'a str> {
    if candidates.is_empty() {
        return None;
    }
    let unproved_featured: Vec<&'a str> = candidates
        .iter()
        .copied()
        .filter(|candidate| is_featured_target(candidate))
        .filter(|candidate| {
            let key = target_portfolio_key(domain, candidate);
            let st = stats.get(&key);
            !st.map(|s| s.proved).unwrap_or(false) && !stalled_target(st, corpus_len, now_unix_secs)
        })
        .collect();
    if !unproved_featured.is_empty() {
        return select_auto_target_from_pool(
            domain,
            unproved_featured,
            stats,
            policy,
            eval_snapshot,
        );
    }
    let unproved_frontier: Vec<&'a str> = candidates
        .iter()
        .copied()
        .filter(|candidate| !is_featured_target(candidate))
        .filter(|candidate| {
            !stats
                .get(&target_portfolio_key(domain, candidate))
                .map(|s| s.proved)
                .unwrap_or(false)
        })
        .collect();
    if unproved_frontier.is_empty() {
        return None;
    }
    select_auto_target_from_pool(domain, unproved_frontier, stats, policy, eval_snapshot)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AutoTargetCurriculumStatus {
    featured_total: usize,
    featured_proved: usize,
    featured_pending: Vec<&'static str>,
    featured_stalled: Vec<&'static str>,
    frontier_pending: Vec<&'static str>,
}

fn auto_target_curriculum_status(
    domain: &str,
    candidates: &[&'static str],
    stats: &std::collections::BTreeMap<String, TargetPortfolioStats>,
    corpus_len: usize,
    now_unix_secs: i64,
) -> AutoTargetCurriculumStatus {
    let mut featured_total = 0usize;
    let mut featured_proved = 0usize;
    let mut featured_pending = Vec::new();
    let mut featured_stalled = Vec::new();
    let mut frontier_pending = Vec::new();
    for candidate in candidates {
        let key = target_portfolio_key(domain, candidate);
        let st = stats.get(&key);
        let proved = st.map(|s| s.proved).unwrap_or(false);
        if is_featured_target(candidate) {
            featured_total += 1;
            if proved {
                featured_proved += 1;
            } else if stalled_target(st, corpus_len, now_unix_secs) {
                featured_stalled.push(*candidate);
            } else {
                featured_pending.push(*candidate);
            }
        } else if !proved {
            frontier_pending.push(*candidate);
        }
    }
    AutoTargetCurriculumStatus {
        featured_total,
        featured_proved,
        featured_pending,
        featured_stalled,
        frontier_pending,
    }
}

fn stalled_target(
    stats: Option<&TargetPortfolioStats>,
    corpus_len: usize,
    now_unix_secs: i64,
) -> bool {
    let Some(s) = stats else {
        return false;
    };
    if s.failure_streak < target_stall_threshold() {
        return false;
    }
    if s.corpus_len_at_last_attempt != 0 && s.corpus_len_at_last_attempt != corpus_len {
        return false;
    }
    let cooldown = target_stall_retry_after_secs();
    if cooldown == 0 {
        return true;
    }
    let elapsed = now_unix_secs.saturating_sub(s.last_attempt_unix_secs);
    elapsed < cooldown
}

fn target_stall_threshold() -> u32 {
    std::env::var("NASRUDIN_TARGET_RL_STALL_THRESHOLD")
        .ok()
        .and_then(|v| v.parse::<u32>().ok())
        .unwrap_or(5)
        .max(1)
}

fn target_stall_retry_after_secs() -> i64 {
    std::env::var("NASRUDIN_TARGET_RL_STALL_RETRY_SECONDS")
        .ok()
        .and_then(|v| v.parse::<i64>().ok())
        .unwrap_or(86_400)
        .max(0)
}

fn format_target_list(targets: &[&str]) -> String {
    if targets.is_empty() {
        "none".into()
    } else {
        targets.join(", ")
    }
}

fn select_auto_target_from_pool<'a>(
    domain: &str,
    candidates: Vec<&'a str>,
    stats: &std::collections::BTreeMap<String, TargetPortfolioStats>,
    policy: &str,
    eval_snapshot: Option<&nasrudin_ga::rl_episode_eval::EvaluationSnapshot>,
) -> Option<&'a str> {
    for candidate in &candidates {
        let key = target_portfolio_key(domain, candidate);
        if stats.get(&key).map(|s| s.pulls).unwrap_or(0) == 0 {
            return Some(*candidate);
        }
    }
    let total_pulls: u32 = candidates
        .iter()
        .map(|candidate| {
            stats
                .get(&target_portfolio_key(domain, candidate))
                .map(|s| s.pulls)
                .unwrap_or(0)
        })
        .sum();
    let total = (total_pulls.max(1) as f64).ln();
    candidates.into_iter().max_by(|a, b| {
        let score = |target: &str| {
            let key = target_portfolio_key(domain, target);
            let st = stats.get(&key);
            let pulls = st.map(|s| s.pulls).unwrap_or(1).max(1) as f64;
            let mean = st
                .map(|s| s.total_reward / s.pulls.max(1) as f64)
                .unwrap_or(0.0);
            let reward_ema = st.map(|s| s.reward_ema).unwrap_or(mean);
            let lake_pass_ema = st.map(|s| s.lake_pass_ema).unwrap_or(0.0);
            let novelty_ema = st.map(|s| s.novelty_ema).unwrap_or(0.0);
            let best = st.map(|s| s.best_reward).unwrap_or(0.0);
            let failure_streak = st.map(|s| s.failure_streak).unwrap_or(0).min(8) as f64;
            let exploration = (2.0 * total / pulls).sqrt();
            let stall_penalty = 0.07 * failure_streak;
            let eval_prior = target_eval_prior(domain, target, eval_snapshot).unwrap_or(reward_ema);
            match policy {
                "recent_verifier" => {
                    0.15 * mean
                        + 0.35 * reward_ema
                        + 0.30 * lake_pass_ema
                        + 0.10 * eval_prior
                        + 0.10 * best
                        + exploration
                        - stall_penalty
                }
                "novelty_seeker" => {
                    0.15 * mean
                        + 0.20 * reward_ema
                        + 0.15 * lake_pass_ema
                        + 0.35 * novelty_ema
                        + 0.05 * eval_prior
                        + 0.10 * best
                        + exploration
                        - stall_penalty
                }
                "stall_rescue" => {
                    let rescue_bonus = 0.04 * failure_streak;
                    0.20 * mean
                        + 0.25 * reward_ema
                        + 0.20 * lake_pass_ema
                        + 0.15 * novelty_ema
                        + 0.05 * eval_prior
                        + 0.15 * best
                        + exploration
                        + rescue_bonus
                        - 0.02 * failure_streak
                }
                _ => {
                    // Nonstationary verifier-aware UCB. Lifetime mean keeps
                    // useful long-run signal, but recent EMA and Lake pass EMA
                    // dominate so the portfolio reacts when a target becomes
                    // newly productive after corpus/proof-cache drift. The
                    // policy meta-bandit above learns when this default scorer
                    // beats the more exploratory scorer variants.
                    0.25 * mean
                        + 0.30 * reward_ema
                        + 0.20 * lake_pass_ema
                        + 0.10 * novelty_ema
                        + 0.05 * eval_prior
                        + 0.10 * best
                        + exploration
                        - stall_penalty
                }
            }
        };
        score(a)
            .partial_cmp(&score(b))
            .unwrap_or(std::cmp::Ordering::Equal)
    })
}

fn target_eval_prior(
    domain: &str,
    target: &str,
    eval_snapshot: Option<&nasrudin_ga::rl_episode_eval::EvaluationSnapshot>,
) -> Option<f64> {
    let snapshot = eval_snapshot?;
    let key = format!("{domain}:{target}");
    snapshot
        .domain_targets
        .iter()
        .find(|row| row.key == key)
        .map(|row| {
            if row.low_sample {
                row.weighted_mean_reward
            } else {
                row.conservative_score
            }
            .clamp(0.0, 1.0)
        })
}

fn update_target_portfolio(
    stats: &mut TargetPortfolioStats,
    target_name: &str,
    report: &nasrudin_ga::chain_engine::DiscoveryReport,
    corpus_len: usize,
    now_unix_secs: i64,
) {
    let reward = strategy_genome_reward(report);
    let alpha = target_portfolio_ema_alpha();
    let pass_rate = if report.lake_attempts > 0 {
        report.lake_passed as f64 / report.lake_attempts as f64
    } else {
        0.0
    };
    let novelty = if report.total_candidates > 0 {
        report.unique_executable as f64 / report.total_candidates as f64
    } else {
        0.0
    }
    .clamp(0.0, 1.0);
    let first_pull = stats.pulls == 0;
    stats.last_attempt_unix_secs = now_unix_secs;
    stats.corpus_len_at_last_attempt = corpus_len;
    stats.pulls = stats.pulls.saturating_add(1);
    stats.total_reward += reward;
    stats.last_reward = reward;
    stats.best_reward = stats.best_reward.max(reward);
    if target_was_verified(target_name, report) {
        stats.proved = true;
    }
    if first_pull {
        stats.reward_ema = reward;
        stats.lake_pass_ema = pass_rate;
        stats.novelty_ema = novelty;
    } else {
        stats.reward_ema = ema(stats.reward_ema, reward, alpha);
        stats.lake_pass_ema = ema(stats.lake_pass_ema, pass_rate, alpha);
        stats.novelty_ema = ema(stats.novelty_ema, novelty, alpha);
    }
    if report.lake_passed > 0 || !report.verified.is_empty() {
        stats.failure_streak = 0;
    } else {
        stats.failure_streak = stats.failure_streak.saturating_add(1);
    }
}

fn target_was_verified(
    target_name: &str,
    report: &nasrudin_ga::chain_engine::DiscoveryReport,
) -> bool {
    let Some(spec) = nasrudin_ga::target::TargetSpec::lookup(target_name) else {
        return false;
    };
    let target_canonical = spec.final_target.to_canonical();
    report.verified.iter().any(|discovery| {
        discovery.canonical == target_canonical
            || discovery.final_expr.to_canonical() == target_canonical
            || nasrudin_ga::target::shape_similarity(&discovery.final_expr, &spec.final_target)
                >= 0.999
    })
}

fn target_portfolio_ema_alpha() -> f64 {
    std::env::var("NASRUDIN_TARGET_RL_EMA_ALPHA")
        .ok()
        .and_then(|v| v.parse::<f64>().ok())
        .unwrap_or(0.30)
        .clamp(0.05, 1.0)
}

fn ema(prev: f64, next: f64, alpha: f64) -> f64 {
    alpha * next + (1.0 - alpha) * prev
}

#[tokio::main]
async fn main() {
    // Pin rustls 0.23's CryptoProvider before any TLS handshake. With both
    // aws-lc-rs and ring features active in the dep tree (via fastembed →
    // ort + reqwest), rustls panics at first TLS use unless one is
    // explicitly installed. Idempotent — silently no-ops on re-call.
    let _ = rustls::crypto::aws_lc_rs::default_provider().install_default();

    let args: Vec<String> = std::env::args().collect();

    let gens: usize = arg_value(&args, "--gens").unwrap_or(50);
    let pop: usize = arg_value(&args, "--pop").unwrap_or(32);
    let max_chain_len: usize = arg_value(&args, "--max-len").unwrap_or(12);
    let max_lake: usize = arg_value(&args, "--max-lake").unwrap_or(3);
    let research_mode: bool = args.iter().any(|a| a == "--research-mode")
        || std::env::var("NASRUDIN_RESEARCH_MODE")
            .map(|v| matches!(v.trim().to_lowercase().as_str(), "1" | "true" | "yes"))
            .unwrap_or(false);
    // Paid Researcher tier ($19/mo) — distinct from --research-mode.
    // **Default: ON.** Volunteers running a vanilla worker contribute
    // to paid-conjecture compute by default; the platform is sustained
    // by paying customers, so untargeted spare capacity should pick
    // up paid load whenever the queue has any. Opt out with
    // `--no-paid-jobs` (or `NASRUDIN_NO_PAID_JOBS=1`) if you want
    // your worker to do background research only.
    //
    // The 96 slot-hour quota per job + the cluster's 10% explorer
    // floor mean a vanilla worker still spends most of its compute
    // on background research even with this on; paid claims are
    // gated server-side so they can never starve the explorer fleet.
    let opt_out_paid: bool = args.iter().any(|a| a == "--no-paid-jobs")
        || std::env::var("NASRUDIN_NO_PAID_JOBS")
            .map(|v| matches!(v.trim().to_lowercase().as_str(), "1" | "true" | "yes"))
            .unwrap_or(false);
    // Legacy explicit-on flag is still honored (no-op if opt-out is
    // also set — opt-out wins).
    let _legacy_paid_on: bool = args.iter().any(|a| a == "--paid-jobs-mode")
        || std::env::var("NASRUDIN_PAID_JOBS_MODE")
            .map(|v| matches!(v.trim().to_lowercase().as_str(), "1" | "true" | "yes"))
            .unwrap_or(false);
    let paid_jobs_mode: bool = !opt_out_paid;
    // P-Task 11/12: `--no-local-lake` is a DEV-ONLY mode that submits
    // candidate chains *without* first running local lake verification.
    // The production architecture requires workers to lake-build
    // locally — only chains the kernel accepts get submitted, marked
    // `worker_verified: true`, and the server immediately publishes
    // them as peer-axioms (a cheap chain-replay sybil firewall is the
    // only server-side check; lazy lake-build on download is
    // defense-in-depth). This makes 99.9%+ of submissions correct
    // without losing GA novelty: the kernel judges every chain.
    //
    // Use --no-local-lake only for development or when intentionally
    // experimenting with the unverified-submission flow.
    let no_local_lake: bool = args.iter().any(|a| a == "--no-local-lake")
        || std::env::var("NASRUDIN_NO_LOCAL_LAKE")
            .map(|v| matches!(v.trim().to_lowercase().as_str(), "1" | "true" | "yes"))
            .unwrap_or(false);
    if no_local_lake {
        eprintln!(
            "⚠ --no-local-lake is a DEV-ONLY mode. Production workers MUST lake-build locally."
        );
        eprintln!("  Submissions in this mode are flagged worker_verified=false; the server's");
        eprintln!("  lazy lake-promotion drain handles kernel confirmation, which is slower");
        eprintln!("  and may produce cascade-rejects on bogus chains.");
    }
    // Default to 4 unverified candidates per gen, regardless of whether
    // local Lake verification is on. The server-side chain-replay
    // drain handles fast verification (microseconds via the
    // pre-loaded Mathlib elaborator) and the lake-promotion drain
    // handles kernel confirmation lazily. Decoupling the two means a
    // worker can emit cheap discoveries while ALSO running the slow
    // local-Lake path on its top-fitness picks — they no longer
    // compete for the same budget. Local lake stays the verification
    // backbone for "definitely-kernel-checked" status; the unverified
    // stream feeds the discovery rate at 50–100× the per-chunk
    // throughput. Override with `--submit-top-k 0` or
    // `NASRUDIN_SUBMIT_TOP_K=0` for the legacy "lake-only emit" mode.
    let submit_top_k: usize = arg_value(&args, "--submit-top-k")
        .or_else(|| {
            std::env::var("NASRUDIN_SUBMIT_TOP_K")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
        })
        .unwrap_or(4);
    let prover_root: Option<PathBuf> = args
        .iter()
        .position(|a| a == "--verify")
        .and_then(|pos| args.get(pos + 1))
        .map(PathBuf::from);
    let no_submit: bool = args.iter().any(|a| a == "--no-submit")
        || std::env::var("NASRUDIN_NO_SUBMIT")
            .map(|v| {
                matches!(
                    v.trim().to_lowercase().as_str(),
                    "1" | "true" | "yes" | "on"
                )
            })
            .unwrap_or(false);
    let domain: String = args
        .iter()
        .position(|a| a == "--domain")
        .and_then(|pos| args.get(pos + 1).cloned())
        .unwrap_or_else(|| "sr".to_string());

    println!("═══════════════════════════════════════════════════════");
    println!("  Nasrudin Spontaneous Physics Discovery — domain={domain}");
    println!("  No headline-result strategies. No headline axioms.");
    println!("  Pure combinatorics + GA over upstream postulates.");
    if research_mode {
        println!("  ▶ research-mode ON — will poll /api/conjecture/claim");
    }
    println!("═══════════════════════════════════════════════════════");
    println!();

    // ── Resolve API submission config (Task 7.1) ─────────────────────
    // Worker key is REQUIRED only if verified discoveries will be
    // submitted. `--no-submit` is the local-machine smoke path: run
    // the GA and local Lean verification without an API daemon or key.
    let api_cfg = if prover_root.is_some() && !no_submit {
        match ApiSubmitConfig::from_env() {
            Ok(cfg) => {
                println!("▶ API submission target: {}", cfg.api_url);
                println!("    worker_id: {}", cfg.worker_id);
                Some(cfg)
            }
            Err(msg) => {
                eprintln!("✗ {msg}");
                eprintln!("  Set NASRUDIN_WORKER_KEY=nsk_worker_… to enable submission, or");
                eprintln!("  drop the --verify flag for a dry run.");
                std::process::exit(2);
            }
        }
    } else {
        if prover_root.is_some() && no_submit {
            println!("▶ Local verification only (--no-submit): API submission disabled");
        }
        None
    };
    println!();

    // ── Background heartbeat to /api/workers/heartbeat ───────────────
    //
    // Spawned BEFORE corpus hydration, axiom dump, Lean elaborator
    // bringup, and chunk loop so a worker shows `Active` on
    // /api/workers within seconds of process start — not minutes
    // after corpus enumeration completes. Without this, a contributor
    // running the worker on a spare laptop sees "Inactive" for the
    // entire warm-up window and assumes the worker is broken.
    //
    // The first heartbeat lands immediately (no skipped tick). After
    // each successful POST we wait the full 30 s tick; on any error we
    // back off to 10 s so a transient network failure can't push us
    // past the API's 180 s stale window.
    //
    // Counters are cumulative; the chunk loop `fetch_add`s them after
    // each completed chunk — so the API surfaces real-time progress
    // even when a single Lake build takes 10+ minutes.
    let hb_gen = Arc::new(AtomicU64::new(0));
    let hb_thms = Arc::new(AtomicU64::new(0));
    let started_at = Instant::now();
    if let Some(cfg) = api_cfg.as_ref() {
        let api_url_for_hb = cfg.api_url.clone();
        let worker_id_for_hb = cfg.worker_id.clone();
        let worker_key_for_hb = cfg.worker_key.clone();
        let hb_gen_task = Arc::clone(&hb_gen);
        let hb_thms_task = Arc::clone(&hb_thms);
        match nasrudin_ga::worker_http::WorkerHttp::from_env(&api_url_for_hb) {
            Ok(http) => {
                tokio::spawn(async move {
                    let auth = format!("Bearer {worker_key_for_hb}");
                    let git_sha = option_env!("VERGEN_GIT_SHA").unwrap_or("unknown");
                    let mut consecutive_failures: u32 = 0;
                    loop {
                        let body = serde_json::json!({
                            "worker_id": worker_id_for_hb,
                            "current_generation":
                                hb_gen_task.load(Ordering::Relaxed) as i64,
                            "theorems_produced_total":
                                hb_thms_task.load(Ordering::Relaxed) as i64,
                            "uptime_seconds": started_at.elapsed().as_secs() as i64,
                            "engine_git_sha": git_sha,
                        });
                        match http
                            .post_json::<_, serde_json::Value>(
                                "/api/workers/heartbeat",
                                &body,
                                &[("authorization", auth.as_str())],
                            )
                            .await
                        {
                            Ok((status, _)) if (200..300).contains(&status) => {
                                consecutive_failures = 0;
                                tracing::debug!(status, "heartbeat ok");
                            }
                            Ok((status, body)) => {
                                consecutive_failures = consecutive_failures.saturating_add(1);
                                tracing::warn!(
                                    status,
                                    body = %body,
                                    failures = consecutive_failures,
                                    "heartbeat non-2xx"
                                );
                            }
                            Err(e) => {
                                consecutive_failures = consecutive_failures.saturating_add(1);
                                tracing::warn!(
                                    error = %e,
                                    failures = consecutive_failures,
                                    "heartbeat post failed"
                                );
                            }
                        }
                        let sleep = if consecutive_failures > 0 {
                            Duration::from_secs(10)
                        } else {
                            Duration::from_secs(30)
                        };
                        tokio::time::sleep(sleep).await;
                    }
                });
                println!(
                    "▶ Heartbeat task running: POST /api/workers/heartbeat (30 s tick, 10 s backoff on failure)"
                );
                println!();
            }
            Err(e) => {
                eprintln!(
                    "  ! heartbeat client build failed: {e}; worker will appear Inactive on /api/workers"
                );
            }
        }
    }

    // ── Local cold-tier corpus boot ─────────────────────────────────
    //
    // Open a worker-local RocksDB at $NASRUDIN_WORKER_ROCKS (defaults
    // to ~/.local/share/nasrudin-worker/rocks). On first boot the
    // local corpus is empty; we hydrate from `/api/corpus/dump`
    // (~150 MB streamed NDJSON, ~30 s on a typical home connection).
    // Subsequent boots see a populated cold tier and skip the dump.
    //
    // This is the load-bearing change for Pi-class workers (1 GB RAM):
    // the previous in-memory AxiomStore::new() + seed-sync path would
    // OOM trying to fit the ~195k Mathlib corpus into a HashMap. With
    // the cold tier, the worker's resident RAM stays bounded by the
    // RocksDB block cache (64 MB on a Pi) + LRU (~5 MB).
    //
    // Opt out for tests / minimal dev runs with NASRUDIN_WORKER_NO_CORPUS=1
    // — the worker falls back to a hot-only AxiomStore (the GA's
    // `IntroduceAxiom` pool shrinks to the hand-coded postulates +
    // peer-verified theorems from /api/seed, which is fine for sr/em
    // domains but cripples pure-math).
    let no_corpus: bool = std::env::var("NASRUDIN_WORKER_NO_CORPUS")
        .map(|v| matches!(v.trim().to_lowercase().as_str(), "1" | "true" | "yes"))
        .unwrap_or(false);

    let mut store = if no_corpus {
        println!("▶ Worker cold-tier corpus DISABLED (NASRUDIN_WORKER_NO_CORPUS=1)");
        println!("    GA will run on hand-coded postulates + peer-verified theorems only.");
        println!();
        AxiomStore::new()
    } else {
        let rocks_path = nasrudin_ga::corpus_sync::resolve_local_path();
        println!("▶ Worker corpus path: {}", rocks_path.display());
        match nasrudin_ga::corpus_sync::open_local(&rocks_path) {
            Ok(corpus) => {
                use nasrudin_rocks::CorpusBackend;
                let initial_count = corpus.count().unwrap_or(0);
                if initial_count == 0 {
                    let api_url_for_hydrate = std::env::var("NASRUDIN_API_URL")
                        .ok()
                        .or_else(|| api_cfg.as_ref().map(|c| c.api_url.clone()))
                        .unwrap_or_else(|| DEFAULT_API_URL.to_string());
                    let worker_key = api_cfg
                        .as_ref()
                        .map(|c| c.worker_key.clone())
                        .unwrap_or_default();
                    println!(
                        "▶ Worker cold-tier corpus is empty — hydrating from {api_url_for_hydrate} (~150 MB stream)..."
                    );
                    match nasrudin_ga::corpus_sync::hydrate_from_server(
                        &corpus,
                        &api_url_for_hydrate,
                        &worker_key,
                    )
                    .await
                    {
                        Ok(n) => println!("    ✓ corpus hydrated: {n} axioms"),
                        Err(e) => {
                            eprintln!(
                                "    ! corpus hydration failed: {e}\n    Worker will run on hand-coded postulates only this session.\n    Re-run with the API reachable to populate the local corpus."
                            );
                        }
                    }
                } else {
                    println!("▶ Worker cold-tier corpus already populated: {initial_count} axioms");
                }
                let count_after = corpus.count().unwrap_or(0);
                if count_after > 0 {
                    let cold: std::sync::Arc<dyn nasrudin_rocks::CorpusBackend> =
                        std::sync::Arc::new(corpus);
                    AxiomStore::with_corpus(cold)
                } else {
                    AxiomStore::new()
                }
            }
            Err(e) => {
                eprintln!(
                    "    ! failed to open worker RocksDB at {}: {e}",
                    rocks_path.display()
                );
                eprintln!("      Falling back to hot-only AxiomStore for this session.");
                AxiomStore::new()
            }
        }
    };
    println!();

    let load_catalog = std::env::var("NASRUDIN_WORKER_LOAD_CATALOG")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true);
    if load_catalog {
        match resolve_local_catalog_path(prover_root.as_deref()) {
            Some(path) => {
                let forbidden: std::collections::HashSet<String> =
                    nasrudin_derive::no_cheat_audit::forbidden_canonical_statements()
                        .into_iter()
                        .map(|(_, canonical)| canonical)
                        .collect();
                match store.load_from_catalog_filtered(&path, |axiom| {
                    let direct = axiom.statement.to_canonical();
                    let peeled =
                        nasrudin_derive::axiom_store::eq_canonical_under_pi(&axiom.statement);
                    nasrudin_derive::axiom_store::is_propositional(&axiom.statement)
                        && !forbidden.contains(&direct)
                        && peeled
                            .as_ref()
                            .map(|canonical| !forbidden.contains(canonical))
                            .unwrap_or(true)
                }) {
                    Ok((loaded, skipped)) => println!(
                        "▶ Dynamic PhysLean catalog load: +{loaded} hot-tier axioms, {skipped} skipped from {}",
                        path.display()
                    ),
                    Err(e) => eprintln!(
                        "  ! dynamic PhysLean catalog load failed from {}: {e}",
                        path.display()
                    ),
                }
            }
            None => {
                println!("▶ Dynamic PhysLean catalog load skipped: no local catalog.json found")
            }
        }
    } else {
        println!("▶ Dynamic PhysLean catalog load DISABLED (NASRUDIN_WORKER_LOAD_CATALOG=0)");
    }
    println!();

    // Always load the classical-mechanics postulate set: every domain's
    // ladder benefits from kinematic primitives (momentum, work, KE).
    // The chain firewall on the API side has the same postulates loaded
    // so server-side replay accepts them.
    store.load_classical_mechanics_postulates();
    let forbidden_axiom = match domain.as_str() {
        "sr" => {
            store.load_special_relativity_upstream();
            "mass_shell_condition"
        }
        "em" => {
            store.load_electromagnetism_upstream();
            // EM has no single "headline-as-axiom" forbidden name in
            // the upstream encoding, but we sanity-check none of the
            // post-derivation results leaked in.
            "photon_energy_momentum_relation"
        }
        "qm" => {
            store.load_quantum_mechanics_postulates();
            // The first local QM smoke target is Planck-Einstein.
            // The current known-good chain uses the upstream EM photon
            // energy relation as its algebraic substrate while the
            // QM postulate set supplies the broader domain context.
            store.load_electromagnetism_upstream();
            ""
        }
        // "Patient compute" mode: load every domain's postulates and
        // pull the full Mathlib corpus from /api/seed. No target. The
        // GA explores the full axiom + theorem space; if E=mc² (or
        // any other headline) ever falls out of a chain, the canonical
        // audit catches it server-side and Lake verifies it. Nothing
        // is "directed" — composite fitness = novelty + depth +
        // connectivity only (target_shape and ladder_progress are
        // zero without a TargetSpec).
        "pure-math" | "mixed" | "all" => {
            store.load_special_relativity_upstream();
            store.load_electromagnetism_upstream();
            store.load_quantum_mechanics_postulates();
            // forbidden-axiom-by-name is moot here since we register
            // multiple domains; the canonical audit (audit_or_panic)
            // is the load-bearing check below.
            ""
        }
        other => {
            eprintln!("✗ unknown domain `{other}` (try `sr`, `em`, `qm`, or `pure-math`)");
            std::process::exit(2);
        }
    };

    // Print a sample of axiom names for visual confirmation. The full
    // corpus on prod is ~195k entries (Mathlib + PhysLean + classical/SR
    // postulates) — listing each one produces ~10 MB of journal traffic
    // and blocks the boot sequence for several minutes on a 1 vCPU box,
    // which delays the heartbeat task that surfaces the worker as
    // `Active` on /api/workers. Sample is enough for the no-cheat audit
    // sanity-check; the full set is queryable by intent via the API.
    let total = store.len();
    let names: Vec<String> = store.names().iter().cloned().collect();
    let preview: Vec<&String> = names.iter().take(10).collect();
    println!("▶ Upstream axiom set ({total} axioms):");
    for name in &preview {
        println!("    • {name}");
    }
    if total > preview.len() {
        println!(
            "    … ({} more, full set in cold-tier RocksDB)",
            total - preview.len()
        );
    }
    println!();

    if !forbidden_axiom.is_empty() {
        if store.get(forbidden_axiom).is_some() {
            eprintln!("✗ FAIL: {forbidden_axiom} leaked into the store. Cheating.");
            std::process::exit(2);
        }
        println!("  ✓ {forbidden_axiom} is NOT in the store. No cheating.");
    }

    // Canonical-form audit: even if the forbidden name doesn't appear,
    // a smuggler could register E=mc² under a different name. Hash-match
    // every axiom's canonical statement against the headline deny-list.
    nasrudin_derive::no_cheat_audit::audit_or_panic(&store, "worker startup");
    println!("  ✓ no-cheat canonical-form audit passed");
    println!();

    // ── Seed-sync from peers via /api/seed ───────────────────────────
    // Pull what other workers have already verified for this domain and
    // fold it into the local AxiomStore. Each peer-verified theorem
    // becomes a synthetic axiom keyed `theorem_<hex>` that the GA can
    // pick up via RuleStep::IntroduceAxiom — workers compound off each
    // other instead of redoing each others' searches from scratch.
    if let Some(api_url) = std::env::var("NASRUDIN_API_URL")
        .ok()
        .or_else(|| api_cfg.as_ref().map(|c| c.api_url.clone()))
    {
        let domain_param = match domain.as_str() {
            "sr" => "SpecialRelativity",
            "em" => "Electromagnetism",
            "qm" => "QuantumMechanics",
            // pure-math/mixed/all: empty filter → /api/seed returns
            // axioms from every domain, so the worker's GA can compose
            // SR + EM + classical + Mathlib lemmas in a single chain.
            _ => "",
        };
        match fetch_and_extend_store(&api_url, domain_param, &mut store).await {
            Ok((axioms_added, theorems_added, _initial_steering)) => {
                println!(
                    "▶ Seed-sync from {api_url}: +{axioms_added} new axioms, \
                     +{theorems_added} peer theorems folded into store"
                );
                println!("    store size now: {} entries", store.len());
                // Re-check the no-cheating invariant after the fold-in:
                // a peer theorem must not equal the forbidden headline,
                // either by name OR by canonical form. The canonical
                // audit is the load-bearing one — it catches a peer
                // theorem registered as `peer_<hash>` whose statement
                // happens to be E=mc².
                if !forbidden_axiom.is_empty() && store.get(forbidden_axiom).is_some() {
                    eprintln!("✗ FAIL: peer-fed `{forbidden_axiom}` after seed-sync. Refusing.");
                    std::process::exit(2);
                }
                nasrudin_derive::no_cheat_audit::audit_or_panic(&store, "worker post-seed-sync");
            }
            Err(e) => {
                eprintln!(
                    "  ! seed-sync skipped: {e}\n    (worker will run with local axioms only)"
                );
            }
        }
        println!();
    }

    let worker_rl_state_path = worker_rl_state_path();
    let mut worker_rl_state = load_worker_rl_state(&worker_rl_state_path);
    let mut worker_rl_eval_snapshot = load_worker_rl_episode_eval(&worker_rl_state_path);

    // Resolve target: --target sr_rest_energy is the canonical first POC.
    // The shape itself is *not* added to the AxiomStore — it's metadata
    // used to bias the search via target_shape + ladder_progress fitness.
    // The no-cheat audit confirms this invariant at boot.
    let requested_target = std::env::args()
        .skip_while(|a| a != "--target")
        .nth(1)
        .or_else(|| std::env::var("NASRUDIN_TARGET").ok());
    let auto_targets = requested_target.as_deref() == Some("auto")
        || std::env::var("NASRUDIN_AUTO_TARGETS")
            .map(|v| {
                !matches!(
                    v.trim().to_lowercase().as_str(),
                    "0" | "false" | "no" | "off"
                )
            })
            .unwrap_or(false);
    let mut active_target_selector_policy: Option<String> = None;
    let target_name = if auto_targets {
        let candidates = target_candidates_for_domain(&domain);
        let target_now = now_unix_secs();
        let target_corpus_len = store.len();
        let selector_policy = select_target_selector_policy(
            &domain,
            &worker_rl_state.target_selector_policies,
            worker_rl_eval_snapshot.as_ref(),
        );
        let curriculum = auto_target_curriculum_status(
            &domain,
            &candidates,
            &worker_rl_state.target_portfolio,
            target_corpus_len,
            target_now,
        );
        println!(
            "▶ Auto-target curriculum: featured {}/{} proved; pending featured: {}; stalled featured: {}; pending frontier: {}",
            curriculum.featured_proved,
            curriculum.featured_total,
            format_target_list(&curriculum.featured_pending),
            format_target_list(&curriculum.featured_stalled),
            format_target_list(&curriculum.frontier_pending),
        );
        match select_auto_target_with_policy(
            &domain,
            &candidates,
            &worker_rl_state.target_portfolio,
            target_corpus_len,
            target_now,
            selector_policy,
            worker_rl_eval_snapshot.as_ref(),
        ) {
            Some(name) => {
                active_target_selector_policy = Some(selector_policy.to_string());
                println!(
                    "▶ Auto-target RL selected `{name}` from {} candidates for domain={domain} policy={selector_policy}",
                    candidates.len(),
                );
                name.to_string()
            }
            None => {
                println!(
                    "▶ Auto-target curriculum exhausted for domain={domain}; running untargeted novelty search"
                );
                String::new()
            }
        }
    } else {
        requested_target.unwrap_or_else(|| match domain.as_str() {
            "sr" => "sr_rest_energy".into(),
            "qm" => "qm_planck_einstein".into(),
            _ => String::new(),
        })
    };
    let target_spec = if target_name.is_empty() {
        None
    } else {
        match nasrudin_ga::target::TargetSpec::lookup(&target_name) {
            Some(spec) => {
                println!(
                    "▶ Target: {} (ladder of {} rungs)",
                    spec.name,
                    spec.ladder.len()
                );
                Some(spec)
            }
            None => {
                eprintln!(
                    "✗ Unknown target spec `{target_name}`. Available: {}",
                    nasrudin_ga::target::TargetSpec::all_names().join(", ")
                );
                std::process::exit(2);
            }
        }
    };

    // Pull the cluster's rejected-canonicals memo. Any chain whose
    // final canonical matches one of these has already been
    // lake-rejected by *some* worker; no point burning lake cycles to
    // re-confirm. Soft-fail on network error — single-worker dev runs
    // still work without the API.
    let rejected_canonicals: std::sync::Arc<std::collections::HashSet<Vec<u8>>> = {
        let api_url = std::env::var("NASRUDIN_API_URL").ok();
        if let Some(url) = api_url {
            match fetch_rejected_canonicals(&url).await {
                Ok(set) => {
                    println!(
                        "▶ Negative-result memo: {} pre-rejected canonicals will be skipped",
                        set.len()
                    );
                    std::sync::Arc::new(set)
                }
                Err(e) => {
                    eprintln!(
                        "  ! rejected-hashes fetch failed: {e}; running without negative memo"
                    );
                    std::sync::Arc::new(std::collections::HashSet::new())
                }
            }
        } else {
            std::sync::Arc::new(std::collections::HashSet::new())
        }
    };

    // ── M3 novelty-vs-catalog filter ─────────────────────────────────
    //
    // Before sizing the Bloom, collect the canonical hashes of every
    // Eq-rooted PhysLean catalog entry so a GA chain that rediscovers
    // an existing PhysLean theorem is treated as "already known" — no
    // lake cycles burned, no novelty score awarded.
    //
    // Source path: discovered from the prover root (or
    // `$NASRUDIN_CATALOG_PATH` override) via the standard
    // `physlean-extract/output/catalog.json` location. Missing file is
    // OK — workers without a local catalog mirror just fall back to
    // the cluster-rejected memo.
    //
    // Default ON; disable with `NASRUDIN_NOVELTY_VS_CATALOG=0` for
    // research / regression runs that need a clean slate.
    let novelty_vs_catalog: bool = std::env::var("NASRUDIN_NOVELTY_VS_CATALOG")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true);

    let catalog_canonicals: Vec<Vec<u8>> = if !novelty_vs_catalog {
        println!("▶ Novelty-vs-catalog filter DISABLED (NASRUDIN_NOVELTY_VS_CATALOG=0)");
        Vec::new()
    } else {
        // Find a local catalog. Priority:
        //   1. $NASRUDIN_CATALOG_PATH (explicit override),
        //   2. <prover_root>/../physlean-extract/output/catalog.json
        //      (mirrors the API server's boot-path resolution),
        //   3. ./physlean-extract/output/catalog.json (repo-root run).
        let catalog_path: Option<PathBuf> = std::env::var("NASRUDIN_CATALOG_PATH")
            .ok()
            .map(PathBuf::from)
            .or_else(|| {
                prover_root
                    .as_ref()
                    .map(|p| p.join("../physlean-extract/output/catalog.json"))
            })
            .or_else(|| {
                let local = PathBuf::from("physlean-extract/output/catalog.json");
                if local.exists() { Some(local) } else { None }
            });

        match catalog_path {
            Some(path) if path.exists() => {
                match nasrudin_derive::axiom_store::AxiomStore::collect_catalog_eq_canonicals(&path)
                {
                    Ok(hashes) => {
                        println!(
                            "▶ Novelty-vs-catalog: {} Eq-rooted PhysLean entries collected from {}",
                            hashes.len(),
                            path.display()
                        );
                        hashes
                    }
                    Err(e) => {
                        eprintln!(
                            "  ! catalog hash collection failed: {e}; novelty filter falls back to cluster-rejected only"
                        );
                        Vec::new()
                    }
                }
            }
            Some(path) => {
                eprintln!(
                    "  ! catalog path resolved to {} but file does not exist; novelty filter falls back to cluster-rejected only",
                    path.display()
                );
                Vec::new()
            }
            None => {
                eprintln!(
                    "  ! no catalog.json found (set NASRUDIN_CATALOG_PATH or pass --verify <prover>); novelty filter falls back to cluster-rejected only"
                );
                Vec::new()
            }
        }
    };

    // Bloom-filter pre-check over the rejected ∪ catalog set. The bloom is
    // sized for ~100k entries with FPR 0.001. CPU-cache-friendly compared
    // to the HashSet probe, so even when the set is small the check is
    // faster. Only built when there's something to prepopulate; an
    // empty bloom would always-miss and regress to the HashSet path
    // anyway. Sized = (catalog_count + rejected_count) * 4, floor 4096,
    // so workers in early-cluster days don't have a near-saturated filter.
    let novelty_bloom: Option<std::sync::Arc<bloomfilter::Bloom<[u8]>>> = {
        let catalog_count = catalog_canonicals.len();
        let rejected_count = rejected_canonicals.len();
        let total_unique_estimate = catalog_count + rejected_count;
        if total_unique_estimate == 0 {
            None
        } else {
            let n = std::cmp::max(total_unique_estimate * 4, 4096);
            let mut b =
                bloomfilter::Bloom::new_for_fp_rate(n, 0.001).expect("bloom params are valid");
            // Catalog hashes first, then cluster-rejected. Duplicates
            // are harmless — `set` is idempotent on the bloom — so we
            // don't bother deduping into a HashSet just to count.
            for h in &catalog_canonicals {
                b.set(h.as_slice());
            }
            for h in rejected_canonicals.iter() {
                b.set(h.as_slice());
            }
            let total = catalog_count + rejected_count;
            println!(
                "▶ Novelty bloom: {catalog_count} catalog + {rejected_count} cluster-rejected = {total} total hashes (capacity {n}, FPR ~0.1%)"
            );
            Some(std::sync::Arc::new(b))
        }
    };
    println!();

    // Layer 2: hard-reject candidates whose final equation has known,
    // mismatched dimensions. Default on; disable with
    // `NASRUDIN_DIMENSION_HARD_REJECT=0` (or `--soft-dimension`) for
    // natural-units / non-SI research where the soft-fitness behaviour
    // is the right call.
    let dimension_hard_reject: bool = !args.iter().any(|a| a == "--soft-dimension")
        && std::env::var("NASRUDIN_DIMENSION_HARD_REJECT")
            .map(|v| {
                !matches!(
                    v.trim().to_lowercase().as_str(),
                    "0" | "false" | "no" | "off"
                )
            })
            .unwrap_or(true);
    let primary_domain = match domain.as_str() {
        "sr" => nasrudin_core::Domain::SpecialRelativity,
        "em" => nasrudin_core::Domain::Electromagnetism,
        "qm" => nasrudin_core::Domain::QuantumMechanics,
        // Pure-math / mixed: no canonical var→dim table; gate becomes
        // a no-op because every var infers to None.
        _ => nasrudin_core::Domain::PureMath,
    };
    let dimension_var_dims =
        std::sync::Arc::new(nasrudin_derive::domain_variable_dimensions(&primary_domain));
    if dimension_hard_reject {
        println!(
            "▶ Dimension hard-reject ON ({} known vars; pass --soft-dimension to disable)",
            dimension_var_dims.len()
        );
    } else {
        println!("▶ Dimension hard-reject OFF (soft fitness only)");
    }

    // Layer 1: persistent Lean elaborator. Spawn one long-lived
    // `lake env lean --run scripts/nasrudin_server.lean` subprocess that
    // pre-loads Mathlib (~5–30s once at boot), then handles each
    // candidate verification as a JSON-RPC call (~100–500ms each)
    // instead of paying the full `lake build` startup tax per candidate.
    //
    // Disable with `--no-persistent-elaborator` (or
    // `NASRUDIN_NO_PERSISTENT=1`) to fall back exclusively to lake build.
    // When the elaborator is in use, the run still keeps the lake-build
    // fallback path live for any candidate the elaborator can't handle
    // (transient RPC error, request timeout, etc.) — the architecture
    // degrades gracefully.
    let no_persistent: bool = args.iter().any(|a| a == "--no-persistent-elaborator")
        || std::env::var("NASRUDIN_NO_PERSISTENT")
            .map(|v| matches!(v.trim().to_lowercase().as_str(), "1" | "true" | "yes"))
            .unwrap_or(false);
    // Two ways to talk to the elaborator. UDS mode (preferred on prod)
    // connects to the long-lived `nasrudin-elaborator.service` daemon
    // that survives worker OOMs — boot cost is paid once per day, not
    // once per worker restart. Spawn mode (dev fallback) forks Lean
    // in-process, paying the 15-min Mathlib import every restart.
    let elab_uds = std::env::var("NASRUDIN_ELAB_UDS").ok();
    let elaborator: Option<std::sync::Arc<nasrudin_lean_bridge::PersistentElaborator>> =
        if no_persistent || prover_root.is_none() {
            None
        } else if let Some(uds_path) = elab_uds.as_deref() {
            println!("▶ Connecting to elaborator daemon at {uds_path}");
            // 2-hour connect window: covers the daemon's 90 min cold
            // boot timeout on a 2 GB box plus restart-and-retry slack.
            // A genuinely-broken daemon (binary bug, missing oleans)
            // will systemd-loop fast enough that the worker still hits
            // its own timeout and falls back to lake build. Per-request
            // timeout matches the in-process path.
            match nasrudin_lean_bridge::PersistentElaborator::from_uds(
                uds_path,
                std::time::Duration::from_secs(7200),
                // 180s per-request: on a 2 GB box the daemon's
                // working set is mostly in swap when idle. The first
                // request after a long quiet period can take 30-90s
                // as the kernel faults in lemma pages from /swapfile.
                // Steady-state requests after that land in <500 ms.
                // 30 s was too tight: a cold-page ping fell back to
                // lake build for the rest of the worker's lifetime.
                std::time::Duration::from_secs(180),
            )
            .await
            {
                Ok(handle) => {
                    // Verify the daemon's Lean is actually alive — a
                    // fresh socket file does not prove the elaborator
                    // is responsive. A failed ping flips us to the
                    // slow path so the GA still produces *something*.
                    match handle.ping().await {
                        Ok(()) => {
                            println!("    ✓ elaborator daemon ready (ping ok)");
                            Some(std::sync::Arc::new(handle))
                        }
                        Err(e) => {
                            eprintln!(
                                "    ! elaborator daemon ping failed: {e}\n    falling back to lake build (slow path)"
                            );
                            None
                        }
                    }
                }
                Err(e) => {
                    eprintln!(
                        "    ! elaborator daemon connect failed: {e}\n    falling back to lake build (slow path)"
                    );
                    None
                }
            }
        } else {
            let cfg = nasrudin_lean_bridge::PersistentElaboratorConfig {
                cwd: prover_root.clone().unwrap(),
                ..nasrudin_lean_bridge::PersistentElaboratorConfig::from_env()
            };
            println!(
                "▶ Spawning persistent Lean elaborator (cwd={}, script={})",
                cfg.cwd.display(),
                cfg.script_path.display()
            );
            match nasrudin_lean_bridge::PersistentElaborator::new(cfg).await {
                Ok(handle) => {
                    println!("    ✓ elaborator booted (Mathlib loaded)");
                    Some(std::sync::Arc::new(handle))
                }
                Err(e) => {
                    eprintln!(
                        "    ! elaborator failed to boot: {e}\n    falling back to lake build (slow path)"
                    );
                    None
                }
            }
        };

    if no_persistent {
        println!("▶ Persistent elaborator DISABLED (lake-only path)");
    }

    // Capture the target name before the spec is moved into config —
    // we still need it to decide whether to install the M1 permanent
    // elite below.
    let target_name_for_elite: Option<&'static str> = target_spec.as_ref().map(|t| t.name);
    let config = DiscoveryConfig {
        population_size: pop,
        generations: gens,
        crossover_rate: 0.6,
        mutation_rate: 0.7,
        tournament_size: 3,
        max_chain_len,
        // P-Task 11: in --no-local-lake mode, drop the local lake-build
        // pipeline entirely. Server's reverify drain handles
        // verification via chain replay (microseconds) and the
        // lake-promotion drain handles kernel confirmation lazily.
        prover_root: if no_local_lake {
            None
        } else {
            prover_root.clone()
        },
        max_lake_verifications: if no_local_lake {
            0
        } else if prover_root.is_some() {
            max_lake
        } else {
            0
        },
        target: target_spec,
        rejected_canonicals: rejected_canonicals.clone(),
        novelty_bloom: novelty_bloom.clone(),
        cache_ctx: None,
        mutation_priors: None,
        submit_unverified_top_k: submit_top_k,
        dimension_hard_reject,
        dimension_var_dims: dimension_var_dims.clone(),
        elaborator: elaborator.clone(),
        // Cluster-steerer mutation_knobs are applied per-chunk via
        // `apply_steering_knobs` once the seed-fetch returns; defaults
        // here keep the legacy (uniform / no-elitism) behaviour for
        // chunks where steering hasn't landed yet.
        suffix_bias: 0.0,
        elitism_fraction: 0.0,
        // Enabled when this worker reports clusters to the API (any
        // worker connected to the cluster steerer). The chunk loop
        // uses report.final_population to compute ClusterSummaries.
        collect_final_population: api_cfg.is_some(),
        // Per-cluster knob overrides — populated per-chunk after
        // matching the LLM's cluster_directives via the bandit. The
        // base config holds an empty map so the GA falls back to
        // global rates until directives land.
        cluster_multipliers: std::collections::HashMap::new(),
        cluster_assignments: vec![],
        atom_pool: None,
        // Milestone 1 mechanism test: when the target is sr_rest_energy
        // and the env opt-out hasn't been set, lock the hand-coded
        // upstream rest-energy chain in as the permanent elite so each
        // chunk has at least one Lake-quality candidate. M1.d clears
        // NASRUDIN_M1_SEED_ELITE=0 (or unsets the target) to confirm
        // the GA can rediscover it from random seeds + the steerer.
        permanent_elite: m1_seed_elite_for(target_name_for_elite),
        // LLM-proposed chains are filled in per-chunk after the
        // steering snapshot lands; empty at boot.
        llm_proposed_chains: Vec::new(),
    };
    if let Some(ref elite) = config.permanent_elite {
        println!(
            "▶ Milestone 1: permanent elite installed ({} steps) for target={:?} — \
             upstream seed chain locked into every generation. \
             Unset NASRUDIN_M1_SEED_ELITE or pass NASRUDIN_M1_SEED_ELITE=0 to disable.",
            elite.len(),
            target_name_for_elite
        );
    } else {
        println!(
            "▶ Milestone 1: no permanent elite (target={:?}, NASRUDIN_M1_SEED_ELITE check). \
             Pure-random GA from random_chain_seed.",
            target_name_for_elite
        );
    }

    // ── Chunked execution with periodic seed-sync ─────────────────────
    // Run the GA in `chunks` rounds of `gens / chunks` generations each.
    // Between rounds:
    //   1. Re-fetch /api/seed and fold any new peer-verified theorems
    //      into the AxiomStore as additional building blocks. As other
    //      workers in the cluster verify intermediates, this worker
    //      picks them up live without restarting.
    //   2. Re-fetch /api/rejected_hashes so newly-rejected canonicals
    //      from the cluster prune our search.
    //   3. Submit any verified discoveries from this chunk *immediately*
    //      so peer workers see them on their next sync.
    //
    // chunks=1 reverts to single-shot behaviour; default is 4.
    let chunks: usize = arg_value(&args, "--chunks")
        .or_else(|| {
            std::env::var("NASRUDIN_CHUNKS")
                .ok()
                .and_then(|s| s.parse().ok())
        })
        .unwrap_or(4);
    let gens_per_chunk = (gens / chunks).max(1);
    let api_url_for_resync = std::env::var("NASRUDIN_API_URL").ok();
    let domain_param_for_resync = match domain.as_str() {
        "sr" => "SpecialRelativity",
        "em" => "Electromagnetism",
        "qm" => "QuantumMechanics",
        _ => "",
    };

    println!(
        "▶ Running discovery: pop={}, gens={} ({} chunks × {} gens), max_chain_len={}, lake_budget={}",
        pop, gens, chunks, gens_per_chunk, max_chain_len, config.max_lake_verifications
    );
    println!();

    let mut rng = rand::rng();
    let mut combined_verified: Vec<VerifiedDiscovery> = Vec::new();
    let mut total_lake = 0usize;
    let mut total_lake_passed = 0usize;
    let mut total_persistent_attempts = 0usize;
    let mut total_dim_rejected = 0usize;
    let mut total_pre_lake_rejected = 0usize;
    let mut total_candidates = 0usize;
    let mut total_unique = 0usize;
    let mut current_rejected = rejected_canonicals.clone();
    // Latest steering snapshot from `/api/seed`. Updated on every
    // chunk-boundary re-sync; applied to the per-chunk DiscoveryConfig
    // via `apply_steering_knobs` so the LLM cluster steerer's
    // mutation rate / population size land on the next chunk's GA.
    let mut last_steering: Option<serde_json::Value> = None;
    // Eligibility-trace buffer for per-cluster directives. Each
    // applied directive stays in flight for `TRACE_HORIZON` chunks
    // and accumulates samples; the bandit reward is the γ-discounted
    // return over that horizon. Replaces the single-shot reward path
    // with a multi-chunk credit assignment more robust to noise.
    let mut directive_traces: Vec<nasrudin_ga::clustering::DirectiveTrace> = Vec::new();
    // Rolling window of the last 50 centroid hashes seen at apply
    // time. Used to compute an intrinsic-motivation novelty bonus
    // for directives that target rarely-visited cluster lineages.
    let mut hash_history = nasrudin_ga::clustering::CentroidHashHistory::with_capacity(50);

    // Phase E: when research-mode is on, build the HTTP client once.
    let research_client = if research_mode {
        api_cfg.as_ref().map(|cfg| {
            nasrudin_ga::research_client::ResearchClient::new(
                cfg.api_url.clone(),
                cfg.worker_key.clone(),
            )
        })
    } else {
        None
    };

    // Paid Researcher tier: distinct queue, distinct client. Tries
    // /api/jobs/claim first each chunk; on award runs a paid slice
    // and skips the rest of the chunk. On 204, falls through to the
    // legacy research_mode path and then the background fleet.
    let paid_jobs_client = if paid_jobs_mode {
        api_cfg.as_ref().map(|cfg| {
            std::sync::Arc::new(nasrudin_ga::paid_jobs_client::PaidJobsClient::new(
                cfg.api_url.clone(),
                cfg.worker_key.clone(),
            ))
        })
    } else {
        None
    };
    // Slot count we report to the server on every paid claim.
    // `ResourceBudget::detect()` honors cgroup CPU + memory limits so
    // a worker running inside Docker / k8s reports the slots actually
    // available to the container, not the host's. The `--max-lake`
    // CLI override (or `NASRUDIN_LAKE_SLOTS_OVERRIDE`) trumps detection
    // when the operator wants to pin a specific count.
    let paid_available_slots: u32 = {
        let budget = nasrudin_ga::auto_size::ResourceBudget::detect();
        let cli_override = max_lake as u32;
        let detected = budget.lake_slots as u32;
        // CLI flag wins when explicitly higher; otherwise prefer
        // detected so a `--max-lake 3` on a 32-slot box still reports
        // 32 to the cluster (the operator can lower with the env-var
        // override if they really mean to cap).
        std::cmp::max(cli_override, detected).max(1)
    };
    tracing::info!(
        paid_available_slots,
        "worker reporting available_lake_slots to /api/jobs/claim"
    );
    // Seed config for paid slices: same shape as the background
    // config but with `submit_unverified_top_k = 0` so a noisy slice
    // doesn't pollute the global ingest path — the slice's only
    // submission channel is `mark_proved` once a kernel-verified
    // theorem appears.
    let paid_slice_base_config = {
        let mut c = config.clone();
        c.submit_unverified_top_k = 0;
        c.population_size = pop;
        c.max_chain_len = max_chain_len;
        c
    };
    let paid_slice_store: std::sync::Arc<AxiomStore> = std::sync::Arc::new(store.clone());
    let worker_rl_scope_key = worker_rl_scope_key(&domain, target_name_for_elite);
    let mut worker_rl_scope_state = worker_rl_state
        .scopes
        .get(&worker_rl_scope_key)
        .cloned()
        .unwrap_or_default();
    decay_worker_rl_scope_state(
        &mut worker_rl_scope_state,
        now_unix_secs(),
        rl_half_life_hours(),
    );
    decay_worker_rl_scope_for_corpus_drift(&mut worker_rl_scope_state, store.len());
    let learned_ops: u32 = worker_rl_scope_state.mutation_operator.pulls.iter().sum();
    let qd_cells = worker_rl_scope_state.qd_archive.cells.len();
    if learned_ops > 0 || qd_cells > 0 {
        println!(
            "▶ Loaded local worker RL state: scope={worker_rl_scope_key}, {learned_ops} operator observations, {qd_cells} QD cells from {}",
            worker_rl_state_path.display()
        );
    }

    for chunk_i in 0..chunks {
        // ── Paid Researcher claim (highest priority) ─────────────────────
        // The $19/mo Researcher tier owns its own queue under
        // /api/jobs/claim. Try it first — if a claim succeeds we hand
        // the entire chunk over to the slice runner (which will heartbeat,
        // mark_proved on a verified hit, or run until the server signals
        // budget_exhausted) and skip the rest of the chunk's work.
        if let Some(client) = paid_jobs_client.as_ref() {
            let claim_body = nasrudin_ga::paid_jobs_client::ClaimBody {
                available_lake_slots: paid_available_slots,
                domains_supported: vec!["all".into()],
            };
            match client.claim(&claim_body).await {
                Ok(Some(job)) => {
                    println!(
                        "▶ chunk {} claimed paid conjecture {} (hunch: {}) — slot-hours remaining: {:.1}",
                        chunk_i + 1,
                        job.job_id,
                        job.hunch.chars().take(80).collect::<String>(),
                        job.lake_slot_hours_remaining
                    );
                    if let Err(e) = nasrudin_ga::paid_slice::run_paid_slice(
                        client,
                        &job,
                        paid_slice_store.clone(),
                        paid_slice_base_config.clone(),
                    )
                    .await
                    {
                        eprintln!("  ! paid slice for {} failed: {e}; releasing", job.job_id);
                        let _ = client.release(job.job_id).await;
                    }
                    continue;
                }
                Ok(None) => {
                    tracing::debug!("paid-jobs claim: queue empty / floor protected");
                }
                Err(e) => {
                    tracing::warn!("paid-jobs claim failed: {e}; falling through");
                }
            }
        }

        // ── Phase E: research-mode dequeue ────────────────────────────────
        // Try to claim a conjecture before falling through to background
        // corpus-fill. If a job is claimed, run it to completion (or budget
        // exhaustion) under its own constrained AxiomStore + LLM-supplied
        // mutation priors. Submissions go to /api/conjecture/{id}/submit
        // so they're accounted to the conjecture, not the global queue.
        if let (Some(client), Some(cfg)) = (research_client.as_ref(), api_cfg.as_ref()) {
            match client.claim().await {
                Ok(Some(job)) => {
                    println!(
                        "▶ chunk {} claimed conjecture {} (hunch: {})",
                        chunk_i + 1,
                        job.job_id,
                        job.hunch.chars().take(80).collect::<String>()
                    );
                    if let Err(e) = run_seed_driven_chunk(
                        client,
                        cfg,
                        &domain,
                        &store,
                        &job,
                        max_chain_len,
                        prover_root.as_deref(),
                        max_lake,
                        current_rejected.clone(),
                        novelty_bloom.clone(),
                        &mut rng,
                    )
                    .await
                    {
                        eprintln!("  ! conjecture {} failed: {e}", job.job_id);
                    }
                    // Skip the regular background chunk on a research-mode
                    // claim: the worker has spent its slot on the conjecture.
                    continue;
                }
                Ok(None) => {
                    tracing::debug!("research-mode claim: queue empty");
                }
                Err(e) => {
                    tracing::warn!(
                        "research-mode claim failed: {e}; falling through to background"
                    );
                }
            }
        }

        // Periodic embed-index refresh. Cheap when index is current
        // (one HTTP HEAD-equivalent call per chunk). Off by default;
        // flip on with NASRUDIN_EMBED_AUTOPULL=1.
        if let Ok(autopull) = std::env::var("NASRUDIN_EMBED_AUTOPULL")
            && matches!(
                autopull.trim().to_lowercase().as_str(),
                "1" | "true" | "yes"
            )
        {
            let api = std::env::var("NASRUDIN_API_URL")
                .unwrap_or_else(|_| "http://localhost:8080".into());
            let path: std::path::PathBuf = std::env::var("NASRUDIN_EMBED_OUT")
                .map(std::path::PathBuf::from)
                .unwrap_or_else(|_| {
                    let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
                    std::path::PathBuf::from(home).join(".nasrudin/embed/corpus.embed")
                });
            if let Err(e) = embed_autopull::maybe_refresh(&api, &path).await {
                tracing::debug!("embed autopull skipped: {e}");
            }
        }

        if chunk_i > 0
            && let Some(ref api_url) = api_url_for_resync
        {
            // Periodic seed-sync: pick up peer discoveries since last
            // chunk. Soft-fail — search continues with current store
            // if the API is briefly unreachable.
            match fetch_and_extend_store(api_url, domain_param_for_resync, &mut store).await {
                Ok((ax, th, steering)) => {
                    if ax + th > 0 {
                        println!(
                            "▶ chunk {} re-sync: +{ax} new axioms, +{th} peer theorems  (store={})",
                            chunk_i + 1,
                            store.len()
                        );
                        nasrudin_derive::no_cheat_audit::audit_or_panic(
                            &store,
                            "worker chunk re-sync",
                        );
                    }
                    if steering.is_some() {
                        last_steering = steering;
                    }
                }
                Err(_) => {}
            }
            // Periodic rejected-canonical re-fetch.
            if let Ok(set) = fetch_rejected_canonicals(api_url).await {
                let delta = set.len().saturating_sub(current_rejected.len());
                if delta > 0 {
                    println!(
                        "▶ chunk {} rejected-set: +{delta} new pre-rejected canonicals",
                        chunk_i + 1
                    );
                }
                current_rejected = std::sync::Arc::new(set);
            }
        }
        let mut chunk_config = DiscoveryConfig {
            generations: gens_per_chunk,
            rejected_canonicals: current_rejected.clone(),
            ..config.clone()
        };
        // Apply LLM mutation knobs from the latest steering snapshot.
        // No-op when steering is absent or `mutation_knobs=null`
        // (mode B / steerer disabled / first chunk before re-sync).
        // The domain key threads through so the LLM's per-domain
        // `atom_pool` reaches `append_productive_suffix`; map the
        // worker's short domain flag (`sr`, `em`, `qm`, `gr`) to the
        // steerer's snake-case key.
        let domain_key = match domain.as_str() {
            "sr" => "special_relativity",
            "em" => "electromagnetism",
            "qm" => "quantum_mechanics",
            "gr" => "general_relativity",
            "cm" => "classical_mechanics",
            "thermo" => "thermodynamics",
            other => other,
        };
        let ga_policy = select_ga_workhorse_policy(
            &worker_rl_scope_key,
            &worker_rl_state.ga_workhorse_policies,
            worker_rl_eval_snapshot.as_ref(),
        );
        apply_ga_workhorse_policy(&mut chunk_config, ga_policy, pop, max_chain_len, max_lake);
        let active_replay_selections = replay_elite_selections(&worker_rl_scope_state);
        if !active_replay_selections.is_empty() {
            let n = active_replay_selections.len();
            chunk_config.llm_proposed_chains.extend(
                active_replay_selections
                    .iter()
                    .cloned()
                    .into_iter()
                    .map(|selection| selection.chain),
            );
            println!(
                "▶ chunk {} replay elites: injected {n} locally verified prioritized chain(s) from worker RL archive",
                chunk_i + 1,
            );
        }
        println!(
            "▶ chunk {} GA workhorse policy={ga_policy}: pop={}, gens={}, mutation={:.3}, crossover={:.3}, tournament={}, max_chain_len={}, max_lake={}",
            chunk_i + 1,
            chunk_config.population_size,
            chunk_config.generations,
            chunk_config.mutation_rate,
            chunk_config.crossover_rate,
            chunk_config.tournament_size,
            chunk_config.max_chain_len,
            chunk_config.max_lake_verifications,
        );
        let mut active_strategy_genome: Option<(String, f64)> = None;
        if let Some(ref s) = last_steering {
            let strategy_weight = if let Some(fp) =
                nasrudin_ga::steering_knobs::strategy_genome_fingerprint(s, domain_key)
            {
                let weight = strategy_genome_select_weight(
                    worker_rl_scope_state.strategy_genomes.get(&fp),
                    strategy_genome_eval_prior(&fp, worker_rl_eval_snapshot.as_ref()),
                );
                active_strategy_genome = Some((fp, weight));
                weight
            } else {
                1.0
            };
            if nasrudin_ga::steering_knobs::apply_steering_knobs_for_domain_with_strategy_weight(
                &mut chunk_config,
                s,
                domain_key,
                strategy_weight,
            ) {
                tracing::debug!(
                    rate = chunk_config.mutation_rate,
                    pop = chunk_config.population_size,
                    atom_pool_size = chunk_config
                        .atom_pool
                        .as_ref()
                        .map(|p| p.len())
                        .unwrap_or(0),
                    domain = domain_key,
                    strategy_weight,
                    "chunk config patched from steering"
                );
            }
        }

        // ── LLM-proposed chain elite injection ─────────────────────
        // Pull the chain the steerer proposed for THIS worker's
        // target name from `steering.config.proposed_chains` and
        // install it as an elite seed for this chunk. Opt-in via
        // env so the change is observable in production without a
        // forced rollout — workers without the flag set keep their
        // existing pure-random + permanent_elite behaviour.
        //
        // Failure modes: missing steering, missing proposed_chains
        // map, missing entry for this target, malformed RuleStep
        // payload — all silently fall back to the empty vec so the
        // chunk proceeds with no LLM elites. Logging fires only on
        // the success path so noisy chunks don't spam.
        let use_llm_chains = std::env::var("NASRUDIN_USE_LLM_CHAINS")
            .map(|v| {
                !matches!(
                    v.trim().to_lowercase().as_str(),
                    "0" | "false" | "no" | "off"
                )
            })
            .unwrap_or(false);
        if use_llm_chains {
            if let (Some(steering_val), Some(target_name)) =
                (last_steering.as_ref(), target_name_for_elite)
            {
                let proposed = steering_val
                    .get("config")
                    .and_then(|c| c.get("proposed_chains"))
                    .and_then(|p| p.get(target_name));
                if let Some(chain_val) = proposed {
                    match serde_json::from_value::<Vec<nasrudin_derive::RuleStep>>(
                        chain_val.clone(),
                    ) {
                        Ok(steps) if !steps.is_empty() => {
                            let chain = nasrudin_derive::Chain(steps);
                            println!(
                                "▶ LLM proposed chain ({} steps) for target={} — \
                                 added as elite seed",
                                chain.len(),
                                target_name
                            );
                            chunk_config.llm_proposed_chains.push(chain);
                        }
                        Ok(_) => {
                            tracing::debug!(
                                target = target_name,
                                "LLM proposed_chains entry was empty; ignored"
                            );
                        }
                        Err(e) => {
                            tracing::warn!(
                                target = target_name,
                                error = %e,
                                "failed to deserialise LLM proposed chain; \
                                 falling back to baseline elites"
                            );
                        }
                    }
                }
            }
        }

        // ── Test-time compute scaling bandit ───────────────────────
        // Read compute_directives, UCB1-pick a population_size /
        // generations multiplier per matched directive, apply
        // chunk-wide. Compute is not per-cluster; one matched
        // directive scales the whole island's chunk. Multiple
        // matched directives compose multiplicatively (capped).
        // Records pulls via `pending_compute_pulls` so the bandit
        // can reward attribution at chunk end based on the chunk's
        // discoveries-per-pop ratio (higher = compute well-spent).
        let mut pending_compute_pulls: Vec<(String, u8, u8, f64)> = Vec::new();
        let canonical_domain_for_compute: &str = match domain.as_str() {
            "sr" => "special_relativity",
            "em" => "electromagnetism",
            "qm" => "quantum_mechanics",
            "thermo" => "thermodynamics",
            "cm" => "classical_mechanics",
            "gr" => "general_relativity",
            other => other,
        };
        if let Some(steering_val) = last_steering.as_ref() {
            let compute_dirs = steering_val
                .get("config")
                .and_then(|c| c.get("compute_directives"))
                .and_then(|v| v.as_array())
                .cloned()
                .unwrap_or_default();
            let mut compute_mult: f32 = 1.0;
            for d in compute_dirs.iter() {
                let scope_dom = d.get("island_domain").and_then(|v| v.as_str());
                if let Some(dom) = scope_dom {
                    if dom != canonical_domain_for_compute {
                        continue;
                    }
                }
                let strength = d.get("strength").and_then(|v| v.as_f64()).unwrap_or(0.0) as f32;
                let strength_bucket = (strength.clamp(0.0, 1.0) * 5.0).floor().min(4.0) as u8;
                let arms = compute_arms_for_slot(
                    steering_val,
                    canonical_domain_for_compute,
                    strength_bucket,
                );
                let multiplier_choice = pick_multiplier_choice(&arms, strength);
                let mult_value = lookup_compute_multiplier(multiplier_choice);
                compute_mult *= mult_value;
                pending_compute_pulls.push((
                    canonical_domain_for_compute.to_string(),
                    strength_bucket,
                    multiplier_choice,
                    chunk_config.population_size as f64,
                ));
                tracing::info!(
                    strength_bucket,
                    multiplier_choice,
                    mult_value,
                    "applied compute directive (test-time scaling)"
                );
            }
            // Cap the chunk-wide compute scaling so a stack of
            // 2.0× directives can't blow past the runtime's pop /
            // generation budget. Bounds match the GA's defaults.
            let scaled_pop =
                (chunk_config.population_size as f32 * compute_mult).clamp(32.0, 512.0);
            let scaled_gens = (chunk_config.generations as f32 * compute_mult).clamp(8.0, 2000.0);
            chunk_config.population_size = scaled_pop as usize;
            chunk_config.generations = scaled_gens as usize;
        }

        // ── Per-cluster directive routing (v1.5 + v2) ──────────────
        // When connected to the API, externally seed the population
        // and cluster the seeds so per-cluster directives can route
        // to specific cluster_ids and the GA's mutation site fires
        // `local_mutation_rate_for_cluster`. `current_directive_log`
        // captures (cluster_id, action, strength_bucket,
        // multiplier_choice, mean_fitness_at_apply) so we can
        // compute the reward at chunk END from the same chunk's
        // final fitness — no cross-chunk hash drift problem.
        let canonical_domain: &str = match domain.as_str() {
            "sr" => "special_relativity",
            "em" => "electromagnetism",
            "qm" => "quantum_mechanics",
            "thermo" => "thermodynamics",
            "cm" => "classical_mechanics",
            "gr" => "general_relativity",
            other => other,
        };
        // Indices into `directive_traces` of new traces created this
        // chunk. Used after the GA runs to observe sample[0] (the
        // immediate post-evolution effect on each directive's
        // matched cluster lineage).
        let mut new_trace_indices: Vec<usize> = Vec::new();
        let mut seed_summaries: Vec<nasrudin_ga::clustering::ClusterSummary> = Vec::new();

        // Build the report's bookkeeping placeholder once so we can
        // either run the legacy `run_discovery` path or the
        // pre-seeded `run_discovery_from_population` path with
        // matching `total_candidates` accounting.
        let mut initial_report = nasrudin_ga::chain_engine::DiscoveryReport::default();
        initial_report.mutation_operator_stats = worker_rl_scope_state.mutation_operator.clone();
        initial_report.qd_archive_stats = worker_rl_scope_state.qd_archive.clone();
        let report =
            if let Some(steering_val) = last_steering.as_ref().filter(|_| api_cfg.is_some()) {
                // Externally seed so we can cluster + tag cluster_id
                // before the offspring loop runs.
                let mut seed_pop = nasrudin_ga::chain_engine::seed_population(
                    &store,
                    &chunk_config,
                    &mut rng,
                    &mut initial_report,
                );
                // K from the bandit's cluster_config; clamp [2, 12].
                let k_for_island = steering_val
                    .get("cluster_config")
                    .and_then(|cc| cc.get("k_per_island"))
                    .and_then(|m| m.get(canonical_domain))
                    .and_then(|v| v.as_u64())
                    .map(|v| v.clamp(2, 12) as u32)
                    .unwrap_or(6);
                // Build cluster features from the seed population.
                let chunk_seed = (chunk_i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
                let chains_with_fitness: Vec<(_, [f32; 4], Vec<String>)> = seed_pop
                    .iter()
                    .map(|ind| {
                        let names = nasrudin_ga::clustering::extract_axiom_names(&ind.chain);
                        let f = &ind.fitness;
                        let length_signal =
                            (1.0 - (ind.chain.0.len() as f64 / 16.0).min(1.0)).clamp(0.0, 1.0);
                        let comps = [
                            f.novelty.clamp(0.0, 1.0) as f32,
                            f.dimensional.clamp(0.0, 1.0) as f32,
                            length_signal as f32,
                            f.target_shape.max(f.ladder_progress).clamp(0.0, 1.0) as f32,
                        ];
                        (ind.chain.clone(), comps, names)
                    })
                    .collect();
                let (s_summaries, s_assignment) = nasrudin_ga::clustering::cluster_and_summarise(
                    &chains_with_fitness,
                    k_for_island,
                    canonical_domain,
                    chunk_seed,
                );
                // Tag each individual with its seed cluster_id so child
                // lineage carries the cluster through crossover.
                for (i, ind) in seed_pop.iter_mut().enumerate() {
                    ind.cluster_id = *s_assignment.assignments.get(i).unwrap_or(&0);
                }
                chunk_config.cluster_assignments = s_assignment.assignments.clone();
                seed_summaries = s_summaries;

                // Match LLM directives against seed clusters by hash.
                // Populate cluster_multipliers and aggregate v1.5 layer.
                let mut aggregate_mut_mult: f64 = 1.0;
                let mut aggregate_elite_mult: f64 = 1.0;
                let directives = steering_val
                    .get("config")
                    .and_then(|c| c.get("cluster_directives"))
                    .and_then(|v| v.as_array())
                    .cloned()
                    .unwrap_or_default();
                let centroids: Vec<(u32, u64)> = seed_summaries
                    .iter()
                    .map(|s| (s.cluster_id, s.centroid_skeleton_hash))
                    .collect();
                for d in directives.iter() {
                    let dom = d
                        .get("island_domain")
                        .and_then(|v| v.as_str())
                        .unwrap_or("");
                    if dom != canonical_domain {
                        continue;
                    }
                    let hash = d
                        .get("centroid_skeleton_hash")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    let action = d
                        .get("action")
                        .and_then(|v| v.as_str())
                        .unwrap_or("")
                        .to_string();
                    let strength = d.get("strength").and_then(|v| v.as_f64()).unwrap_or(0.0) as f32;
                    let strength_bucket = (strength.clamp(0.0, 1.0) * 5.0).floor().min(4.0) as u8;
                    let Some(cid) =
                        nasrudin_ga::clustering::match_directive_to_cluster(hash, &centroids, 0.10)
                    else {
                        continue;
                    };
                    let arms = directive_arms_for_slot(
                        steering_val,
                        canonical_domain,
                        &action,
                        strength_bucket,
                    );
                    let multiplier_choice = pick_multiplier_choice(&arms, strength);
                    let mult_value = lookup_action_multiplier(&action, multiplier_choice);
                    let m = chunk_config.cluster_multipliers.entry(cid).or_default();
                    match action.as_str() {
                        "boost" => {
                            m.mutation_rate_mult = mult_value;
                            if (mult_value as f64) > aggregate_mut_mult {
                                aggregate_mut_mult = mult_value as f64;
                            }
                        }
                        "exploit" => {
                            m.elitism_mult = mult_value;
                            if (mult_value as f64) > aggregate_elite_mult {
                                aggregate_elite_mult = mult_value as f64;
                            }
                        }
                        "diversify" => m.diversify_fraction = mult_value,
                        "kill" => m.kill_fraction = mult_value,
                        _ => continue,
                    }
                    let mean_fitness_at_apply = seed_summaries
                        .iter()
                        .find(|s| s.cluster_id == cid)
                        .map(|s| s.mean_fitness)
                        .unwrap_or(0.0);
                    let mut trace = nasrudin_ga::clustering::DirectiveTrace::new(
                        hash,
                        action.clone(),
                        strength_bucket,
                        multiplier_choice,
                        mean_fitness_at_apply,
                    );
                    // Curiosity / novelty bonus: rare hashes in the
                    // recent window get a small extra reward, capped at
                    // INTRINSIC_BONUS_CAP so the bandit can't be
                    // hijacked by always-novel arms with zero extrinsic
                    // value. Apply BEFORE recording the hash so a
                    // freshly-seen hash gets full novelty credit.
                    trace.novelty_bonus = hash_history.novelty_bonus(hash);
                    hash_history.observe(hash);
                    directive_traces.push(trace);
                    new_trace_indices.push(directive_traces.len() - 1);
                    tracing::info!(
                        cluster_id = cid,
                        action = %action,
                        strength_bucket,
                        multiplier_choice,
                        mult_value,
                        "applied cluster directive (per-individual, trace started)"
                    );
                }
                // v1.5 chunk-wide aggregate: even individuals in
                // unmatched clusters feel some shift, so the bandit's
                // reward signal isn't washed out by clusters that didn't
                // get a directive.
                chunk_config.mutation_rate =
                    (chunk_config.mutation_rate * aggregate_mut_mult).clamp(0.05, 0.30);
                chunk_config.elitism_fraction = (chunk_config.elitism_fraction as f64
                    * aggregate_elite_mult)
                    .clamp(0.0, 0.2) as f32;

                nasrudin_ga::chain_engine::run_discovery_from_population(
                    &store,
                    &chunk_config,
                    seed_pop,
                    &mut rng,
                    initial_report,
                )
            } else {
                // Offline / no steering yet: use the legacy seed-then-
                // evolve path; cluster_assignments stays empty so the
                // GA falls back to global mutation rate.
                let mut seed_pop = nasrudin_ga::chain_engine::seed_population(
                    &store,
                    &chunk_config,
                    &mut rng,
                    &mut initial_report,
                );
                for ind in &mut seed_pop {
                    ind.cluster_id = 0;
                }
                nasrudin_ga::chain_engine::run_discovery_from_population(
                    &store,
                    &chunk_config,
                    seed_pop,
                    &mut rng,
                    initial_report,
                )
            };
        if let Some((fp, weight)) = active_strategy_genome.as_ref() {
            let reward = strategy_genome_reward(&report);
            let stats = worker_rl_scope_state
                .strategy_genomes
                .entry(fp.clone())
                .or_default();
            strategy_genome_update(stats, *weight, reward);
            tracing::debug!(
                pulls = stats.pulls,
                mean_reward = stats.total_reward / stats.pulls.max(1) as f64,
                weight_mean = stats.weight_mean,
                weight_sigma = stats.weight_sigma,
                reward,
                "updated strategy genome evaluator stats"
            );
        }
        let ga_policy_reward = strategy_genome_reward(&report);
        let ga_policy_key = ga_workhorse_policy_key(&worker_rl_scope_key, ga_policy);
        let ga_policy_stats = worker_rl_state
            .ga_workhorse_policies
            .entry(ga_policy_key)
            .or_default();
        update_ga_workhorse_policy(ga_policy_stats, ga_policy_reward);
        tracing::debug!(
            policy = ga_policy,
            pulls = ga_policy_stats.pulls,
            mean_reward = ga_policy_stats.total_reward / ga_policy_stats.pulls.max(1) as f64,
            reward = ga_policy_reward,
            "updated GA workhorse policy stats"
        );
        let now_after_chunk = now_unix_secs();
        update_selected_replay_elites(
            &mut worker_rl_scope_state,
            &active_replay_selections,
            &report,
            ga_policy_reward,
            now_after_chunk,
        );
        if worker_rl_episode_log_enabled() {
            let episode = WorkerRlEpisode {
                version: 1,
                at_unix_secs: now_after_chunk,
                scope_key: worker_rl_scope_key.clone(),
                domain: domain.clone(),
                target: target_name_for_elite.map(|s| s.to_string()),
                chunk_index: chunk_i,
                chunks_total: chunks,
                corpus_len: store.len(),
                target_selector_policy: active_target_selector_policy.clone(),
                ga_policy: ga_policy.to_string(),
                strategy_genome_fingerprint: active_strategy_genome
                    .as_ref()
                    .map(|(fp, _)| fp.clone()),
                strategy_genome_weight: active_strategy_genome.as_ref().map(|(_, weight)| *weight),
                replay_canonicals: active_replay_selections
                    .iter()
                    .map(|selection| selection.canonical.clone())
                    .collect(),
                population_size: chunk_config.population_size,
                generations: chunk_config.generations,
                mutation_rate: chunk_config.mutation_rate,
                crossover_rate: chunk_config.crossover_rate,
                tournament_size: chunk_config.tournament_size,
                max_chain_len: chunk_config.max_chain_len,
                max_lake_verifications: chunk_config.max_lake_verifications,
                total_candidates: report.total_candidates,
                unique_executable: report.unique_executable,
                lake_attempts: report.lake_attempts,
                lake_passed: report.lake_passed,
                dim_rejected: report.dim_rejected,
                pre_lake_rejected: report.pre_lake_rejected,
                verified_count: report.verified.len(),
                verified_canonicals: report
                    .verified
                    .iter()
                    .map(|d| d.canonical.clone())
                    .collect(),
                reward: ga_policy_reward,
            };
            let episode_path = worker_rl_episode_log_path(&worker_rl_state_path);
            if let Err(e) = append_worker_rl_episode(&episode_path, &episode) {
                tracing::warn!(
                    error = %e,
                    path = %episode_path.display(),
                    "failed to append worker RL episode"
                );
            } else {
                match maybe_refresh_worker_rl_episode_eval(
                    &episode_path,
                    &worker_rl_state_path,
                    now_after_chunk,
                ) {
                    Ok(Some(snapshot)) => {
                        worker_rl_eval_snapshot = Some(snapshot);
                    }
                    Ok(None) => {}
                    Err(e) => {
                        tracing::warn!(
                            error = %e,
                            path = %episode_path.display(),
                            "failed to refresh worker RL episode evaluation"
                        );
                    }
                }
            }
        }
        if !no_local_lake {
            let replay_added = update_replay_elites_from_verified(
                &mut worker_rl_scope_state,
                &report,
                now_after_chunk,
            );
            if replay_added > 0 {
                println!(
                    "▶ replay archive: added/updated {replay_added} locally verified elite(s), archive_size={}",
                    worker_rl_scope_state.replay_elites.len()
                );
            }
        }
        worker_rl_scope_state.mutation_operator = report.mutation_operator_stats.clone();
        worker_rl_scope_state.qd_archive = report.qd_archive_stats.clone();
        worker_rl_scope_state.updated_at_unix_secs = now_unix_secs();
        worker_rl_scope_state.corpus_len = store.len();
        worker_rl_state
            .scopes
            .insert(worker_rl_scope_key.clone(), worker_rl_scope_state.clone());
        if let Err(e) = save_worker_rl_state(&worker_rl_state_path, &worker_rl_state) {
            tracing::warn!(
                error = %e,
                path = %worker_rl_state_path.display(),
                "failed to persist worker RL state"
            );
        }

        // Cluster the chunk's final population and POST per-cluster
        // ClusterSummaries to the API. Re-cluster the final population
        // here (separate from the seed-time clustering above) because
        // the LLM addresses clusters by their CURRENT-state hashes,
        // and the final population reflects the post-evolution state.
        if !report.final_population.is_empty()
            && let Some(api_cfg_for_cluster) = api_cfg.as_ref()
        {
            let k_for_island = last_steering
                .as_ref()
                .and_then(|s| s.get("cluster_config"))
                .and_then(|cc| cc.get("k_per_island"))
                .and_then(|m| m.get(canonical_domain))
                .and_then(|v| v.as_u64())
                .map(|v| v.clamp(2, 12) as u32)
                .unwrap_or(6);
            // Deterministic per-chunk seed so re-running the same
            // chunk reproduces the same cluster assignments.
            let chunk_seed = (chunk_i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
            // final_population is `(chain, comps, names, cluster_id)`;
            // cluster_and_summarise wants `(chain, comps, names)`.
            let final_3tuple: Vec<(_, [f32; 4], Vec<String>)> = report
                .final_population
                .iter()
                .map(|(c, f, n, _)| (c.clone(), *f, n.clone()))
                .collect();
            let (summaries, _assignment) = nasrudin_ga::clustering::cluster_and_summarise(
                &final_3tuple,
                k_for_island,
                canonical_domain,
                chunk_seed,
            );
            tracing::debug!(
                chunk = chunk_i,
                k = k_for_island,
                n_clusters = summaries.len(),
                "chunk clustered"
            );
            let rl_policy_evidence = rl_policy_evidence_for_cluster_report(
                ga_policy,
                active_target_selector_policy.as_deref(),
                worker_rl_eval_snapshot.as_ref(),
            );
            if let Err(e) = post_cluster_report(
                api_cfg_for_cluster,
                chunk_i as i64,
                k_for_island as i16,
                canonical_domain,
                &summaries,
                &rl_policy_evidence,
            )
            .await
            {
                tracing::debug!(error=%e, "cluster_report post failed (non-blocking)");
            }

            // Eligibility-trace bookkeeping for THIS chunk:
            //
            //   1. Compute the per-cluster post-evolution mean from
            //      the final population grouped by lineage cluster_id
            //      (same-chunk lineage signal).
            //   2. For each NEW trace started this chunk (sample[0]),
            //      look up its lineage cluster's post mean.
            //   3. For each ALREADY-IN-FLIGHT trace, hash-match
            //      against the current chunk's centroid hashes to
            //      find a successor cluster (cross-chunk identity).
            //   4. Decrement chunks_remaining; finalise traces that
            //      reach 0 by computing the γ-discounted reward and
            //      posting it.
            if !directive_traces.is_empty() {
                use std::collections::HashMap;
                let mut sums: HashMap<u32, (f64, u32)> = HashMap::new();
                for (_, comps, _, cid) in &report.final_population {
                    let mean = (comps.iter().sum::<f32>() / 4.0) as f64;
                    let e = sums.entry(*cid).or_insert((0.0, 0));
                    e.0 += mean;
                    e.1 += 1;
                }
                let seed_centroids: Vec<(u32, u64)> = seed_summaries
                    .iter()
                    .map(|s| (s.cluster_id, s.centroid_skeleton_hash))
                    .collect();
                let now_centroids: Vec<(u32, u64)> = summaries
                    .iter()
                    .map(|s| (s.cluster_id, s.centroid_skeleton_hash))
                    .collect();
                let new_index_set: std::collections::HashSet<usize> =
                    new_trace_indices.iter().copied().collect();
                for (i, trace) in directive_traces.iter_mut().enumerate() {
                    if trace.chunks_remaining == 0 {
                        continue;
                    }
                    let sample = if new_index_set.contains(&i) {
                        // sample[0]: lineage grouping from final_population
                        // for the seed cluster the directive landed on.
                        match nasrudin_ga::clustering::match_directive_to_cluster(
                            trace.centroid_hash_at_apply,
                            &seed_centroids,
                            0.10,
                        ) {
                            Some(seed_cid) => sums
                                .get(&seed_cid)
                                .map(|(s, n)| (s / (*n as f64).max(1.0)) as f32)
                                .unwrap_or(trace.mean_fitness_at_apply),
                            None => trace.mean_fitness_at_apply,
                        }
                    } else {
                        // sample[t≥1]: cross-chunk hash match against
                        // the post-evolution clustering of this chunk.
                        match nasrudin_ga::clustering::match_directive_to_cluster(
                            trace.centroid_hash_at_apply,
                            &now_centroids,
                            0.10,
                        ) {
                            Some(cid) => summaries
                                .iter()
                                .find(|s| s.cluster_id == cid)
                                .map(|s| s.mean_fitness)
                                .unwrap_or(
                                    *trace.samples.last().unwrap_or(&trace.mean_fitness_at_apply),
                                ),
                            None => *trace.samples.last().unwrap_or(&trace.mean_fitness_at_apply),
                        }
                    };
                    trace.samples.push(sample);
                    trace.chunks_remaining = trace.chunks_remaining.saturating_sub(1);
                }

                // Finalise traces that reached the horizon.
                let mut feedback_batch: Vec<serde_json::Value> = Vec::new();
                directive_traces.retain(|trace| {
                    if trace.chunks_remaining > 0 {
                        return true;
                    }
                    let reward = trace.discounted_reward();
                    feedback_batch.push(serde_json::json!({
                        "island_domain": canonical_domain,
                        "action": trace.action,
                        "strength_bucket": trace.strength_bucket,
                        "multiplier_choice": trace.multiplier_choice,
                        "reward": reward,
                    }));
                    false
                });
                if !feedback_batch.is_empty() {
                    if let Err(e) =
                        post_directive_feedback(api_cfg_for_cluster, &feedback_batch).await
                    {
                        tracing::debug!(error=%e,
                            "directive_feedback post failed (non-blocking)");
                    } else {
                        tracing::info!(
                            n = feedback_batch.len(),
                            traces_in_flight = directive_traces.len(),
                            "posted directive_feedback batch (γ-discounted)"
                        );
                    }
                }
            }

            // Compute-bandit reward attribution: a single chunk-wide
            // signal — `discoveries_per_pop` (verified-theorem yield
            // per individual). Higher-throughput chunks reward the
            // compute multiplier that produced them; the bandit
            // converges on multipliers that turn extra compute into
            // proportionally more discoveries. AlphaProof-style
            // test-time-compute scaling: spend more where it pays.
            if !pending_compute_pulls.is_empty()
                && let Some(api_cfg_for_cluster) = api_cfg.as_ref()
            {
                let pop_used = chunk_config.population_size.max(1) as f64;
                let yield_per_pop = report.verified.len() as f64 / pop_used;
                // Map to [0, 1]: assume 0.05 verified/individual is
                // a strong chunk; saturate above. Tunable.
                let reward = (yield_per_pop / 0.05).clamp(0.0, 1.0);
                let mut feedback_batch: Vec<serde_json::Value> = Vec::new();
                for (dom, bucket, choice, _pop_at_apply) in pending_compute_pulls.iter() {
                    feedback_batch.push(serde_json::json!({
                        "island_domain": dom,
                        "strength_bucket": bucket,
                        "multiplier_choice": choice,
                        "reward": reward,
                    }));
                }
                if let Err(e) = post_compute_feedback(api_cfg_for_cluster, &feedback_batch).await {
                    tracing::debug!(error=%e,
                        "compute_feedback post failed (non-blocking)");
                } else {
                    tracing::info!(
                        n = feedback_batch.len(),
                        reward,
                        yield_per_pop,
                        "posted compute_feedback batch"
                    );
                }
            }
        }

        total_candidates += report.total_candidates;
        total_unique += report.unique_executable;
        total_lake += report.lake_attempts;
        total_lake_passed += report.lake_passed;
        total_persistent_attempts += report.persistent_attempts;
        total_dim_rejected += report.dim_rejected;
        total_pre_lake_rejected += report.pre_lake_rejected;
        if !report.verified.is_empty() {
            println!(
                "▶ chunk {}/{}: {} verified, {} lake attempts",
                chunk_i + 1,
                chunks,
                report.verified.len(),
                report.lake_attempts
            );
            // Submit each chunk's discoveries immediately so peer
            // workers see them on their next periodic re-sync.
            //
            // Items in report.verified came from one of two paths:
            //
            //   * Local lake-build (default): pass worker_verified=true
            //     so the server flips directly to LakeVerified on
            //     chain-replay success — kernel has already confirmed
            //     the theorem and we don't need the lake-promotion
            //     drain to redo it.
            //
            //   * `--no-local-lake` dev mode: the GA harvested top-K
            //     novel candidates and pushed them into report.verified
            //     without lake. Pass worker_verified=false so the
            //     server's lazy lake-promotion drain handles kernel
            //     confirmation before they enter /api/seed.
            if let (Some(cfg), Some(_)) = (api_cfg.as_ref(), prover_root.as_ref()) {
                let worker_verified = !no_local_lake;
                for d in &report.verified {
                    if let Err(e) = submit_discovery(cfg, &domain, d, worker_verified).await {
                        eprintln!("  ! chunk-submit failed: {e}");
                    }
                }
            }
        }
        // Heartbeat counters: cumulative gens advanced + theorems produced
        // this run. The background task reads these every 30 s; bumping
        // here ensures /api/workers reflects real progress at chunk
        // boundaries (between chunks, the counters stay flat — that's
        // fine, the heartbeat itself still ticks via uptime_seconds).
        hb_gen.fetch_add(gens_per_chunk as u64, Ordering::Relaxed);
        hb_thms.fetch_add(report.verified.len() as u64, Ordering::Relaxed);
        combined_verified.extend(report.verified);
    }

    // Backwards-compatible report shim — code below expects `report.*`.
    let report = nasrudin_ga::chain_engine::DiscoveryReport {
        generations_run: gens_per_chunk * chunks,
        total_candidates,
        unique_executable: total_unique,
        lake_attempts: total_lake,
        lake_passed: total_lake_passed,
        persistent_attempts: total_persistent_attempts,
        dim_rejected: total_dim_rejected,
        pre_lake_rejected: total_pre_lake_rejected,
        verified: combined_verified,
        top_fitness_canonical: None,
        final_population: vec![],
        mutation_operator_stats: worker_rl_scope_state.mutation_operator,
        qd_archive_stats: worker_rl_scope_state.qd_archive,
    };

    if let Some(target_name) = target_name_for_elite {
        let key = target_portfolio_key(&domain, target_name);
        let stats = worker_rl_state
            .target_portfolio
            .entry(key.clone())
            .or_default();
        update_target_portfolio(stats, target_name, &report, store.len(), now_unix_secs());
        let pulls = stats.pulls;
        let mean_reward = stats.total_reward / stats.pulls.max(1) as f64;
        let last_reward = stats.last_reward;
        if let Some(policy) = active_target_selector_policy.as_deref() {
            let policy_key = target_selector_policy_key(&domain, policy);
            let policy_stats = worker_rl_state
                .target_selector_policies
                .entry(policy_key)
                .or_default();
            update_target_selector_policy(policy_stats, strategy_genome_reward(&report));
        }
        if let Err(e) = save_worker_rl_state(&worker_rl_state_path, &worker_rl_state) {
            tracing::warn!(
                error = %e,
                path = %worker_rl_state_path.display(),
                "failed to persist target portfolio RL state"
            );
        } else {
            tracing::debug!(
                key,
                pulls,
                mean_reward,
                last_reward,
                "updated target portfolio RL state"
            );
        }
    }

    println!("▶ Run complete.");
    println!("    Generations:         {}", report.generations_run);
    println!("    Total candidates:    {}", report.total_candidates);
    println!("    Unique executable:   {}", report.unique_executable);
    println!("    Dimension rejected:  {}", report.dim_rejected);
    println!("    Pre-lake rejected:   {}", report.pre_lake_rejected);
    println!("    Lake attempts:       {}", report.lake_attempts);
    println!("    Lake passed:         {}", report.lake_passed);
    if report.lake_attempts > 0 {
        let pass_rate = (report.lake_passed as f64 / report.lake_attempts as f64) * 100.0;
        println!("    Pass rate:           {pass_rate:.2}%");
    }
    println!("    Persistent attempts: {}", report.persistent_attempts);
    println!("    Verified theorems:   {}", report.verified.len());
    if let Some(top) = &report.top_fitness_canonical {
        println!("    Top-fitness final: {top}");
    }
    println!();

    if report.verified.is_empty() {
        println!("▶ No theorems verified this run.");
        println!("  This is expected for short runs — the search space is large.");
        println!("  See `progress.md` Phase 6+ for next-step heuristics.");
    } else {
        println!("▶ Verified discoveries:");
        for d in &report.verified {
            println!();
            println!("  ── Generation {} ──", d.generation);
            println!("    canonical: {}", d.canonical);
            println!("    chain length: {}", d.chain.len());
            println!("    chain steps:");
            for (i, step) in d.chain.0.iter().enumerate() {
                println!("      {}: {step:?}", i + 1);
            }
            println!("    Lean module: {}", d.module_path);
            // Detect the rest-energy theorem.
            if d.canonical
                .contains("(= v:E (* v:m (^ c:SpeedOfLight n:2)))")
                || d.canonical.contains("E = m * c^2")
                || d.canonical
                    .contains("(= v:E (* (^ c:SpeedOfLight n:2) v:m))")
            {
                println!();
                println!("  ★ E = m·c² SPONTANEOUSLY DERIVED AND VERIFIED ★");
            }
            if d.canonical.contains("(= v:Eph (* v:hbar v:omega))")
                || d.canonical.contains("(= v:Eph (* v:omega v:hbar))")
                || d.canonical.contains("Eph = hbar * omega")
            {
                println!();
                println!("  ★ QUANTUM PLANCK-EINSTEIN RELATION DERIVED AND VERIFIED ★");
            }
        }

        // ── Submit to /api/ingest, then erase the on-disk Discover*.lean
        //    files so nothing persists in `prover/PhysicsGenerator/Derived/`
        //    going forward (Phase 9 acceptance criterion #14).
        if let (Some(cfg), Some(prover)) = (api_cfg.as_ref(), prover_root.as_ref()) {
            println!();
            println!(
                "▶ Submitting {} discoveries to {}",
                report.verified.len(),
                cfg.api_url
            );
            let domain_str = domain.clone();
            let worker_verified = !no_local_lake;
            for d in &report.verified {
                match submit_discovery(cfg, &domain_str, d, worker_verified).await {
                    Ok(()) => {
                        println!("  ✓ submitted: {} (gen {})", d.canonical, d.generation);
                    }
                    Err(e) => {
                        // Don't abort: the lake build already proved the
                        // math is correct locally. Failed submissions can
                        // be retried later (Phase 9 v2).
                        eprintln!(
                            "  ! submit failed for gen {} ({}): {e}",
                            d.generation, d.canonical
                        );
                    }
                }
                // Always delete the local .lean file. Even if the POST
                // failed, we don't want `Discover*.lean` to accumulate
                // in the prover dir — that's the whole point of Task 7.1.
                if let Err(e) = remove_module_file(prover, &d.module_path) {
                    eprintln!(
                        "  ! could not remove {} from prover dir: {e}",
                        d.module_path
                    );
                }
            }
        }
    }
    println!();
}

/// Phase E: run one claimed conjecture against an LLM-suggested seed.
///
/// 1. Parse `seed: serde_json::Value` into an `LlmSuggestion`.
/// 2. Build a *filtered* `AxiomStore` containing only the axioms named in
///    `axiom_set`. Anything not present in the worker's full store is
///    skipped with a warning. Classical-mechanics postulates are always
///    layered in as a kinematic baseline (matches non-research-mode).
/// 3. Run a series of small chunks (≤30s each) until the budget exhausts.
///    Between chunks, heartbeat with current counters and submit each
///    verified theorem to `/api/conjecture/{id}/submit`.
/// 4. Complete with `Verified` (≥1 theorem submitted) or `NoResult`.
#[allow(clippy::too_many_arguments)]
async fn run_seed_driven_chunk(
    client: &nasrudin_ga::research_client::ResearchClient,
    cfg: &ApiSubmitConfig,
    domain: &str,
    full_store: &AxiomStore,
    job: &nasrudin_ga::research_client::ClaimedJob,
    max_chain_len: usize,
    prover_root: Option<&Path>,
    max_lake: usize,
    rejected_canonicals: std::sync::Arc<std::collections::HashSet<Vec<u8>>>,
    novelty_bloom: Option<std::sync::Arc<bloomfilter::Bloom<[u8]>>>,
    rng: &mut impl rand::Rng,
) -> anyhow::Result<()> {
    use nasrudin_ga::chain_engine::{DiscoveryConfig, run_discovery};
    use nasrudin_ga::research_client::*;

    // 1. Parse the seed.
    let suggestion: SeedSuggestion = match serde_json::from_value(job.seed.clone()) {
        Ok(s) => s,
        Err(e) => {
            // Non-conformant seed JSON: fail the job with NoResult so the
            // researcher can resubmit. Avoid stalling the lease.
            client
                .complete(
                    job.job_id,
                    &CompleteBody {
                        outcome: "NoResult".into(),
                        reason: Some(format!("seed_parse_error: {e}")),
                    },
                )
                .await?;
            anyhow::bail!("seed parse failed: {e}");
        }
    };

    // 2. Filter the AxiomStore to the LLM-supplied subset.
    //
    // The LLM names 10–100 axioms per conjecture; first-touch on each is a
    // cold-tier RocksDB seek. `get_many` collapses them into one
    // `multi_get_cf` round-trip — minus the LRU/hot hits — so a 100-axiom
    // suggestion costs O(1) disk seek instead of O(100).
    let mut filtered = AxiomStore::new();
    filtered.load_classical_mechanics_postulates();
    let names: Vec<&str> = suggestion.axiom_set.iter().map(|s| s.as_str()).collect();
    let resolved = full_store.get_many(&names);
    let mut missing = Vec::<String>::new();
    for (name, axiom_opt) in suggestion.axiom_set.iter().zip(resolved.into_iter()) {
        match axiom_opt {
            Some(a) => filtered.register(a),
            None => missing.push(name.clone()),
        }
    }
    if !missing.is_empty() {
        eprintln!(
            "  ! conjecture {} references {} unknown axiom(s); ignored: {:?}",
            job.job_id,
            missing.len(),
            missing,
        );
    }

    // 2a. Layer the LLM's initial_population as synthetic seed axioms so
    // the GA can introduce them via `IntroduceAxiom`. Each parseable
    // s-expression becomes a `seed_<idx>` axiom; unparseable strings are
    // logged and skipped.
    for (idx, src) in suggestion.initial_population.iter().enumerate() {
        match nasrudin_core::parse::parse_sexpr(src) {
            Ok(expr) => {
                filtered.register(nasrudin_derive::axiom_store::Axiom {
                    name: format!("seed_{idx}"),
                    domain: nasrudin_core::Domain::PureMath,
                    statement: expr,
                    description: format!("LLM-suggested seed: {src}"),
                });
            }
            Err(e) => {
                tracing::debug!("conjecture seed[{idx}] parse failed ({e}): {src}");
            }
        }
    }

    if filtered.is_empty() {
        client
            .complete(
                job.job_id,
                &CompleteBody {
                    outcome: "NoResult".into(),
                    reason: Some("no_axioms_resolvable_from_seed".into()),
                },
            )
            .await?;
        return Ok(());
    }

    // 3. Build the constrained DiscoveryConfig.
    let wall_seconds = job
        .budget
        .get("wall_seconds")
        .and_then(|v| v.as_u64())
        .unwrap_or(600);
    let max_candidates = job
        .budget
        .get("max_candidates")
        .and_then(|v| v.as_u64())
        .unwrap_or(100_000);
    let mutation_priors = if suggestion.mutation_priors.is_empty() {
        None
    } else {
        Some(suggestion.mutation_priors.clone())
    };

    let chunk_seconds: u64 = 30; // bounded heartbeat cadence
    let chunk_gens: usize = 25; // small enough that one chunk runs in ~chunk_seconds

    let started = std::time::Instant::now();
    let mut total_attempted: u64 = 0;
    let mut total_verified: u32 = 0;
    let mut submitted_any = false;

    // Research-mode also benefits from the dimension hard-reject; same
    // env-var check (workers run with one global config). Build a
    // domain-aware var-dim table from the conjecture's nominal domain
    // (string passed in from the parent run).
    let research_domain = match domain {
        "sr" => nasrudin_core::Domain::SpecialRelativity,
        "em" => nasrudin_core::Domain::Electromagnetism,
        _ => nasrudin_core::Domain::PureMath,
    };
    let research_dim_var_dims = std::sync::Arc::new(nasrudin_derive::domain_variable_dimensions(
        &research_domain,
    ));
    let research_dim_hard_reject = std::env::var("NASRUDIN_DIMENSION_HARD_REJECT")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true);

    while started.elapsed().as_secs() < wall_seconds && total_attempted < max_candidates {
        let chunk_config = DiscoveryConfig {
            population_size: 32,
            generations: chunk_gens,
            crossover_rate: 0.6,
            mutation_rate: 0.7,
            tournament_size: 3,
            max_chain_len,
            prover_root: prover_root.map(|p| p.to_path_buf()),
            max_lake_verifications: if prover_root.is_some() { max_lake } else { 0 },
            target: None,
            rejected_canonicals: rejected_canonicals.clone(),
            cache_ctx: None,
            novelty_bloom: novelty_bloom.clone(),
            mutation_priors: mutation_priors.clone(),
            // research-mode submit path is its own conjecture-flow
            // endpoint and doesn't share the /api/ingest pipeline that
            // P-Task 11 unblocks. Stay on the legacy lake-locally
            // pattern here; if a research-mode worker wants to skip
            // local lake too it can be wired in a follow-up.
            submit_unverified_top_k: 0,
            dimension_hard_reject: research_dim_hard_reject,
            dimension_var_dims: research_dim_var_dims.clone(),
            // Research-mode chunks share the same persistent elaborator
            // as the main run (one per worker). When the parent run has
            // no elaborator (lake-only path), this stays None and the
            // chunk falls back to legacy lake build.
            elaborator: None,
            // research-mode chunks pre-date the cluster steerer's
            // per-chunk knob plumbing; pass uniform defaults for now.
            // (When the legacy /api/conjecture flow is folded into
            // /api/research/jobs the steering knobs will land here too.)
            suffix_bias: 0.0,
            elitism_fraction: 0.0,
            // Research-mode does not (yet) participate in cluster
            // reporting, so skip the final-population snapshot.
            collect_final_population: false,
            cluster_multipliers: std::collections::HashMap::new(),
            cluster_assignments: vec![],
            atom_pool: None,
            // Research-mode jobs target an LLM-supplied conjecture, not
            // sr_rest_energy — no permanent elite makes sense here.
            permanent_elite: None,
            llm_proposed_chains: Vec::new(),
        };
        let report = run_discovery(&filtered, &chunk_config, rng);
        total_attempted += report.total_candidates as u64;

        // Submit each verified theorem to the conjecture's submit endpoint.
        for d in &report.verified {
            let body = SubmitBody {
                engine_git_sha: "unknown".into(),
                lean_version: "4.27.0".into(),
                theorem: SubmitTheorem {
                    canonical_statement: d.canonical.clone(),
                    domain: domain.to_string(),
                    lean_source: d.lean_source.clone(),
                    chain: chain_to_json(&d.chain),
                    axioms_used: axioms_used(&d.chain),
                    depth: Some(d.chain.len() as u32),
                    generation: Some(d.generation as u64),
                },
            };
            match client.submit(job.job_id, &body).await {
                Ok(r) => {
                    println!("    ✓ conjecture submit: {}", r.theorem_id);
                    total_verified += 1;
                    submitted_any = true;
                }
                Err(e) => {
                    eprintln!("    ! conjecture submit failed: {e}");
                }
            }
        }

        // Heartbeat extends the lease and surfaces progress to the SSE feed.
        let elapsed_s = started.elapsed().as_secs() as u32;
        let _ = client
            .heartbeat(
                job.job_id,
                &HeartbeatBody {
                    candidates_attempted: total_attempted.min(i32::MAX as u64) as i32,
                    candidates_verified: total_verified as i32,
                    time_elapsed_s: elapsed_s,
                },
            )
            .await;

        // Bail early if this chunk took the full slice but produced nothing
        // executable — likely a degenerate axiom subset.
        if started.elapsed().as_secs() >= wall_seconds {
            break;
        }
        if started.elapsed().as_secs() < chunk_seconds {
            // small breather so heartbeats don't pile up at machine speed
            tokio::time::sleep(std::time::Duration::from_millis(200)).await;
        }
    }

    let outcome = if submitted_any {
        "Verified"
    } else {
        "NoResult"
    };
    let reason = format!(
        "candidates_attempted={total_attempted} verified={total_verified} elapsed_s={}",
        started.elapsed().as_secs()
    );
    client
        .complete(
            job.job_id,
            &CompleteBody {
                outcome: outcome.into(),
                reason: Some(reason),
            },
        )
        .await?;
    println!(
        "▶ conjecture {} → {outcome} ({} verified, {} attempted)",
        job.job_id, total_verified, total_attempted
    );
    let _ = cfg; // worker_id is implicit in the bearer
    Ok(())
}

/// Local mirror of physics-api's LlmSuggestion. Workers don't depend on
/// the api crate, so we keep a structurally-identical type here. Round-trips
/// through the seed JSON the API stored from the LLM call.
#[derive(serde::Deserialize)]
#[allow(dead_code)] // target_shape and rationale are reserved for future heuristics
struct SeedSuggestion {
    #[serde(default)]
    axiom_set: Vec<String>,
    #[serde(default)]
    initial_population: Vec<String>,
    #[serde(default)]
    mutation_priors: std::collections::HashMap<String, f32>,
    #[serde(default)]
    target_shape: Option<String>,
    #[serde(default)]
    rationale: String,
}

fn arg_value<T: std::str::FromStr>(args: &[String], flag: &str) -> Option<T> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|pos| args.get(pos + 1))
        .and_then(|s| s.parse().ok())
}

/// Milestone 1: map a target spec name to the hand-coded "known-good"
/// chain that hits it. Returns `None` when no such chain is registered
/// for the given target, or when the user has set
/// `NASRUDIN_M1_SEED_ELITE=0` to opt out (M1.d acceptance run).
///
/// Registered seed chains:
/// - `sr_rest_energy`            → `Chain::rest_energy_from_upstream`
/// - `qm_planck_einstein`        → `Chain::planck_einstein_from_upstream`
/// - `qm_schrodinger`            → `Chain::schrodinger_from_upstream`
/// - `thermo_boltzmann_entropy`  → `Chain::boltzmann_entropy_from_upstream`
/// - `newton_second`             → `Chain::newton_second_from_upstream`
/// - `gr_einstein_field_equation` → `Chain::einstein_field_no_lambda_from_upstream`
///
/// `em_gauss_law` is intentionally NOT registered: the electromagnetism
/// upstream store has no `div E`, `rho`, or `VacuumPermittivity` axioms,
/// so `∇·E = ρ/ε₀` is not derivable from the existing postulate set
/// without inventing axioms (which would itself be a no-cheat
/// violation). `thermo_boltzmann_entropy` takes that slot as the M1.b
/// "second domain" anchor.
///
/// As Milestone 3 progresses and more domains get hand-coded baselines,
/// add their mappings here.
fn m1_seed_elite_for(target_name: Option<&str>) -> Option<Chain> {
    let enabled = std::env::var("NASRUDIN_M1_SEED_ELITE")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true);
    if !enabled {
        return None;
    }
    match target_name {
        Some("sr_rest_energy") => Some(Chain::rest_energy_from_upstream()),
        Some("qm_planck_einstein") => Some(Chain::planck_einstein_from_upstream()),
        Some("qm_schrodinger" | "schrodinger") => Some(Chain::schrodinger_from_upstream()),
        Some("thermo_boltzmann_entropy" | "boltzmann_entropy") => {
            Some(Chain::boltzmann_entropy_from_upstream())
        }
        Some("newton_second" | "f_eq_ma") => Some(Chain::newton_second_from_upstream()),
        Some("gr_einstein_field_equation" | "einstein_field_equation") => {
            Some(Chain::einstein_field_no_lambda_from_upstream())
        }
        _ => None,
    }
}

/// Submission config sourced from env. Worker key is required.
struct ApiSubmitConfig {
    api_url: String,
    worker_key: String,
    worker_id: String,
}

impl ApiSubmitConfig {
    fn from_env() -> Result<Self, String> {
        let worker_key = std::env::var("NASRUDIN_WORKER_KEY").map_err(|_| {
            "NASRUDIN_WORKER_KEY is required for verified-discovery submission".to_string()
        })?;
        if worker_key.trim().is_empty() {
            return Err("NASRUDIN_WORKER_KEY is empty".to_string());
        }
        let api_url =
            std::env::var("NASRUDIN_API_URL").unwrap_or_else(|_| DEFAULT_API_URL.to_string());
        let worker_id =
            std::env::var("NASRUDIN_WORKER_ID").unwrap_or_else(|_| DEFAULT_WORKER_ID.to_string());
        Ok(Self {
            api_url,
            worker_key,
            worker_id,
        })
    }
}

/// Serialize a chain for the wire. `RuleStep` derives `#[serde(tag = "kind")]`
/// so the array shape is `[{"kind": "IntroduceAxiom", "axiom_name": …}, …]`.
/// `RearrangeEquation.target` and `SubstituteValue.value` are serialized as
/// full Expr trees (not canonical strings) so the server can replay the
/// chain against its own AxiomStore in reverify::check_chain.
fn chain_to_json(chain: &Chain) -> serde_json::Value {
    serde_json::to_value(&chain.0).expect("RuleStep is Serialize")
}

/// Pull every IntroduceAxiom name out of the chain (deduplicated, in
/// first-seen order).
fn axioms_used(chain: &Chain) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for step in &chain.0 {
        if let RuleStep::IntroduceAxiom { axiom_name } = step {
            if !out.iter().any(|a| a == axiom_name) {
                out.push(axiom_name.clone());
            }
        }
    }
    out
}

/// POST a per-chunk cluster report to `/api/cluster-report`. The
/// API steerer reads `cluster_reports` rows for both UCB1 reward
/// (which K worked) and the LLM prompt's `cluster_summaries` block
/// (semantic reasoning over per-cluster axioms / fitness). Soft-fails
/// — a missing/down API never blocks the GA chunk loop.
async fn post_cluster_report(
    cfg: &ApiSubmitConfig,
    chunk_index: i64,
    k_used: i16,
    island_domain: &str,
    summaries: &[nasrudin_ga::clustering::ClusterSummary],
    rl_policy_evidence: &serde_json::Value,
) -> anyhow::Result<()> {
    let summaries_json: Vec<serde_json::Value> = summaries
        .iter()
        .map(|s| {
            let mut value = serde_json::to_value(s).unwrap_or(serde_json::Value::Null);
            if let serde_json::Value::Object(map) = &mut value {
                map.insert("rl_policy_evidence".into(), rl_policy_evidence.clone());
            }
            value
        })
        .collect();
    // The endpoint stores worker_id as PG UUID. Production workers
    // typically have a string identifier (e.g. "pool-worker-1"); derive
    // a deterministic UUID v5 in the DNS namespace so reports from
    // the same logical worker collapse to the same row regardless of
    // restart, and we never need server-side worker provisioning just
    // for cluster reports.
    let worker_uuid = uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_DNS, cfg.worker_id.as_bytes());
    let body = serde_json::json!({
        "worker_id": worker_uuid,
        "chunk_index": chunk_index,
        "k_used": k_used,
        "island_reports": [{
            "island_domain": island_domain,
            "summaries": summaries_json,
        }]
    });
    let client = reqwest::Client::new();
    let resp = client
        .post(format!("{}/api/cluster-report", cfg.api_url))
        .bearer_auth(&cfg.worker_key)
        .json(&body)
        .send()
        .await?;
    resp.error_for_status()?;
    Ok(())
}

/// Look up the arms for a (island, action, strength_bucket) slot
/// from a seed payload's compact `directive_arms` snapshot. Returns
/// an empty Vec if the slot isn't present (cold boot before the
/// steerer cycle has run). Each arm tuple is
/// `(choice, pulls, total_reward_sum, linucb_score?)`. The LinUCB
/// score is the server-computed contextual score; `None` until
/// the LinUCB row reaches its warmup pull count.
fn directive_arms_for_slot(
    seed_value: &serde_json::Value,
    island_domain: &str,
    action: &str,
    strength_bucket: u8,
) -> Vec<(u8, i64, f64, Option<f64>)> {
    let Some(snapshot) = seed_value
        .get("directive_arms")
        .and_then(|v| v.get("snapshot"))
        .and_then(|v| v.as_array())
    else {
        return vec![];
    };
    for slot in snapshot {
        if slot.get("island_domain").and_then(|v| v.as_str()) == Some(island_domain)
            && slot.get("action").and_then(|v| v.as_str()) == Some(action)
            && slot.get("strength_bucket").and_then(|v| v.as_i64()) == Some(strength_bucket as i64)
        {
            let arms = slot
                .get("arms")
                .and_then(|v| v.as_array())
                .cloned()
                .unwrap_or_default();
            return arms
                .into_iter()
                .filter_map(|a| {
                    let choice = a.get("multiplier_choice").and_then(|v| v.as_u64())? as u8;
                    let pulls = a.get("pulls").and_then(|v| v.as_i64())?;
                    let mean = a.get("mean_reward").and_then(|v| v.as_f64())?;
                    let total = mean * pulls as f64;
                    let linucb = a.get("linucb_score").and_then(|v| v.as_f64());
                    Some((choice, pulls, total, linucb))
                })
                .collect();
        }
    }
    vec![]
}

/// Pick a multiplier_choice for one (island, action, strength_bucket)
/// slot. Three regimes blended by total pull count:
///
/// 1. **Cold start** (total < 15): fall back to the static linear
///    strength → choice map. The bandit hasn't seen enough data to
///    pick anything meaningful.
/// 2. **Per-arm UCB1** (15 ≤ total < 100): classic UCB1 over the
///    discrete arm rewards.
/// 3. **Blended UCB1 + LinUCB** (total ≥ 100): when LinUCB has
///    enough pulls, blend its contextual score with UCB1's
///    per-arm score. Weight ramps linearly to 100% LinUCB at
///    total=200, so the contextual layer takes over once it has
///    reliable predictions.
fn pick_multiplier_choice(arms: &[(u8, i64, f64, Option<f64>)], strength: f32) -> u8 {
    const COLD_START: i64 = 15;
    const LINUCB_FULL_WEIGHT_AT: f64 = 200.0;
    let total: i64 = arms.iter().map(|(_, p, _, _)| *p).sum();
    if arms.is_empty() || total < COLD_START {
        return (strength.clamp(0.0, 1.0) * 5.0).floor().min(4.0) as u8;
    }
    if let Some((c, _, _, _)) = arms.iter().find(|(_, p, _, _)| *p == 0) {
        return *c;
    }
    let ln_n = (total as f64).ln();
    // Blend weight: 0.0 below LINUCB_FULL_WEIGHT_AT*0.5, ramps to
    // 1.0 at LINUCB_FULL_WEIGHT_AT. Keeps UCB1 dominant while
    // LinUCB warms up; flips to contextual once it's reliable.
    let blend = ((total as f64 - 50.0) / (LINUCB_FULL_WEIGHT_AT - 50.0)).clamp(0.0, 1.0);
    let mut best_choice = arms[0].0;
    let mut best_score = f64::NEG_INFINITY;
    for &(c, p, t, linucb) in arms {
        let mean = if p > 0 { t / p as f64 } else { 0.0 };
        let exploration = (2.0 * ln_n / p as f64).sqrt();
        let ucb1_score = mean + exploration;
        let score = match linucb {
            Some(l) => (1.0 - blend) * ucb1_score + blend * l,
            None => ucb1_score,
        };
        if score > best_score {
            best_score = score;
            best_choice = c;
        }
    }
    best_choice
}

fn lookup_action_multiplier(action: &str, choice: u8) -> f32 {
    let i = (choice as usize).min(4);
    match action {
        "boost" => [1.00, 1.25, 1.50, 1.75, 2.00][i],
        "exploit" => [1.00, 1.25, 1.50, 1.75, 2.00][i],
        "diversify" => [0.00, 0.10, 0.20, 0.30, 0.50][i],
        "kill" => [0.00, 0.10, 0.20, 0.30, 0.50][i],
        _ => 1.0,
    }
}

/// Compute-scaling multiplier table. Mirrors
/// `directive_bandit::COMPUTE_MULTIPLIERS` server-side.
fn lookup_compute_multiplier(choice: u8) -> f32 {
    let i = (choice as usize).min(4);
    [0.50, 0.75, 1.00, 1.50, 3.00][i]
}

/// Look up the compute arms for a (island, strength_bucket) slot
/// from the seed payload's `compute_arms` snapshot. Returns 4-tuples
/// `(choice, pulls, total_reward_sum, linucb_score?)` so the same
/// `pick_multiplier_choice` selector works for compute too. The
/// LinUCB score is read from the per-arm JSON if present (set by
/// the compute LinUCB layer when it warms up); `None` otherwise.
fn compute_arms_for_slot(
    seed_value: &serde_json::Value,
    island_domain: &str,
    strength_bucket: u8,
) -> Vec<(u8, i64, f64, Option<f64>)> {
    let Some(snapshot) = seed_value
        .get("compute_arms")
        .and_then(|v| v.get("snapshot"))
        .and_then(|v| v.as_array())
    else {
        return vec![];
    };
    for slot in snapshot {
        if slot.get("island_domain").and_then(|v| v.as_str()) == Some(island_domain)
            && slot.get("strength_bucket").and_then(|v| v.as_i64()) == Some(strength_bucket as i64)
        {
            return slot
                .get("arms")
                .and_then(|v| v.as_array())
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .filter_map(|a| {
                    let choice = a.get("multiplier_choice").and_then(|v| v.as_u64())? as u8;
                    let pulls = a.get("pulls").and_then(|v| v.as_i64())?;
                    let mean = a.get("mean_reward").and_then(|v| v.as_f64())?;
                    let linucb = a.get("linucb_score").and_then(|v| v.as_f64());
                    Some((choice, pulls, mean * pulls as f64, linucb))
                })
                .collect();
        }
    }
    vec![]
}

/// POST a batch of compute-bandit reward observations to
/// /api/directive-feedback. Reuses the same endpoint with
/// action="compute" so the server-side handler can route to
/// `cluster_compute_arms` based on the action sentinel.
async fn post_compute_feedback(
    cfg: &ApiSubmitConfig,
    feedback: &[serde_json::Value],
) -> anyhow::Result<()> {
    if feedback.is_empty() {
        return Ok(());
    }
    let body = serde_json::json!({ "feedback": feedback });
    let client = reqwest::Client::new();
    let resp = client
        .post(format!("{}/api/compute-feedback", cfg.api_url))
        .bearer_auth(&cfg.worker_key)
        .json(&body)
        .send()
        .await?;
    resp.error_for_status()?;
    Ok(())
}

/// POST a batch of (arm_key, reward) tuples to /api/directive-feedback.
/// Soft-fails — feedback drops are best-effort, missing pulls just
/// slow the bandit's convergence.
async fn post_directive_feedback(
    cfg: &ApiSubmitConfig,
    feedback: &[serde_json::Value],
) -> anyhow::Result<()> {
    if feedback.is_empty() {
        return Ok(());
    }
    let body = serde_json::json!({ "feedback": feedback });
    let client = reqwest::Client::new();
    let resp = client
        .post(format!("{}/api/directive-feedback", cfg.api_url))
        .bearer_auth(&cfg.worker_key)
        .json(&body)
        .send()
        .await?;
    resp.error_for_status()?;
    Ok(())
}

/// POST a single verified discovery to `/api/ingest`.
///
/// `worker_verified` reflects whether the worker locally lake-built
/// the theorem before calling this. The default flow (no
/// `--no-local-lake`) lake-builds every submitted theorem and passes
/// `true` here; `--no-local-lake` dev mode passes `false` and the
/// server falls back to the lazy lake-promotion drain.
async fn submit_discovery(
    cfg: &ApiSubmitConfig,
    domain: &str,
    d: &VerifiedDiscovery,
    worker_verified: bool,
) -> anyhow::Result<()> {
    submit_to_api(
        &cfg.api_url,
        &cfg.worker_key,
        &cfg.worker_id,
        // No vergen wired up; record "unknown" so the API's required
        // field is non-empty. Phase 9 v2 can plumb VERGEN_GIT_SHA.
        "unknown",
        &d.canonical,
        domain,
        &d.lean_source,
        chain_to_json(&d.chain),
        axioms_used(&d.chain),
        Some(d.chain.len() as u32),
        Some(d.generation as u64),
        worker_verified,
    )
    .await
}

#[allow(clippy::too_many_arguments)]
async fn submit_to_api(
    api_url: &str,
    worker_key: &str,
    worker_id: &str,
    engine_git_sha: &str,
    canonical_statement: &str,
    domain_str: &str,
    lean_source: &str,
    chain_json: serde_json::Value,
    axioms_used: Vec<String>,
    depth: Option<u32>,
    generation: Option<u64>,
    worker_verified: bool,
) -> anyhow::Result<()> {
    let payload = serde_json::json!({
        "worker_id": worker_id,
        "engine_git_sha": engine_git_sha,
        "lean_version": "4.27.0",
        "theorems": [{
            "canonical_statement": canonical_statement,
            "domain": domain_str,
            "lean_source": lean_source,
            "chain": chain_json,
            "axioms_used": axioms_used,
            "depth": depth,
            "generation": generation,
            "worker_verified": worker_verified,
        }]
    });
    let http = nasrudin_ga::worker_http::WorkerHttp::from_env(api_url)?;
    let auth = format!("Bearer {worker_key}");
    let body_bytes = serde_json::to_vec(&payload)?;
    let (status, body) = http
        .post_bytes(
            "/api/ingest",
            body_bytes.into(),
            &[
                ("authorization", auth.as_str()),
                ("content-type", "application/json"),
            ],
        )
        .await?;
    // 200..299 success, 409 (CONFLICT) = duplicate, both treat as ok.
    if (200..300).contains(&status) || status == 409 {
        return Ok(());
    }
    let body_str = String::from_utf8_lossy(&body);
    anyhow::bail!("ingest failed: {status} body={body_str}");
}

/// Translate a Lean module path (e.g.
/// `PhysicsGenerator.Derived.DiscoverGen3`) into its on-disk file
/// (`<prover_root>/PhysicsGenerator/Derived/DiscoverGen3.lean`) and
/// remove it. No-op if the file isn't there.
fn remove_module_file(prover_root: &Path, module_path: &str) -> std::io::Result<()> {
    let relative = format!("{}.lean", module_path.replace('.', "/"));
    let file_path = prover_root.join(&relative);
    if file_path.exists() {
        std::fs::remove_file(&file_path)?;
    }
    Ok(())
}

/// Fetch `/api/seed?domain={d}&top=200` and fold the response into the
/// local AxiomStore. Returns `(axioms_added, peer_theorems_added)`.
///
/// **Axioms** that the server has but we don't are registered as-is.
/// **Peer theorems** with a non-empty replayable chain are replayed
/// locally to extract the final Expr; that Expr is registered as a
/// synthetic axiom named `theorem_<hex_id>`. Anything that fails to
/// parse / replay is silently skipped — we trust only the math we can
/// reproduce locally, not just whatever the API reports.
/// Sync from `/api/seed`. Returns `(axioms_added, peer_theorems_added,
/// steering_payload)`. `steering_payload` is the full JSON value of
/// `body["steering"]` if the server included it, else `None`. The
/// caller passes it to `apply_steering_knobs` to bias the next chunk.
/// True if an axiom NAME is a PhysLean/Mathlib catalog identifier
/// (formalization scaffolding) rather than one of the curated physics
/// postulates. The curated physics axioms — `work_def`, `newton_second`,
/// `minkowski_invariant_def`, `four_momentum_time_component`,
/// `kinetic_energy_def`, `invariant_mass_postulate`, … — never contain any
/// of these namespace tokens, whereas the imported catalog lemmas always
/// do. This is the NAME gate for opaque-placeholder axioms whose statement
/// is a bare var the symbol gate can't flag (note: `minkowskimatrix` is
/// listed, NOT `minkowski`, so the real `minkowski_invariant_def` survives).
fn is_plumbing_axiom_name(name: &str) -> bool {
    let n = name.to_ascii_lowercase();
    const PLUMBING_TOKENS: &[&str] = &[
        "lorentz",
        "spacetime",
        "space_",
        "tensorspecies",
        "fermion",
        "clifford",
        "dfunlike",
        "minkowskimatrix",
        "euclidean",
        "schwartz",
        "veccons",
        "diracform",
        "contrco",
        "contrmetric",
        "contrmod",
        "isorthochronous",
        "toselfadjoint",
        "frompairt",
        "borelspace",
        "measuretheory",
        "γ",
        "ℝequiv",
        "ℂmodule",
        "complexcontrbasis",
        "complexcobasis",
        "ofrat",
        "permt",
    ];
    PLUMBING_TOKENS.iter().any(|t| n.contains(t))
}

async fn fetch_and_extend_store(
    api_url: &str,
    domain: &str,
    store: &mut nasrudin_derive::AxiomStore,
) -> anyhow::Result<(usize, usize, Option<serde_json::Value>)> {
    use nasrudin_core::Expr;
    use nasrudin_derive::{
        Axiom, Chain, DerivationContext, RuleStep, strategies::DerivationStrategy,
    };

    let path = if domain.is_empty() {
        "/api/seed?top=200".to_string()
    } else {
        format!("/api/seed?domain={domain}&top=200")
    };
    let http = nasrudin_ga::worker_http::WorkerHttp::from_env(api_url)?;
    let (status, body_bytes) = http.get_bytes(&path, &[]).await?;
    if !(200..300).contains(&status) {
        anyhow::bail!(
            "seed http {status}: {}",
            String::from_utf8_lossy(&body_bytes)
        );
    }
    let body: serde_json::Value = serde_json::from_slice(&body_bytes)?;

    // Physics-only seeding (lever #1, default ON). Set
    // NASRUDIN_WORKER_PHYSICS_ONLY=0 to restore the old behavior of seeding
    // from the raw catalog (useful only for debugging).
    let physics_only = std::env::var("NASRUDIN_WORKER_PHYSICS_ONLY")
        .map(|v| {
            !matches!(
                v.trim().to_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
        .unwrap_or(true);
    let mut plumbing_skipped = 0usize;

    let mut axioms_added = 0usize;
    if let Some(arr) = body.get("axioms").and_then(|v| v.as_array()) {
        for entry in arr {
            let Some(name) = entry.get("name").and_then(|v| v.as_str()) else {
                continue;
            };
            if store.get(name).is_some() {
                continue;
            }
            // Lever #1 (name gate): many PhysLean catalog axioms are stored
            // as OPAQUE PLACEHOLDERS whose statement is a bare variable (the
            // sanitized lemma name, no dot), so the symbol check below can't
            // see they're plumbing. Their NAMES, however, always carry a
            // PhysLean namespace token (`lorentz…`, `spacetime…`,
            // `tensorspecies…`, etc.) that the ~16 curated physics axioms
            // (`work_def`, `newton_second`, `minkowski_invariant_def`,
            // `four_momentum_time_component`, …) never contain. Gate on the
            // name first so opaque scaffolding can't seed a chain.
            if physics_only && is_plumbing_axiom_name(name) {
                plumbing_skipped += 1;
                continue;
            }
            let Some(stmt_str) = entry.get("statement").and_then(|v| v.as_str()) else {
                continue;
            };
            let Ok(stmt) = serde_json::from_str::<Expr>(stmt_str) else {
                continue;
            };
            // Lever #1 (symbol gate): keep formalization plumbing OUT of the
            // sampleable pool. Imported tensor-category scaffolding uses
            // dotted internal names (`complexLorentzTensor.leftMetric`,
            // `DFunLike.coe`). If the GA can sample those as seed axioms it
            // farms trivially-true restatements — or, worse, loads mutually
            // contradictory ones and "proves" nonsense via ex-falso.
            if physics_only && nasrudin_ga::chain_engine::contains_plumbing_symbol(&stmt) {
                plumbing_skipped += 1;
                continue;
            }
            let domain_str = entry.get("domain").and_then(|v| v.as_str()).unwrap_or("");
            let parsed_domain = match domain_str {
                "SpecialRelativity" | "special_relativity" => {
                    nasrudin_core::Domain::SpecialRelativity
                }
                "Electromagnetism" | "electromagnetism" => nasrudin_core::Domain::Electromagnetism,
                _ => nasrudin_core::Domain::PureMath,
            };
            store.register(Axiom {
                name: name.to_string(),
                domain: parsed_domain,
                statement: stmt,
                description: format!("seed-sync from {api_url}"),
            });
            axioms_added += 1;
        }
    }

    let mut theorems_added = 0usize;
    if let Some(arr) = body.get("seed_theorems").and_then(|v| v.as_array()) {
        for t in arr {
            let chain_val = match t.get("chain_json") {
                Some(c) => c,
                None => continue,
            };
            if chain_val.is_null() {
                continue;
            }
            let Ok(steps): Result<Vec<RuleStep>, _> = serde_json::from_value(chain_val.clone())
            else {
                continue;
            };
            if steps.is_empty() {
                continue;
            }
            let chain = Chain(steps);
            let mut ctx = DerivationContext::new();
            let Ok(final_expr) = chain.execute(store, &mut ctx) else {
                continue;
            };
            // Same plumbing guard as the axiom path: don't fold peer
            // theorems stated in tensor-category internals into the
            // sampleable pool.
            if physics_only && nasrudin_ga::chain_engine::contains_plumbing_symbol(&final_expr) {
                plumbing_skipped += 1;
                continue;
            }

            // Name keyed on canonical-statement bytes so re-pulls don't
            // duplicate. Falls back to the row id hex for robustness.
            let name = if let Some(canon) = t.get("canonical_statement").and_then(|v| v.as_str()) {
                format!(
                    "peer_{:016x}",
                    xxhash_rust::xxh64::xxh64(canon.as_bytes(), 0)
                )
            } else {
                continue;
            };
            if store.get(&name).is_some() {
                continue;
            }

            let domain_str = t.get("domain").and_then(|v| v.as_str()).unwrap_or("");
            let parsed_domain = match domain_str {
                "SpecialRelativity" => nasrudin_core::Domain::SpecialRelativity,
                "Electromagnetism" => nasrudin_core::Domain::Electromagnetism,
                _ => nasrudin_core::Domain::PureMath,
            };
            store.register(Axiom {
                name,
                domain: parsed_domain,
                statement: final_expr,
                description: "peer-verified theorem (seed-sync)".to_string(),
            });
            theorems_added += 1;
        }
    }

    if physics_only && plumbing_skipped > 0 {
        println!(
            "    ⊘ physics-only seeding: skipped {plumbing_skipped} formalization-plumbing entries (kept {axioms_added} axioms + {theorems_added} peer theorems)"
        );
    }

    // Cluster steering. The server folds the live `SteeringConfig`
    // into every `/api/seed` response alongside an etag; we log
    // visibility info here and bubble the payload up to the chunk
    // loop so it can call `apply_steering_knobs` on the next
    // DiscoveryConfig.
    let steering_payload = body.get("steering").cloned();
    if let Some(ref steering) = steering_payload {
        let etag = steering.get("etag").and_then(|v| v.as_str()).unwrap_or("?");
        let scope = steering
            .get("config")
            .and_then(|c| c.get("scope"))
            .and_then(|v| v.as_str())
            .unwrap_or("?");
        tracing::debug!(scope, etag, "worker received steering snapshot");
    }

    Ok((axioms_added, theorems_added, steering_payload))
}

/// Fetch the cluster's rejected-canonical-hash memo from
/// `GET /api/rejected_hashes`. Returns a HashSet of 8-byte
/// canonical-hash bytes (`nasrudin_core::canonical_hash` output) the
/// GA can lookup `O(1)` to skip lake-builds that other workers have
/// already rejected.
///
/// Soft-fail on network or parse errors — running without the memo is
/// strictly worse than running with it, but it's not a correctness
/// issue, just a wasted-compute one.
async fn fetch_rejected_canonicals(
    api_url: &str,
) -> anyhow::Result<std::collections::HashSet<Vec<u8>>> {
    let http = nasrudin_ga::worker_http::WorkerHttp::from_env(api_url)?;
    let (status, body_bytes) = http.get_bytes("/api/rejected_hashes", &[]).await?;
    if !(200..300).contains(&status) {
        anyhow::bail!("rejected_hashes http {status}");
    }
    let body: serde_json::Value = serde_json::from_slice(&body_bytes)?;
    let arr = body
        .get("hashes")
        .and_then(|v| v.as_array())
        .ok_or_else(|| anyhow::anyhow!("expected hashes: [...] in response"))?;
    let mut set = std::collections::HashSet::with_capacity(arr.len());
    for entry in arr {
        let bytes = entry
            .as_array()
            .ok_or_else(|| anyhow::anyhow!("each hash must be an array of bytes"))?
            .iter()
            .map(|n| {
                n.as_u64()
                    .and_then(|x| u8::try_from(x).ok())
                    .ok_or_else(|| anyhow::anyhow!("byte out of range"))
            })
            .collect::<Result<Vec<u8>, _>>()?;
        set.insert(bytes);
    }
    Ok(set)
}

mod embed_autopull {
    //! Worker-side auto-pull of `/api/embed/index.bin`.
    //!
    //! On each chunk iteration, GET `/api/embed/checksum`. If the
    //! local file's BLAKE3 doesn't match the server's, download
    //! `/api/embed/index.bin` (atomic write via `.tmp` + rename) and
    //! rebuild the local HNSW sidecar from the records.

    use anyhow::Result;
    use std::path::Path;

    /// One-shot refresh attempt. Returns `Ok(true)` if the index was
    /// actually swapped, `Ok(false)` if no change needed.
    pub async fn maybe_refresh(api_url: &str, local_path: &Path) -> Result<bool> {
        let http = match nasrudin_ga::worker_http::WorkerHttp::from_env(api_url) {
            Ok(h) => h,
            Err(e) => {
                tracing::debug!("embed http build failed: {e}");
                return Ok(false);
            }
        };
        let (status, body) = match http.get_bytes("/api/embed/checksum", &[]).await {
            Ok(r) => r,
            Err(e) => {
                tracing::debug!("embed checksum fetch failed: {e}");
                return Ok(false);
            }
        };
        if !(200..300).contains(&status) {
            return Ok(false);
        }
        #[derive(serde::Deserialize)]
        struct CsBody {
            hex: String,
        }
        let cs: CsBody = match serde_json::from_slice(&body) {
            Ok(c) => c,
            Err(e) => {
                tracing::debug!("embed checksum body parse failed: {e}");
                return Ok(false);
            }
        };
        let local_hex = if local_path.exists() {
            nasrudin_embed::compute_index_checksum(local_path)
                .ok()
                .map(|c| c.hex)
        } else {
            None
        };
        if local_hex.as_deref() == Some(cs.hex.as_str()) {
            return Ok(false);
        }
        tracing::info!("embed: local checksum mismatch, downloading new index");
        let (bin_status, bytes) = http.get_bytes("/api/embed/index.bin", &[]).await?;
        if !(200..300).contains(&bin_status) {
            anyhow::bail!("embed download http {bin_status}");
        }
        if let Some(parent) = local_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let tmp = with_tmp_suffix(local_path);
        std::fs::write(&tmp, &bytes)?;
        std::fs::rename(&tmp, local_path)?;
        tracing::info!("embed: wrote {} bytes to {:?}", bytes.len(), local_path);
        rebuild_sidecar(local_path)?;
        Ok(true)
    }

    fn with_tmp_suffix(p: &Path) -> std::path::PathBuf {
        let mut s = p.as_os_str().to_owned();
        s.push(".tmp");
        std::path::PathBuf::from(s)
    }

    fn rebuild_sidecar(main: &Path) -> Result<()> {
        use instant_distance::Builder as HnswBuilder;
        use nasrudin_core::TheoremId;
        use nasrudin_embed::format::{HEADER_SIZE, RECORD_SIZE};
        use nasrudin_embed::index::{CosinePoint, sidecar_path};
        use nasrudin_embed::{EMBED_DIM, IndexHeader};

        let bytes = std::fs::read(main)?;
        let header_bytes = &bytes[..HEADER_SIZE];
        let header = IndexHeader::decode(header_bytes)?;
        let body = &bytes[HEADER_SIZE..];
        let mut points: Vec<CosinePoint> = Vec::with_capacity(header.count as usize);
        let mut values: Vec<TheoremId> = Vec::with_capacity(header.count as usize);
        for i in 0..(header.count as usize) {
            let off = i * RECORD_SIZE;
            let mut id = [0u8; 8];
            id.copy_from_slice(&body[off..off + 8]);
            let mut v = vec![0f32; EMBED_DIM as usize];
            for j in 0..(EMBED_DIM as usize) {
                let s = off + 8 + j * 4;
                v[j] = f32::from_le_bytes([body[s], body[s + 1], body[s + 2], body[s + 3]]);
            }
            points.push(CosinePoint(v));
            values.push(id);
        }
        let hnsw = HnswBuilder::default().build(points, values);
        let bytes = postcard::to_allocvec(&hnsw)?;
        let sidecar = sidecar_path(main);
        std::fs::write(&sidecar, &bytes)?;
        Ok(())
    }
}

#[cfg(test)]
mod mutation_rl_state_tests {
    use super::*;

    #[test]
    fn worker_rl_state_round_trip_to_disk() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("worker_rl_state.json");
        let mut state = WorkerRlState::default();
        let mut scope = WorkerRlScopeState::default();
        scope.corpus_len = 123;
        scope.mutation_operator.pulls[5] = 7;
        scope.mutation_operator.total_reward[5] = 4.25;
        scope
            .qd_archive
            .cells
            .push(nasrudin_ga::chain_engine::QdArchiveCellStat {
                chain_len_bin: 2,
                axiom_count_bin: 1,
                target_progress_bin: 4,
                best_score: 3.5,
            });
        scope.replay_elites.push(ReplayElite {
            canonical: "x = y".into(),
            chain: vec![RuleStep::AlgebraicSimplify],
            added_at_unix_secs: 123,
            generation: 4,
            ..Default::default()
        });
        state
            .scopes
            .insert("domain=sr|target=sr_rest_energy".into(), scope);

        save_worker_rl_state(&path, &state).unwrap();
        let loaded = load_worker_rl_state(&path);
        let loaded_scope = loaded
            .scopes
            .get("domain=sr|target=sr_rest_energy")
            .unwrap();

        assert_eq!(loaded.version, 4);
        assert_eq!(loaded_scope.corpus_len, 123);
        assert_eq!(loaded_scope.mutation_operator.pulls[5], 7);
        assert!((loaded_scope.mutation_operator.total_reward[5] - 4.25).abs() < 1e-12);
        assert_eq!(loaded_scope.qd_archive.cells.len(), 1);
        assert!((loaded_scope.qd_archive.cells[0].best_score - 3.5).abs() < 1e-12);
        assert_eq!(loaded_scope.replay_elites.len(), 1);
        assert_eq!(loaded_scope.replay_elites[0].canonical, "x = y");
    }

    #[test]
    fn worker_rl_episode_log_path_defaults_next_to_state() {
        let dir = tempfile::tempdir().unwrap();
        let state_path = dir.path().join("worker_rl_state.json");

        let episode_path = worker_rl_episode_log_path(&state_path);

        assert_eq!(episode_path, dir.path().join("worker_rl_episodes.jsonl"));
    }

    #[test]
    fn worker_rl_episode_log_appends_jsonl() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("episodes.jsonl");
        let episode = WorkerRlEpisode {
            version: 1,
            at_unix_secs: 200_000,
            scope_key: "domain=qm|target=qm_planck_einstein".into(),
            domain: "qm".into(),
            target: Some("qm_planck_einstein".into()),
            chunk_index: 0,
            chunks_total: 1,
            corpus_len: 100,
            target_selector_policy: Some("verifier_ucb".into()),
            ga_policy: "steady_verify".into(),
            strategy_genome_fingerprint: None,
            strategy_genome_weight: None,
            replay_canonicals: vec!["canon-a".into()],
            population_size: 8,
            generations: 1,
            mutation_rate: 0.7,
            crossover_rate: 0.6,
            tournament_size: 3,
            max_chain_len: 12,
            max_lake_verifications: 1,
            total_candidates: 8,
            unique_executable: 1,
            lake_attempts: 1,
            lake_passed: 1,
            dim_rejected: 0,
            pre_lake_rejected: 0,
            verified_count: 1,
            verified_canonicals: vec!["canon-a".into()],
            reward: 0.86,
        };

        append_worker_rl_episode(&path, &episode).unwrap();
        append_worker_rl_episode(&path, &episode).unwrap();

        let body = std::fs::read_to_string(&path).unwrap();
        let lines: Vec<&str> = body.lines().collect();
        assert_eq!(lines.len(), 2);
        let parsed: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
        assert_eq!(parsed["ga_policy"], "steady_verify");
        assert_eq!(parsed["verified_count"], 1);
    }

    #[test]
    fn worker_rl_episode_log_compaction_keeps_newest_rows() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("episodes.jsonl");
        for i in 0..5 {
            let episode = WorkerRlEpisode {
                version: 1,
                at_unix_secs: 200_000 + i,
                scope_key: "domain=qm|target=qm_planck_einstein".into(),
                domain: "qm".into(),
                target: Some("qm_planck_einstein".into()),
                chunk_index: i as usize,
                chunks_total: 5,
                corpus_len: 100,
                target_selector_policy: Some("verifier_ucb".into()),
                ga_policy: "steady_verify".into(),
                strategy_genome_fingerprint: None,
                strategy_genome_weight: None,
                replay_canonicals: vec![],
                population_size: 8,
                generations: 1,
                mutation_rate: 0.7,
                crossover_rate: 0.6,
                tournament_size: 3,
                max_chain_len: 12,
                max_lake_verifications: 1,
                total_candidates: 8,
                unique_executable: 1,
                lake_attempts: 1,
                lake_passed: 0,
                dim_rejected: 0,
                pre_lake_rejected: 0,
                verified_count: 0,
                verified_canonicals: vec![],
                reward: i as f64,
            };
            append_worker_rl_episode(&path, &episode).unwrap();
        }

        compact_worker_rl_episode_log(&path, 2).unwrap();

        let body = std::fs::read_to_string(&path).unwrap();
        let lines: Vec<&str> = body.lines().collect();
        assert_eq!(lines.len(), 2);
        let first: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
        let second: serde_json::Value = serde_json::from_str(lines[1]).unwrap();
        assert_eq!(first["chunk_index"], 3);
        assert_eq!(second["chunk_index"], 4);
    }

    #[test]
    fn legacy_mutation_operator_state_loads_as_worker_rl_state() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("mutation_operator_rl.json");
        let mut stats = nasrudin_ga::chain_engine::MutationOperatorStats::default();
        stats.pulls[1] = 2;
        std::fs::write(&path, serde_json::to_vec(&stats).unwrap()).unwrap();

        let loaded = load_worker_rl_state(&path);
        let legacy = loaded.scopes.get("legacy-global").unwrap();

        assert_eq!(legacy.mutation_operator.pulls[1], 2);
        assert!(legacy.qd_archive.cells.is_empty());
    }

    #[test]
    fn legacy_combined_state_loads_into_legacy_global_scope() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("worker_rl_state_v1.json");
        let raw = serde_json::json!({
            "version": 1,
            "mutation_operator": {
                "pulls": [0, 3, 0, 0, 0, 0],
                "total_reward": [0.0, 1.5, 0.0, 0.0, 0.0, 0.0]
            },
            "qd_archive": {
                "cells": [{
                    "chain_len_bin": 1,
                    "axiom_count_bin": 2,
                    "target_progress_bin": 3,
                    "best_score": 4.0
                }]
            }
        });
        std::fs::write(&path, serde_json::to_vec(&raw).unwrap()).unwrap();

        let loaded = load_worker_rl_state(&path);
        let legacy = loaded.scopes.get("legacy-global").unwrap();

        assert_eq!(legacy.mutation_operator.pulls[1], 3);
        assert_eq!(legacy.qd_archive.cells.len(), 1);
    }

    #[test]
    fn worker_rl_scope_key_separates_domains_and_targets() {
        assert_ne!(
            worker_rl_scope_key("sr", Some("sr_rest_energy")),
            worker_rl_scope_key("qm", Some("sr_rest_energy"))
        );
        assert_ne!(
            worker_rl_scope_key("sr", Some("sr_rest_energy")),
            worker_rl_scope_key("sr", None)
        );
    }

    #[test]
    fn worker_rl_scope_decay_halves_old_rewards_after_one_half_life() {
        let mut scope = WorkerRlScopeState {
            updated_at_unix_secs: 1_000,
            corpus_len: 0,
            mutation_operator: nasrudin_ga::chain_engine::MutationOperatorStats {
                pulls: [10, 0, 0, 0, 0, 0],
                total_reward: [6.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            },
            qd_archive: nasrudin_ga::chain_engine::QdArchiveStats {
                cells: vec![nasrudin_ga::chain_engine::QdArchiveCellStat {
                    chain_len_bin: 1,
                    axiom_count_bin: 1,
                    target_progress_bin: 1,
                    best_score: 8.0,
                }],
            },
            strategy_genomes: std::collections::BTreeMap::from([(
                "genome-a".to_string(),
                StrategyGenomeStats {
                    pulls: 10,
                    total_reward: 6.0,
                    ..Default::default()
                },
            )]),
            replay_elites: Vec::new(),
        };

        decay_worker_rl_scope_state(&mut scope, 1_000 + 3600, Some(1.0));

        assert_eq!(scope.mutation_operator.pulls[0], 5);
        assert!((scope.mutation_operator.total_reward[0] - 3.0).abs() < 1e-12);
        assert!((scope.qd_archive.cells[0].best_score - 4.0).abs() < 1e-12);
        let genome = scope.strategy_genomes.get("genome-a").unwrap();
        assert_eq!(genome.pulls, 5);
        assert!((genome.total_reward - 3.0).abs() < 1e-12);
    }

    #[test]
    fn worker_rl_scope_decay_can_be_disabled() {
        let mut scope = WorkerRlScopeState {
            updated_at_unix_secs: 1_000,
            corpus_len: 0,
            mutation_operator: nasrudin_ga::chain_engine::MutationOperatorStats {
                pulls: [10, 0, 0, 0, 0, 0],
                total_reward: [6.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            },
            qd_archive: nasrudin_ga::chain_engine::QdArchiveStats::default(),
            strategy_genomes: std::collections::BTreeMap::from([(
                "genome-a".to_string(),
                StrategyGenomeStats {
                    pulls: 10,
                    total_reward: 6.0,
                    ..Default::default()
                },
            )]),
            replay_elites: Vec::new(),
        };

        decay_worker_rl_scope_state(&mut scope, 1_000 + 3600, None);

        assert_eq!(scope.mutation_operator.pulls[0], 10);
        assert!((scope.mutation_operator.total_reward[0] - 6.0).abs() < 1e-12);
        assert_eq!(scope.strategy_genomes["genome-a"].pulls, 10);
    }

    #[test]
    fn worker_rl_scope_corpus_drift_discounts_old_state() {
        let mut scope = WorkerRlScopeState {
            updated_at_unix_secs: 1_000,
            corpus_len: 100,
            mutation_operator: nasrudin_ga::chain_engine::MutationOperatorStats {
                pulls: [10, 0, 0, 0, 0, 0],
                total_reward: [6.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            },
            qd_archive: nasrudin_ga::chain_engine::QdArchiveStats {
                cells: vec![nasrudin_ga::chain_engine::QdArchiveCellStat {
                    chain_len_bin: 1,
                    axiom_count_bin: 1,
                    target_progress_bin: 1,
                    best_score: 8.0,
                }],
            },
            strategy_genomes: std::collections::BTreeMap::from([(
                "genome-a".to_string(),
                StrategyGenomeStats {
                    pulls: 10,
                    total_reward: 6.0,
                    ..Default::default()
                },
            )]),
            replay_elites: Vec::new(),
        };

        decay_worker_rl_scope_for_corpus_drift(&mut scope, 200);

        assert!(scope.mutation_operator.pulls[0] < 10);
        assert!(scope.mutation_operator.total_reward[0] < 6.0);
        assert!(scope.qd_archive.cells[0].best_score < 8.0);
        if let Some(genome) = scope.strategy_genomes.get("genome-a") {
            assert!(genome.pulls < 10);
            assert!(genome.total_reward < 6.0);
        }
    }

    #[test]
    fn worker_rl_scope_same_corpus_does_not_decay() {
        let mut scope = WorkerRlScopeState {
            updated_at_unix_secs: 1_000,
            corpus_len: 100,
            mutation_operator: nasrudin_ga::chain_engine::MutationOperatorStats {
                pulls: [10, 0, 0, 0, 0, 0],
                total_reward: [6.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            },
            qd_archive: nasrudin_ga::chain_engine::QdArchiveStats::default(),
            strategy_genomes: std::collections::BTreeMap::from([(
                "genome-a".to_string(),
                StrategyGenomeStats {
                    pulls: 10,
                    total_reward: 6.0,
                    ..Default::default()
                },
            )]),
            replay_elites: Vec::new(),
        };

        decay_worker_rl_scope_for_corpus_drift(&mut scope, 100);

        assert_eq!(scope.mutation_operator.pulls[0], 10);
        assert!((scope.mutation_operator.total_reward[0] - 6.0).abs() < 1e-12);
        assert_eq!(scope.strategy_genomes["genome-a"].pulls, 10);
    }

    #[test]
    fn strategy_genome_weight_uses_mean_reward() {
        assert_eq!(strategy_genome_weight(None), 1.0);
        assert!(
            (strategy_genome_weight(Some(&StrategyGenomeStats {
                pulls: 4,
                total_reward: 3.0,
                ..Default::default()
            })) - 1.25)
                .abs()
                < 1e-12
        );
    }

    #[test]
    fn strategy_genome_select_weight_uses_local_es_state() {
        let stats = StrategyGenomeStats {
            pulls: 4,
            total_reward: 2.0,
            weight_mean: 1.2,
            weight_sigma: 0.2,
            ..Default::default()
        };

        assert!((strategy_genome_select_weight(Some(&stats), None) - 1.33).abs() < 1e-12);
    }

    #[test]
    fn strategy_genome_select_weight_blends_episode_eval_prior() {
        let stats = StrategyGenomeStats {
            pulls: 4,
            total_reward: 2.0,
            weight_mean: 1.2,
            weight_sigma: 0.2,
            ..Default::default()
        };
        let snapshot = nasrudin_ga::rl_episode_eval::EvaluationSnapshot {
            generated_at_unix_secs: TEST_NOW,
            episodes: 16,
            domains: Default::default(),
            targets: Default::default(),
            latest_unix_secs: TEST_NOW,
            half_life_hours: 168.0,
            min_pulls: 3,
            ga_policies: Vec::new(),
            target_selector_policies: Vec::new(),
            strategy_genomes: vec![nasrudin_ga::rl_episode_eval::RankedPolicy {
                key: "genome-a".into(),
                stats: nasrudin_ga::rl_episode_eval::PolicyStats {
                    pulls: 8,
                    weighted_pulls: 7.5,
                    reward_sum: 6.0,
                    weighted_reward_sum: 5.8,
                    lake_attempts: 8,
                    lake_passed: 5,
                    ..Default::default()
                },
                mean_reward: 0.75,
                weighted_mean_reward: 0.77,
                ucb_score: 1.0,
                conservative_score: 0.90,
                lake_pass_rate: 0.625,
                low_sample: false,
            }],
            domain_targets: Vec::new(),
        };

        let prior = strategy_genome_eval_prior("genome-a", Some(&snapshot)).unwrap();
        assert!((prior - 1.40).abs() < 1e-12);
        assert!((strategy_genome_select_weight(Some(&stats), Some(prior)) - 1.3475).abs() < 1e-12);
    }

    #[test]
    fn strategy_genome_update_moves_mean_toward_successful_perturbation() {
        let mut stats = StrategyGenomeStats {
            pulls: 4,
            total_reward: 2.0,
            weight_mean: 1.0,
            weight_sigma: 0.25,
            ..Default::default()
        };

        strategy_genome_update(&mut stats, 1.25, 0.9);

        assert_eq!(stats.pulls, 5);
        assert!(stats.weight_mean > 1.0);
        assert!(stats.weight_sigma < 0.25);
        assert_eq!(stats.last_weight, 1.25);
        assert_eq!(stats.last_reward, 0.9);
        assert_eq!(stats.best_reward, 0.9);
    }

    #[test]
    fn strategy_genome_reward_prefers_verified_and_lake_passes() {
        let report = nasrudin_ga::chain_engine::DiscoveryReport {
            total_candidates: 100,
            unique_executable: 10,
            lake_attempts: 4,
            lake_passed: 3,
            verified: vec![nasrudin_ga::chain_engine::VerifiedDiscovery {
                chain: Chain(vec![]),
                final_expr: nasrudin_core::Expr::Var("x".into()),
                canonical: "x".into(),
                lean_source: String::new(),
                module_path: String::new(),
                generation: 0,
            }],
            ..Default::default()
        };

        assert!((strategy_genome_reward(&report) - 0.86).abs() < 1e-12);
    }

    const TEST_CORPUS_LEN: usize = 100;
    const TEST_NOW: i64 = 200_000;

    fn test_verified_discovery(canonical: &str, generation: usize) -> VerifiedDiscovery {
        VerifiedDiscovery {
            chain: Chain(vec![RuleStep::AlgebraicSimplify]),
            final_expr: nasrudin_core::Expr::Var("x".into()),
            canonical: canonical.into(),
            lean_source: String::new(),
            module_path: String::new(),
            generation,
        }
    }

    #[test]
    fn replay_archive_adds_dedupes_and_keeps_recent_verified_chains() {
        let mut scope = WorkerRlScopeState::default();
        let report = nasrudin_ga::chain_engine::DiscoveryReport {
            verified: vec![
                test_verified_discovery("canon-a", 1),
                test_verified_discovery("canon-b", 2),
            ],
            ..Default::default()
        };

        let added = update_replay_elites_from_verified(&mut scope, &report, TEST_NOW);

        assert_eq!(added, 2);
        assert_eq!(scope.replay_elites.len(), 2);
        assert_eq!(scope.replay_elites[0].canonical, "canon-b");
        assert_eq!(scope.replay_elites[1].canonical, "canon-a");

        let replacement = nasrudin_ga::chain_engine::DiscoveryReport {
            verified: vec![test_verified_discovery("canon-a", 9)],
            ..Default::default()
        };
        update_replay_elites_from_verified(&mut scope, &replacement, TEST_NOW + 1);

        assert_eq!(scope.replay_elites.len(), 2);
        assert_eq!(scope.replay_elites[0].canonical, "canon-a");
        assert_eq!(scope.replay_elites[0].generation, 9);
    }

    #[test]
    fn replay_archive_truncates_to_limit() {
        let mut scope = WorkerRlScopeState::default();
        let report = nasrudin_ga::chain_engine::DiscoveryReport {
            verified: (0..(replay_elite_archive_limit() + 4))
                .map(|i| test_verified_discovery(&format!("canon-{i}"), i))
                .collect(),
            ..Default::default()
        };

        update_replay_elites_from_verified(&mut scope, &report, TEST_NOW);

        assert_eq!(scope.replay_elites.len(), replay_elite_archive_limit());
        assert_eq!(
            scope.replay_elites[0].canonical,
            format!("canon-{}", replay_elite_archive_limit() + 3)
        );
    }

    #[test]
    fn replay_elite_chains_returns_per_chunk_prefix() {
        let mut scope = WorkerRlScopeState::default();
        for i in 0..(replay_elites_per_chunk() + 2) {
            scope.replay_elites.push(ReplayElite {
                canonical: format!("canon-{i}"),
                chain: vec![RuleStep::AlgebraicSimplify],
                added_at_unix_secs: TEST_NOW + i as i64,
                generation: i,
                ..Default::default()
            });
        }

        let chains = replay_elite_chains(&scope);

        assert_eq!(chains.len(), replay_elites_per_chunk());
        assert_eq!(chains[0].0, vec![RuleStep::AlgebraicSimplify]);
    }

    #[test]
    fn replay_elite_selection_prefers_unpulled_then_rewarded_elites() {
        let mut scope = WorkerRlScopeState::default();
        scope.replay_elites.push(ReplayElite {
            canonical: "low".into(),
            chain: vec![RuleStep::AlgebraicSimplify],
            pulls: 10,
            total_reward: 1.0,
            reward_ema: 0.1,
            best_reward: 0.2,
            ..Default::default()
        });
        scope.replay_elites.push(ReplayElite {
            canonical: "fresh".into(),
            chain: vec![RuleStep::AlgebraicSimplify],
            pulls: 0,
            ..Default::default()
        });
        scope.replay_elites.push(ReplayElite {
            canonical: "high".into(),
            chain: vec![RuleStep::AlgebraicSimplify],
            pulls: 10,
            total_reward: 9.0,
            reward_ema: 0.9,
            best_reward: 1.0,
            ..Default::default()
        });

        let selected = replay_elite_selections(&scope);

        assert_eq!(selected[0].canonical, "fresh");
        assert_eq!(selected[1].canonical, "high");
    }

    #[test]
    fn selected_replay_elite_update_rewards_exact_verified_replay() {
        let mut scope = WorkerRlScopeState::default();
        scope.replay_elites.push(ReplayElite {
            canonical: "canon-a".into(),
            chain: vec![RuleStep::AlgebraicSimplify],
            ..Default::default()
        });
        let selection = ReplayEliteSelection {
            canonical: "canon-a".into(),
            chain: Chain(vec![RuleStep::AlgebraicSimplify]),
        };
        let report = nasrudin_ga::chain_engine::DiscoveryReport {
            verified: vec![test_verified_discovery("canon-a", 1)],
            ..Default::default()
        };

        update_selected_replay_elites(&mut scope, &[selection], &report, 0.75, TEST_NOW);

        let elite = &scope.replay_elites[0];
        assert_eq!(elite.pulls, 1);
        assert_eq!(elite.last_reward, 1.0);
        assert_eq!(elite.best_reward, 1.0);
        assert_eq!(elite.reward_ema, 1.0);
        assert_eq!(elite.last_replayed_unix_secs, TEST_NOW);
    }

    #[test]
    fn selected_replay_elite_update_rewards_descendant_verified_chain() {
        let prefix = Chain(vec![RuleStep::AlgebraicSimplify]);
        let descendant = Chain(vec![
            RuleStep::AlgebraicSimplify,
            RuleStep::TakePositiveRoot,
        ]);
        let mut scope = WorkerRlScopeState::default();
        scope.replay_elites.push(ReplayElite {
            canonical: "prefix".into(),
            chain: prefix.0.clone(),
            ..Default::default()
        });
        let selection = ReplayEliteSelection {
            canonical: "prefix".into(),
            chain: prefix,
        };
        let report = nasrudin_ga::chain_engine::DiscoveryReport {
            verified: vec![VerifiedDiscovery {
                chain: descendant,
                final_expr: nasrudin_core::Expr::Var("x".into()),
                canonical: "descendant".into(),
                lean_source: String::new(),
                module_path: String::new(),
                generation: 2,
            }],
            ..Default::default()
        };

        update_selected_replay_elites(&mut scope, &[selection], &report, 0.2, TEST_NOW);

        assert_eq!(scope.replay_elites[0].last_reward, 0.9);
    }

    #[test]
    fn target_selector_policy_covers_unpulled_policies_first() {
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_selector_policy_key("all", "verifier_ucb"),
            TargetSelectorPolicyStats {
                pulls: 1,
                total_reward: 0.4,
                reward_ema: 0.4,
                ..Default::default()
            },
        );

        assert_eq!(
            select_target_selector_policy("all", &stats, None),
            "recent_verifier"
        );
    }

    #[test]
    fn target_selector_policy_prefers_recent_reward_signal() {
        let mut stats = std::collections::BTreeMap::new();
        for policy in TARGET_SELECTOR_POLICIES {
            stats.insert(
                target_selector_policy_key("all", policy),
                TargetSelectorPolicyStats {
                    pulls: 10,
                    total_reward: 8.0,
                    reward_ema: 0.20,
                    best_reward: 0.8,
                    ..Default::default()
                },
            );
        }
        stats.insert(
            target_selector_policy_key("all", "novelty_seeker"),
            TargetSelectorPolicyStats {
                pulls: 10,
                total_reward: 5.0,
                reward_ema: 0.95,
                best_reward: 1.0,
                ..Default::default()
            },
        );

        assert_eq!(
            select_target_selector_policy("all", &stats, None),
            "novelty_seeker"
        );
    }

    #[test]
    fn target_selector_policy_uses_episode_eval_prior_after_exploration() {
        let mut stats = std::collections::BTreeMap::new();
        for policy in TARGET_SELECTOR_POLICIES {
            stats.insert(
                target_selector_policy_key("all", policy),
                TargetSelectorPolicyStats {
                    pulls: 10,
                    total_reward: 5.0,
                    reward_ema: 0.50,
                    best_reward: 0.60,
                    ..Default::default()
                },
            );
        }
        let snapshot = nasrudin_ga::rl_episode_eval::EvaluationSnapshot {
            generated_at_unix_secs: TEST_NOW,
            episodes: 24,
            domains: Default::default(),
            targets: Default::default(),
            latest_unix_secs: TEST_NOW,
            half_life_hours: 168.0,
            min_pulls: 3,
            ga_policies: Vec::new(),
            target_selector_policies: TARGET_SELECTOR_POLICIES
                .iter()
                .map(|policy| nasrudin_ga::rl_episode_eval::RankedPolicy {
                    key: (*policy).to_string(),
                    stats: nasrudin_ga::rl_episode_eval::PolicyStats {
                        pulls: 6,
                        weighted_pulls: 6.0,
                        reward_sum: 3.0,
                        weighted_reward_sum: 3.0,
                        ..Default::default()
                    },
                    mean_reward: 0.50,
                    weighted_mean_reward: if *policy == "stall_rescue" { 1.0 } else { 0.50 },
                    ucb_score: if *policy == "stall_rescue" { 1.2 } else { 0.70 },
                    conservative_score: if *policy == "stall_rescue" {
                        0.95
                    } else {
                        0.20
                    },
                    lake_pass_rate: if *policy == "stall_rescue" { 1.0 } else { 0.0 },
                    low_sample: false,
                })
                .collect(),
            strategy_genomes: Vec::new(),
            domain_targets: Vec::new(),
        };

        assert_eq!(
            select_target_selector_policy("all", &stats, Some(&snapshot)),
            "stall_rescue"
        );
    }

    #[test]
    fn target_selector_policy_update_tracks_reward_ema() {
        let mut stats = TargetSelectorPolicyStats {
            pulls: 1,
            total_reward: 0.2,
            reward_ema: 0.2,
            best_reward: 0.2,
            ..Default::default()
        };

        update_target_selector_policy(&mut stats, 0.8);

        assert_eq!(stats.pulls, 2);
        assert_eq!(stats.last_reward, 0.8);
        assert_eq!(stats.best_reward, 0.8);
        assert!(stats.reward_ema > 0.2);
    }

    #[test]
    fn auto_target_policy_can_prioritize_novelty_over_verifier_score() {
        let candidates = ["qm_free_particle_dispersion", "qm_de_broglie"];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("qm", "qm_free_particle_dispersion"),
            TargetPortfolioStats {
                pulls: 20,
                total_reward: 10.0,
                reward_ema: 0.70,
                lake_pass_ema: 0.90,
                novelty_ema: 0.10,
                best_reward: 0.8,
                ..Default::default()
            },
        );
        stats.insert(
            target_portfolio_key("qm", "qm_de_broglie"),
            TargetPortfolioStats {
                pulls: 20,
                total_reward: 9.0,
                reward_ema: 0.60,
                lake_pass_ema: 0.20,
                novelty_ema: 1.0,
                best_reward: 0.7,
                ..Default::default()
            },
        );

        assert_eq!(
            select_auto_target_with_policy(
                "qm",
                &candidates,
                &stats,
                TEST_CORPUS_LEN,
                TEST_NOW,
                "novelty_seeker",
                None,
            ),
            Some("qm_de_broglie")
        );
        assert_eq!(
            select_auto_target_with_policy(
                "qm",
                &candidates,
                &stats,
                TEST_CORPUS_LEN,
                TEST_NOW,
                "recent_verifier",
                None,
            ),
            Some("qm_free_particle_dispersion")
        );
    }

    #[test]
    fn auto_target_selector_uses_domain_target_eval_prior_within_allowed_pool() {
        let candidates = ["qm_free_particle_dispersion", "qm_de_broglie"];
        let mut stats = std::collections::BTreeMap::new();
        for target in candidates {
            stats.insert(
                target_portfolio_key("qm", target),
                TargetPortfolioStats {
                    pulls: 10,
                    total_reward: 5.0,
                    reward_ema: 0.50,
                    lake_pass_ema: 0.50,
                    novelty_ema: 0.20,
                    best_reward: 0.60,
                    ..Default::default()
                },
            );
        }
        let snapshot = nasrudin_ga::rl_episode_eval::EvaluationSnapshot {
            generated_at_unix_secs: TEST_NOW,
            episodes: 20,
            domains: Default::default(),
            targets: Default::default(),
            latest_unix_secs: TEST_NOW,
            half_life_hours: 168.0,
            min_pulls: 3,
            ga_policies: Vec::new(),
            target_selector_policies: Vec::new(),
            strategy_genomes: Vec::new(),
            domain_targets: vec![
                nasrudin_ga::rl_episode_eval::RankedPolicy {
                    key: "qm:qm_free_particle_dispersion".into(),
                    stats: nasrudin_ga::rl_episode_eval::PolicyStats {
                        pulls: 8,
                        weighted_pulls: 8.0,
                        reward_sum: 3.0,
                        weighted_reward_sum: 3.0,
                        ..Default::default()
                    },
                    mean_reward: 0.38,
                    weighted_mean_reward: 0.38,
                    ucb_score: 0.50,
                    conservative_score: 0.10,
                    lake_pass_rate: 0.10,
                    low_sample: false,
                },
                nasrudin_ga::rl_episode_eval::RankedPolicy {
                    key: "qm:qm_de_broglie".into(),
                    stats: nasrudin_ga::rl_episode_eval::PolicyStats {
                        pulls: 8,
                        weighted_pulls: 8.0,
                        reward_sum: 7.2,
                        weighted_reward_sum: 7.0,
                        lake_attempts: 8,
                        lake_passed: 6,
                        ..Default::default()
                    },
                    mean_reward: 0.90,
                    weighted_mean_reward: 0.88,
                    ucb_score: 1.0,
                    conservative_score: 0.95,
                    lake_pass_rate: 0.75,
                    low_sample: false,
                },
            ],
        };

        assert_eq!(
            select_auto_target_with_policy(
                "qm",
                &candidates,
                &stats,
                TEST_CORPUS_LEN,
                TEST_NOW,
                "verifier_ucb",
                Some(&snapshot),
            ),
            Some("qm_de_broglie")
        );
    }

    #[test]
    fn ga_workhorse_policy_covers_unpulled_policies_first() {
        let scope = "domain=qm|target=qm_planck_einstein";
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            ga_workhorse_policy_key(scope, "steady_verify"),
            GaWorkhorsePolicyStats {
                pulls: 1,
                total_reward: 0.5,
                reward_ema: 0.5,
                ..Default::default()
            },
        );

        assert_eq!(
            select_ga_workhorse_policy(scope, &stats, None),
            "wide_explore"
        );
    }

    #[test]
    fn ga_workhorse_policy_prefers_recent_reward_signal() {
        let scope = "domain=qm|target=qm_planck_einstein";
        let mut stats = std::collections::BTreeMap::new();
        for policy in GA_WORKHORSE_POLICIES {
            stats.insert(
                ga_workhorse_policy_key(scope, policy),
                GaWorkhorsePolicyStats {
                    pulls: 8,
                    total_reward: 6.0,
                    reward_ema: 0.20,
                    best_reward: 0.7,
                    ..Default::default()
                },
            );
        }
        stats.insert(
            ga_workhorse_policy_key(scope, "deep_recombine"),
            GaWorkhorsePolicyStats {
                pulls: 8,
                total_reward: 4.0,
                reward_ema: 0.95,
                best_reward: 1.0,
                ..Default::default()
            },
        );

        assert_eq!(
            select_ga_workhorse_policy(scope, &stats, None),
            "deep_recombine"
        );
    }

    #[test]
    fn ga_workhorse_policy_uses_episode_eval_prior_after_exploration() {
        let scope = "domain=qm|target=qm_planck_einstein";
        let mut stats = std::collections::BTreeMap::new();
        for policy in GA_WORKHORSE_POLICIES {
            stats.insert(
                ga_workhorse_policy_key(scope, policy),
                GaWorkhorsePolicyStats {
                    pulls: 8,
                    total_reward: 4.0,
                    reward_ema: 0.50,
                    best_reward: 0.60,
                    ..Default::default()
                },
            );
        }
        let snapshot = nasrudin_ga::rl_episode_eval::EvaluationSnapshot {
            generated_at_unix_secs: TEST_NOW,
            episodes: 20,
            domains: Default::default(),
            targets: Default::default(),
            latest_unix_secs: TEST_NOW,
            half_life_hours: 168.0,
            min_pulls: 3,
            ga_policies: GA_WORKHORSE_POLICIES
                .iter()
                .map(|policy| nasrudin_ga::rl_episode_eval::RankedPolicy {
                    key: (*policy).to_string(),
                    stats: nasrudin_ga::rl_episode_eval::PolicyStats {
                        pulls: 4,
                        weighted_pulls: 4.0,
                        reward_sum: 2.0,
                        weighted_reward_sum: 2.0,
                        ..Default::default()
                    },
                    mean_reward: 0.50,
                    weighted_mean_reward: if *policy == "lake_focus" { 1.0 } else { 0.50 },
                    ucb_score: if *policy == "lake_focus" { 1.2 } else { 0.70 },
                    conservative_score: if *policy == "lake_focus" { 0.95 } else { 0.20 },
                    lake_pass_rate: if *policy == "lake_focus" { 1.0 } else { 0.0 },
                    low_sample: false,
                })
                .collect(),
            target_selector_policies: Vec::new(),
            strategy_genomes: Vec::new(),
            domain_targets: Vec::new(),
        };

        assert_eq!(
            select_ga_workhorse_policy(scope, &stats, Some(&snapshot)),
            "lake_focus"
        );
    }

    #[test]
    fn rl_policy_evidence_for_cluster_report_is_compact() {
        let snapshot = nasrudin_ga::rl_episode_eval::EvaluationSnapshot {
            generated_at_unix_secs: TEST_NOW,
            episodes: 12,
            domains: Default::default(),
            targets: Default::default(),
            latest_unix_secs: TEST_NOW,
            half_life_hours: 168.0,
            min_pulls: 3,
            ga_policies: vec![nasrudin_ga::rl_episode_eval::RankedPolicy {
                key: "lake_focus".into(),
                stats: nasrudin_ga::rl_episode_eval::PolicyStats {
                    pulls: 6,
                    weighted_pulls: 5.5,
                    reward_sum: 4.2,
                    weighted_reward_sum: 4.0,
                    lake_attempts: 6,
                    lake_passed: 3,
                    ..Default::default()
                },
                mean_reward: 0.70,
                weighted_mean_reward: 0.73,
                ucb_score: 1.0,
                conservative_score: 0.62,
                lake_pass_rate: 0.50,
                low_sample: false,
            }],
            target_selector_policies: vec![nasrudin_ga::rl_episode_eval::RankedPolicy {
                key: "verifier_ucb".into(),
                stats: nasrudin_ga::rl_episode_eval::PolicyStats {
                    pulls: 7,
                    weighted_pulls: 6.8,
                    reward_sum: 5.0,
                    weighted_reward_sum: 4.7,
                    lake_attempts: 7,
                    lake_passed: 4,
                    ..Default::default()
                },
                mean_reward: 0.71,
                weighted_mean_reward: 0.69,
                ucb_score: 0.9,
                conservative_score: 0.55,
                lake_pass_rate: 0.57,
                low_sample: false,
            }],
            strategy_genomes: Vec::new(),
            domain_targets: Vec::new(),
        };

        let evidence = rl_policy_evidence_for_cluster_report(
            "lake_focus",
            Some("verifier_ucb"),
            Some(&snapshot),
        );

        assert_eq!(evidence["ga_policy"], "lake_focus");
        assert_eq!(evidence["target_selector_policy"], "verifier_ucb");
        assert_eq!(evidence["episodes"], 12);
        assert_eq!(evidence["ga_policy_pulls"], 6);
        assert_eq!(evidence["ga_policy_lake_pass_rate"], 0.5);
        assert!(evidence.get("replay_canonicals").is_none());
        assert!(evidence.get("verified_canonicals").is_none());
    }

    #[test]
    fn ga_workhorse_policy_update_tracks_reward_ema() {
        let mut stats = GaWorkhorsePolicyStats {
            pulls: 1,
            total_reward: 0.1,
            reward_ema: 0.1,
            best_reward: 0.1,
            ..Default::default()
        };

        update_ga_workhorse_policy(&mut stats, 0.9);

        assert_eq!(stats.pulls, 2);
        assert_eq!(stats.last_reward, 0.9);
        assert_eq!(stats.best_reward, 0.9);
        assert!(stats.reward_ema > 0.1);
    }

    #[test]
    fn ga_workhorse_policy_applies_bounded_config_changes() {
        let mut cfg = DiscoveryConfig {
            population_size: 16,
            mutation_rate: 0.12,
            crossover_rate: 0.60,
            tournament_size: 3,
            max_chain_len: 10,
            max_lake_verifications: 2,
            ..Default::default()
        };

        apply_ga_workhorse_policy(&mut cfg, "deep_recombine", 16, 10, 2);

        assert_eq!(cfg.population_size, 16);
        assert_eq!(cfg.max_chain_len, 14);
        assert_eq!(cfg.tournament_size, 4);
        assert!(cfg.crossover_rate > 0.60);
        assert!(cfg.mutation_rate < 0.12);
    }

    #[test]
    fn auto_target_selector_stays_on_unproved_featured_before_frontier() {
        let candidates = ["qm_planck_einstein", "qm_free_particle_dispersion"];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("qm", "qm_planck_einstein"),
            TargetPortfolioStats {
                pulls: 3,
                total_reward: 2.0,
                ..Default::default()
            },
        );

        assert_eq!(
            select_auto_target("qm", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW),
            Some("qm_planck_einstein")
        );
    }

    #[test]
    fn auto_target_selector_covers_unpulled_featured_targets_first() {
        let candidates = [
            "qm_planck_einstein",
            "qm_schrodinger",
            "qm_free_particle_dispersion",
        ];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("qm", "qm_planck_einstein"),
            TargetPortfolioStats {
                pulls: 3,
                total_reward: 2.0,
                ..Default::default()
            },
        );

        assert_eq!(
            select_auto_target("qm", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW),
            Some("qm_schrodinger")
        );
    }

    #[test]
    fn auto_target_selector_prefers_recent_verifier_signal_over_stale_mean() {
        let candidates = ["qm_planck_einstein", "qm_free_particle_dispersion"];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("qm", "qm_planck_einstein"),
            TargetPortfolioStats {
                proved: true,
                pulls: 20,
                total_reward: 16.0,
                best_reward: 1.0,
                reward_ema: 0.05,
                lake_pass_ema: 0.0,
                novelty_ema: 0.05,
                failure_streak: 6,
                ..Default::default()
            },
        );
        stats.insert(
            target_portfolio_key("qm", "qm_free_particle_dispersion"),
            TargetPortfolioStats {
                pulls: 20,
                total_reward: 8.0,
                best_reward: 0.8,
                reward_ema: 0.85,
                lake_pass_ema: 1.0,
                novelty_ema: 0.30,
                failure_streak: 0,
                ..Default::default()
            },
        );

        assert_eq!(
            select_auto_target("qm", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW),
            Some("qm_free_particle_dispersion")
        );
    }

    #[test]
    fn auto_target_selector_returns_none_after_all_candidates_proved() {
        let candidates = ["sr_rest_energy"];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("sr", "sr_rest_energy"),
            TargetPortfolioStats {
                proved: true,
                pulls: 1,
                total_reward: 1.0,
                ..Default::default()
            },
        );

        assert_eq!(
            select_auto_target("sr", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW),
            None
        );
    }

    #[test]
    fn auto_target_selector_moves_to_frontier_after_featured_targets_proved() {
        let candidates = [
            "qm_planck_einstein",
            "qm_schrodinger",
            "qm_free_particle_dispersion",
        ];
        let mut stats = std::collections::BTreeMap::new();
        for target in ["qm_planck_einstein", "qm_schrodinger"] {
            stats.insert(
                target_portfolio_key("qm", target),
                TargetPortfolioStats {
                    proved: true,
                    pulls: 1,
                    total_reward: 1.0,
                    ..Default::default()
                },
            );
        }

        assert_eq!(
            select_auto_target("qm", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW),
            Some("qm_free_particle_dispersion")
        );
    }

    #[test]
    fn auto_target_selector_skips_stalled_featured_targets() {
        let candidates = ["em_gauss_law", "qm_free_particle_dispersion"];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("all", "em_gauss_law"),
            TargetPortfolioStats {
                pulls: target_stall_threshold(),
                failure_streak: target_stall_threshold(),
                last_attempt_unix_secs: TEST_NOW,
                corpus_len_at_last_attempt: TEST_CORPUS_LEN,
                ..Default::default()
            },
        );

        assert_eq!(
            select_auto_target("all", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW),
            Some("qm_free_particle_dispersion")
        );
    }

    #[test]
    fn auto_target_selector_retries_stalled_target_after_cooldown() {
        let candidates = ["em_gauss_law", "qm_free_particle_dispersion"];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("all", "em_gauss_law"),
            TargetPortfolioStats {
                pulls: target_stall_threshold(),
                failure_streak: target_stall_threshold(),
                last_attempt_unix_secs: TEST_NOW - target_stall_retry_after_secs() - 1,
                corpus_len_at_last_attempt: TEST_CORPUS_LEN,
                ..Default::default()
            },
        );

        assert_eq!(
            select_auto_target("all", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW),
            Some("em_gauss_law")
        );
    }

    #[test]
    fn auto_target_selector_retries_stalled_target_after_corpus_change() {
        let candidates = ["em_gauss_law", "qm_free_particle_dispersion"];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("all", "em_gauss_law"),
            TargetPortfolioStats {
                pulls: target_stall_threshold(),
                failure_streak: target_stall_threshold(),
                last_attempt_unix_secs: TEST_NOW,
                corpus_len_at_last_attempt: TEST_CORPUS_LEN - 1,
                ..Default::default()
            },
        );

        assert_eq!(
            select_auto_target("all", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW),
            Some("em_gauss_law")
        );
    }

    #[test]
    fn auto_target_curriculum_status_reports_featured_and_frontier_tiers() {
        let candidates = [
            "qm_planck_einstein",
            "qm_schrodinger",
            "qm_free_particle_dispersion",
        ];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("qm", "qm_planck_einstein"),
            TargetPortfolioStats {
                proved: true,
                pulls: 1,
                total_reward: 1.0,
                ..Default::default()
            },
        );

        let status =
            auto_target_curriculum_status("qm", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW);

        assert_eq!(status.featured_total, 2);
        assert_eq!(status.featured_proved, 1);
        assert_eq!(status.featured_pending, vec!["qm_schrodinger"]);
        assert!(status.featured_stalled.is_empty());
        assert_eq!(status.frontier_pending, vec!["qm_free_particle_dispersion"]);
    }

    #[test]
    fn auto_target_curriculum_status_reports_stalled_featured_targets() {
        let candidates = ["em_gauss_law", "qm_free_particle_dispersion"];
        let mut stats = std::collections::BTreeMap::new();
        stats.insert(
            target_portfolio_key("all", "em_gauss_law"),
            TargetPortfolioStats {
                pulls: target_stall_threshold(),
                failure_streak: target_stall_threshold(),
                last_attempt_unix_secs: TEST_NOW,
                corpus_len_at_last_attempt: TEST_CORPUS_LEN,
                ..Default::default()
            },
        );

        let status =
            auto_target_curriculum_status("all", &candidates, &stats, TEST_CORPUS_LEN, TEST_NOW);

        assert_eq!(status.featured_total, 1);
        assert_eq!(status.featured_proved, 0);
        assert!(status.featured_pending.is_empty());
        assert_eq!(status.featured_stalled, vec!["em_gauss_law"]);
        assert_eq!(status.frontier_pending, vec!["qm_free_particle_dispersion"]);
    }

    #[test]
    fn target_portfolio_update_rewards_verified_chunks() {
        let mut stats = TargetPortfolioStats::default();
        let report = nasrudin_ga::chain_engine::DiscoveryReport {
            total_candidates: 100,
            unique_executable: 10,
            lake_attempts: 1,
            lake_passed: 1,
            verified: vec![nasrudin_ga::chain_engine::VerifiedDiscovery {
                chain: Chain(vec![]),
                final_expr: nasrudin_core::Expr::Var("x".into()),
                canonical: "x".into(),
                lean_source: String::new(),
                module_path: String::new(),
                generation: 0,
            }],
            ..Default::default()
        };

        update_target_portfolio(
            &mut stats,
            "qm_planck_einstein",
            &report,
            TEST_CORPUS_LEN,
            TEST_NOW,
        );

        assert_eq!(stats.pulls, 1);
        assert_eq!(stats.last_attempt_unix_secs, TEST_NOW);
        assert_eq!(stats.corpus_len_at_last_attempt, TEST_CORPUS_LEN);
        assert!(stats.last_reward > 0.9);
        assert_eq!(stats.best_reward, stats.last_reward);
        assert!(stats.reward_ema > 0.9);
        assert_eq!(stats.lake_pass_ema, 1.0);
        assert_eq!(stats.failure_streak, 0);
        assert!(!stats.proved);
    }

    #[test]
    fn target_portfolio_marks_matching_featured_target_proved() {
        let mut stats = TargetPortfolioStats::default();
        let final_expr = nasrudin_ga::target::TargetSpec::lookup("qm_planck_einstein")
            .unwrap()
            .final_target;
        let report = nasrudin_ga::chain_engine::DiscoveryReport {
            total_candidates: 8,
            unique_executable: 1,
            lake_attempts: 1,
            lake_passed: 1,
            verified: vec![nasrudin_ga::chain_engine::VerifiedDiscovery {
                chain: Chain(vec![]),
                canonical: final_expr.to_canonical(),
                final_expr,
                lean_source: String::new(),
                module_path: String::new(),
                generation: 0,
            }],
            ..Default::default()
        };

        update_target_portfolio(
            &mut stats,
            "qm_planck_einstein",
            &report,
            TEST_CORPUS_LEN,
            TEST_NOW,
        );

        assert!(stats.proved);
    }

    #[test]
    fn target_portfolio_marks_planck_einstein_alias_expr_proved() {
        use nasrudin_core::{BinOp, Expr};

        let final_expr = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("Eph".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Var("hbar".into())),
                Box::new(Expr::Var("omega".into())),
            )),
        );
        let report = nasrudin_ga::chain_engine::DiscoveryReport {
            total_candidates: 8,
            unique_executable: 1,
            lake_attempts: 1,
            lake_passed: 1,
            verified: vec![nasrudin_ga::chain_engine::VerifiedDiscovery {
                chain: Chain(vec![]),
                canonical: final_expr.to_canonical(),
                final_expr,
                lean_source: String::new(),
                module_path: String::new(),
                generation: 0,
            }],
            ..Default::default()
        };
        let mut stats = TargetPortfolioStats::default();

        update_target_portfolio(
            &mut stats,
            "qm_planck_einstein",
            &report,
            TEST_CORPUS_LEN,
            TEST_NOW,
        );

        assert!(stats.proved);
    }

    #[test]
    fn featured_postulate_backed_targets_have_seed_elites() {
        for target in [
            "sr_rest_energy",
            "qm_planck_einstein",
            "qm_schrodinger",
            "thermo_boltzmann_entropy",
            "newton_second",
            "gr_einstein_field_equation",
        ] {
            assert!(
                m1_seed_elite_for(Some(target)).is_some(),
                "featured target {target} should have a seed elite"
            );
        }
        assert!(
            m1_seed_elite_for(Some("em_gauss_law")).is_none(),
            "Gauss law has no current upstream div_E/rho/epsilon_0 postulate seed"
        );
    }

    #[test]
    fn target_portfolio_update_tracks_stalls() {
        let mut stats = TargetPortfolioStats {
            pulls: 1,
            total_reward: 1.0,
            reward_ema: 1.0,
            lake_pass_ema: 1.0,
            novelty_ema: 1.0,
            ..Default::default()
        };
        let report = nasrudin_ga::chain_engine::DiscoveryReport {
            total_candidates: 100,
            unique_executable: 5,
            lake_attempts: 1,
            lake_passed: 0,
            verified: vec![],
            ..Default::default()
        };

        update_target_portfolio(
            &mut stats,
            "qm_planck_einstein",
            &report,
            TEST_CORPUS_LEN,
            TEST_NOW,
        );

        assert_eq!(stats.failure_streak, 1);
        assert!(stats.reward_ema < 1.0);
        assert!(stats.lake_pass_ema < 1.0);
        assert!(stats.novelty_ema < 1.0);
    }

    #[test]
    fn corrupt_worker_rl_state_falls_back_to_default() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("worker_rl_state.json");
        std::fs::write(&path, b"not-json").unwrap();

        let loaded = load_worker_rl_state(&path);

        assert!(loaded.scopes.is_empty());
    }
}
