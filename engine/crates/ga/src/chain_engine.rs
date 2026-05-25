//! Chain-based discovery engine.
//!
//! Phase 6 of the project plan. Runs a simple tournament-selection GA over
//! `ChainIndividual`s using the operators in `chain_ga` (`mutate_chain`,
//! `splice_chains`, `evaluate_chain_fitness`). Promising chains are
//! optionally Lean-verified via `verify_chain`.
//!
//! ## Verification budget
//!
//! Lake build per candidate is ~5 minutes (cold Mathlib import) → ~30s
//! warm if module imports are stable. So unrestricted lake-verify is
//! infeasible. The driver applies lake only to the top-fitness Pareto
//! front *and* only to chains whose final expression is novel (we
//! deduplicate via canonical form). Even then expect ~minutes per
//! verified candidate.

use crate::chain_ga::{
    ChainIndividual, ChainVerifyOutcome, splice_chains,
    verify_chain_cached_full,
};
use crate::target::TargetSpec;
use nasrudin_core::Expr;
use nasrudin_derive::{AxiomStore, Chain, RuleStep};
use rand::{Rng, RngExt};
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Cheap pre-lake-build filter knobs. Read from env once at first use,
/// then reused across every `pick_top_for_verify` call. The point is
/// to drop chains that have ~zero chance of lake-verifying *before*
/// we spend ~30–60 s of compute on a `lake build` for them.
///
/// All filters are sub-millisecond. Filters 1, 2, 4 require a target;
/// without one they are no-ops.
#[derive(Debug, Clone, Copy)]
struct PreLakeFilters {
    enabled: bool,
    /// Filter 1: `target::symbol_overlap(candidate, target.final_target) >= min`.
    /// Default 0.5 — a chain whose final symbols overlap the target by
    /// less than half cannot be on the right ladder.
    symbol_overlap_min: f64,
    /// Filter 2: `target::ladder_score(candidate, spec) >= min`.
    /// Default 0.3 — sub-0.3 hasn't reached even rung 1 meaningfully.
    ladder_min: f64,
    /// Filter 3: `chain.0.len() >= min`. Default 3 — sub-3-step chains
    /// are typically mutation artifacts (one IntroduceAxiom +
    /// RearrangeEquation), no real composition happened.
    chain_min_steps: usize,
    /// Filter 4: every Var/Const symbol in `target.final_target` must
    /// appear somewhere in the candidate's final expression. Reject
    /// rate ~5–15 %, cost ~1 µs.
    require_target_symbols: bool,
}

impl PreLakeFilters {
    fn from_env_once() -> &'static Self {
        static CACHED: OnceLock<PreLakeFilters> = OnceLock::new();
        CACHED.get_or_init(|| {
            let enabled = std::env::var("NASRUDIN_PRE_LAKE_FILTERS")
                .map(|v| !matches!(
                    v.trim().to_lowercase().as_str(),
                    "0" | "false" | "no" | "off"
                ))
                .unwrap_or(true);
            let symbol_overlap_min = std::env::var("NASRUDIN_PRE_LAKE_SYMBOL_OVERLAP_MIN")
                .ok()
                .and_then(|v| v.parse::<f64>().ok())
                .unwrap_or(0.5);
            let ladder_min = std::env::var("NASRUDIN_PRE_LAKE_LADDER_MIN")
                .ok()
                .and_then(|v| v.parse::<f64>().ok())
                .unwrap_or(0.3);
            let chain_min_steps = std::env::var("NASRUDIN_PRE_LAKE_CHAIN_MIN_STEPS")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
                .unwrap_or(3);
            let require_target_symbols = std::env::var("NASRUDIN_PRE_LAKE_REQUIRE_SYMBOLS")
                .map(|v| !matches!(
                    v.trim().to_lowercase().as_str(),
                    "0" | "false" | "no" | "off"
                ))
                .unwrap_or(true);
            tracing::info!(
                enabled, symbol_overlap_min, ladder_min, chain_min_steps,
                require_target_symbols, "pre-lake filter knobs"
            );
            PreLakeFilters {
                enabled,
                symbol_overlap_min,
                ladder_min,
                chain_min_steps,
                require_target_symbols,
            }
        })
    }

    /// Apply filters. Returns `Some(reason)` on reject, `None` on pass.
    fn check(
        &self,
        chain: &Chain,
        final_expr: &Expr,
        target: Option<&TargetSpec>,
    ) -> Option<&'static str> {
        if !self.enabled {
            return None;
        }
        // Filter 3 — applies even without a target (sub-3-step chains
        // are degenerate mutation artifacts in any domain).
        if chain.0.len() < self.chain_min_steps {
            return Some("chain_too_short");
        }
        let Some(spec) = target else {
            return None;
        };
        // Filter 1 — symbol-overlap floor.
        if crate::target::symbol_overlap(final_expr, &spec.final_target)
            < self.symbol_overlap_min
        {
            return Some("symbol_overlap_below_floor");
        }
        // Filter 2 — ladder-score floor.
        if crate::target::ladder_score(final_expr, spec) < self.ladder_min {
            return Some("ladder_below_floor");
        }
        // Filter 4 — required-subexpression presence (set semantics:
        // every target symbol — Var, Const, Lit — must appear in the
        // candidate). `collect_symbols` produces typed strings like
        // "var:E", "const:C", "lit:1/2"; intersection is exact.
        if self.require_target_symbols {
            let target_syms = crate::target::collect_symbols(&spec.final_target);
            if !target_syms.is_empty() {
                let cand_syms = crate::target::collect_symbols(final_expr);
                if !target_syms.iter().all(|s| cand_syms.contains(s)) {
                    return Some("missing_target_symbol");
                }
            }
        }
        None
    }
}

/// Configuration for `run_discovery`.
#[derive(Debug, Clone)]
pub struct DiscoveryConfig {
    pub population_size: usize,
    pub generations: usize,
    pub crossover_rate: f64,
    pub mutation_rate: f64,
    pub tournament_size: usize,
    pub max_chain_len: usize,
    /// If `Some`, attempt `verify_chain` on top-fitness novel candidates
    /// at this prover root. If `None`, skip lake-verify entirely (fast
    /// dry run for development).
    pub prover_root: Option<PathBuf>,
    /// Hard cap on lake-verifications per discovery run. Lake build is
    /// slow; you almost always want this small (e.g. 3-5).
    pub max_lake_verifications: usize,
    /// Symbolic target the search should bias toward. When `Some`, every
    /// chain's `target_shape` and `ladder_progress` fitness components
    /// get computed against this spec; the composite weight on those
    /// components in `composite()` is high (10x), so the search climbs
    /// toward the target instead of optimising for novelty alone.
    pub target: Option<crate::target::TargetSpec>,
    /// Negative-result memo: 8-byte canonical hashes (xxhash64 of
    /// `Expr::to_canonical()`, matches `nasrudin_core::canonical_hash`)
    /// for theorems the cluster has already lake-rejected. The GA
    /// skips lake-verification for any chain whose final canonical
    /// hashes into this set — wasted compute is the dominant cost
    /// and previous workers have already paid it. Empty = no skips
    /// (legacy / single-worker behaviour).
    pub rejected_canonicals: std::sync::Arc<HashSet<Vec<u8>>>,
    /// When `Some`, the GA's lake-verify path goes through the cache
    /// layer (skip on hit, record on success). The bundle is `Clone`
    /// (Arc-backed) so `DiscoveryConfig` keeps its existing `Clone`
    /// derive without lifetime gymnastics.
    pub cache_ctx: Option<crate::cache_bundle::CacheBundle>,
    /// Bloom filter pre-check over `rejected_canonicals`. When set,
    /// `pick_top_for_verify` queries this before the full HashSet
    /// lookup — a Bloom miss means definitely-novel (skip the
    /// HashSet probe), a Bloom hit falls through to the real check.
    /// Sized for ~100k entries with FPR 0.001. Built once at worker
    /// startup from the same source as `rejected_canonicals`.
    pub novelty_bloom: Option<std::sync::Arc<bloomfilter::Bloom<[u8]>>>,
    /// Phase E: per-operator weights for mutation selection. Keys are
    /// the names in [`crate::chain_ga::MUTATION_OPS`]; missing keys
    /// inherit the uniform fallback. `None` is the legacy
    /// uniform-1/6 distribution. Threaded in via the LLM-supplied
    /// LlmSuggestion seed.
    pub mutation_priors: Option<std::collections::HashMap<String, f32>>,
    /// P-Task 11: when > 0, the GA harvests this many top-fitness
    /// novel candidates per generation and pushes them into
    /// `report.verified` *without running lake build*. The worker
    /// submits them to /api/ingest where the server's reverify drain
    /// chain-replays in microseconds (P-Task 1) and the lake-promotion
    /// drain (P-Task 2) handles kernel confirmation lazily.
    ///
    /// This unblocks the "thousands of cheap school-volunteer workers"
    /// model: each worker runs only the GA + canonical hashing +
    /// Lean source emission (all sub-millisecond) instead of paying
    /// 5–60s/lake-build locally. A 4-core school laptop can submit
    /// hundreds of candidates per minute instead of a handful per hour.
    ///
    /// Set to 0 (default) for the legacy "verify locally before
    /// submitting" mode.
    pub submit_unverified_top_k: usize,
    /// Layer 2: hard-reject candidates whose final equation has known,
    /// definitively-mismatched dimensions on either side. Conservative —
    /// only rejects when both LHS and RHS infer to known dimensions and
    /// they differ; unknown vars / non-equations / pure-math fall through.
    /// Default true (set false via `NASRUDIN_DIMENSION_HARD_REJECT=0` for
    /// natural-units / non-SI research).
    pub dimension_hard_reject: bool,
    /// Variable→dimension table used by the hard-reject gate. Domain-aware:
    /// the worker builds this from the active domain at boot. Empty map
    /// is fine for pure-math runs where no variable has a known dimension.
    pub dimension_var_dims: std::sync::Arc<
        std::collections::HashMap<String, nasrudin_core::Dimension>,
    >,
    /// Layer 1: persistent Lean elaborator. When `Some`, the verify path
    /// routes through the long-lived `lean --run nasrudin_server.lean`
    /// subprocess (~100–500ms per candidate against pre-loaded Mathlib)
    /// and only falls back to `lake build` (~30–120s) on RPC error.
    /// When `None`, we use the legacy lake-build path exclusively.
    ///
    /// Spawn this once at worker boot via
    /// `nasrudin_lean_bridge::PersistentElaborator::new`.
    pub elaborator: Option<std::sync::Arc<nasrudin_lean_bridge::PersistentElaborator>>,
    /// LLM-emitted "bias toward end-of-chain mutations". Bounded
    /// [0.0, 1.0] by the steerer validator. Multiplies the
    /// `append_productive_suffix` mutation operator's selection
    /// weight by `(1.0 + 4.0 * suffix_bias)` so suffix_bias=1.0
    /// makes that op 5× more likely than uniform. 0.0 = no
    /// bias (uniform).
    pub suffix_bias: f32,
    /// Fraction of best-fitness individuals copied through to the
    /// next generation unchanged. Bounded [0.0, 0.2]. Default 0.0
    /// (no elitism). With elitism_fraction=0.05 and population=128,
    /// the top 6 elites carry through verbatim each generation.
    pub elitism_fraction: f32,
    /// When true, `run_discovery` snapshots the chunk's final
    /// population into `DiscoveryReport.final_population`. Off by
    /// default — only the worker that runs cluster reporting needs it.
    pub collect_final_population: bool,
    /// Per-cluster knob overrides. Empty → all individuals use the
    /// global rate / elitism unchanged. Populated by the worker after
    /// matching LLM `cluster_directives` to the chunk's clusters.
    pub cluster_multipliers: std::collections::HashMap<u32, ClusterMultiplier>,
    /// Per-individual cluster_id, aligned with the offspring index.
    /// Empty → cluster-aware path is skipped and the GA runs in legacy
    /// uniform mode.
    pub cluster_assignments: Vec<u32>,
    /// LLM-curated physics-shape atom pool for this discovery run.
    /// Workers extract `steering.atom_pool[domain]` from the cluster
    /// steerer's response and set this; the GA's
    /// `append_productive_suffix` mutation operator reads it on every
    /// invocation so domain-specific compounds (e.g. EM `Eph`, `pph`;
    /// QM `hbar_omega`) feed target synthesis. `None` falls back to
    /// the hardcoded 8-atom SR baseline (uniform).
    pub atom_pool: Option<Vec<(String, f32)>>,
    /// Permanent elite chain — when `Some`, this chain is injected as
    /// individual #0 of every seed population and re-injected as
    /// offspring[0] of every generation, regardless of fitness. The
    /// rest of the population still gets random seeds + tournament
    /// selection + mutation/crossover (which may produce variants of
    /// this chain that are evaluated normally), but the canonical copy
    /// is locked in for the entire run.
    ///
    /// Milestone 1 mechanism test: set this to
    /// `Chain::rest_energy_from_upstream()` so the GA's verifier
    /// pipeline gets at least one chain per generation that lands
    /// exactly on the sr_rest_energy target. Once a verified row hits
    /// /api/theorems we clear this and let the steerer + mutations
    /// rediscover the chain from random seeds (M1.d).
    pub permanent_elite: Option<Chain>,
}

/// Per-cluster knob multiplier. Default is identity (1.0× rate, 1.0×
/// elitism, no kill, no diversify). The worker fills these in when a
/// matched LLM `cluster_directive` lands; the GA mutation site
/// applies the multiplier to the per-individual rate / elitism check.
#[derive(Debug, Clone)]
pub struct ClusterMultiplier {
    pub mutation_rate_mult: f32,
    pub elitism_mult: f32,
    pub kill_fraction: f32,
    pub diversify_fraction: f32,
}

impl Default for ClusterMultiplier {
    fn default() -> Self {
        Self {
            mutation_rate_mult: 1.0,
            elitism_mult: 1.0,
            kill_fraction: 0.0,
            diversify_fraction: 0.0,
        }
    }
}

/// Resolve the per-individual mutation rate by cluster_id. Falls back
/// to global when no per-cluster multiplier is set for the id. Clamps
/// to the existing GA bounds [0.05, 0.30] so a directive can't
/// accidentally turn the GA into pure random search or freeze it.
pub fn local_mutation_rate_for_cluster(cfg: &DiscoveryConfig, cluster_id: u32) -> f64 {
    if cfg.cluster_multipliers.is_empty() {
        return cfg.mutation_rate;
    }
    let mult = cfg
        .cluster_multipliers
        .get(&cluster_id)
        .map(|m| m.mutation_rate_mult as f64)
        .unwrap_or(1.0);
    (cfg.mutation_rate * mult).clamp(0.05, 0.30)
}

/// Backwards-compatible idx-based variant. Reads cluster_assignments
/// at `individual_idx` to find the cluster_id, then forwards to
/// `local_mutation_rate_for_cluster`. Empty `cluster_assignments`
/// falls through to the global rate (legacy behaviour).
pub fn local_mutation_rate(cfg: &DiscoveryConfig, individual_idx: usize) -> f64 {
    if cfg.cluster_assignments.is_empty() {
        return cfg.mutation_rate;
    }
    let cid = match cfg.cluster_assignments.get(individual_idx) {
        Some(c) => *c,
        None => return cfg.mutation_rate,
    };
    local_mutation_rate_for_cluster(cfg, cid)
}

/// Compute the elitism count for a specific cluster. Used when the
/// GA performs its global elitism step but wants to honour a cluster
/// directive that exploits one cluster harder than another.
pub fn elite_count_with_cluster_multiplier(
    cfg: &DiscoveryConfig,
    cluster_id: u32,
) -> usize {
    let mult = cfg
        .cluster_multipliers
        .get(&cluster_id)
        .map(|m| m.elitism_mult as f64)
        .unwrap_or(1.0);
    let base = (cfg.elitism_fraction.clamp(0.0, 0.2) as f64
        * cfg.population_size as f64)
        .floor();
    (base * mult)
        .round()
        .max(0.0)
        .min(cfg.population_size as f64) as usize
}

impl Default for DiscoveryConfig {
    fn default() -> Self {
        Self {
            population_size: 32,
            generations: 100,
            crossover_rate: 0.6,
            mutation_rate: 0.5,
            tournament_size: 3,
            max_chain_len: 12,
            prover_root: None,
            max_lake_verifications: 0,
            target: None,
            rejected_canonicals: std::sync::Arc::new(HashSet::new()),
            cache_ctx: None,
            novelty_bloom: None,
            mutation_priors: None,
            submit_unverified_top_k: 0,
            dimension_hard_reject: true,
            dimension_var_dims: std::sync::Arc::new(std::collections::HashMap::new()),
            elaborator: None,
            suffix_bias: 0.0,
            elitism_fraction: 0.0,
            collect_final_population: false,
            cluster_multipliers: std::collections::HashMap::new(),
            cluster_assignments: vec![],
            atom_pool: None,
            permanent_elite: None,
        }
    }
}

/// One Lean-verified discovery from the GA run.
#[derive(Debug, Clone)]
pub struct VerifiedDiscovery {
    pub chain: Chain,
    pub final_expr: Expr,
    pub canonical: String,
    pub lean_source: String,
    pub module_path: String,
    pub generation: usize,
}

/// Aggregated outcome of a single discovery run.
#[derive(Debug, Default)]
pub struct DiscoveryReport {
    pub generations_run: usize,
    pub total_candidates: usize,
    pub unique_executable: usize,
    /// Total lake / persistent-elaborator verification attempts. Counts
    /// each candidate that reached the kernel (either via persistent RPC
    /// or via `lake build`); does not include candidates dropped by
    /// pre-filters.
    pub lake_attempts: usize,
    /// Of `lake_attempts`, how many were accepted by the kernel.
    /// `lake_passed / lake_attempts` is the pass-rate metric the user
    /// cares about — Layer-1+2 push this toward 99.9%.
    pub lake_passed: usize,
    /// Of `lake_attempts`, how many took the fast persistent-elaborator
    /// path (vs. fell back to `lake build`). High `persistent_attempts /
    /// lake_attempts` means the warm Lean process is doing the work.
    pub persistent_attempts: usize,
    /// Layer-2 dimension hard-reject count: candidates dropped before
    /// reaching the kernel because their final equation has known,
    /// definitively-mismatched dimensions on each side.
    pub dim_rejected: usize,
    /// Pre-lake-build cheap filter rejection count. These are
    /// candidates that survived the dimension hard-reject and the
    /// novelty + bloom checks, but were dropped *before* `lake build`
    /// (or the persistent elaborator) by `PreLakeFilters` — symbol
    /// overlap, ladder score, chain length, required target symbols.
    /// Cost ~µs per rejection, saves ~30–60 s of lake compute on the
    /// shared 1 vCPU droplet.
    pub pre_lake_rejected: usize,
    pub verified: Vec<VerifiedDiscovery>,
    pub top_fitness_canonical: Option<String>,
    /// Snapshot of the chunk's final population for clustering /
    /// reporting. Populated when `config.collect_final_population` is
    /// true; empty otherwise so the legacy hot path doesn't pay for
    /// the clone. Each entry is (chain, fitness components vector,
    /// axiom/theorem names referenced by the chain).
    /// Snapshot of the chunk's final population for clustering /
    /// reporting / per-cluster reward attribution. Each tuple is
    /// `(chain, fitness_components, axiom_names, cluster_id)`. The
    /// last element traces back to the SEED cluster_id (parent →
    /// child inheritance through crossover) so callers can group
    /// final-population fitness by the cluster a directive landed
    /// on at chunk start.
    pub final_population: Vec<(Chain, [f32; 4], Vec<String>, u32)>,
}

/// Run the chain-based GA for `config.generations` generations.
///
/// Population is seeded by `random_chain_seed` — a 1-step
/// `[IntroduceAxiom(name)]` per individual using a randomly-chosen
/// axiom from `store`. Each generation: tournament-select two parents,
/// `splice_chains` (with prob `crossover_rate`), then `mutate_chain`
/// (with prob `mutation_rate`) on each child, and replace the
/// population with the offspring (truncated to `population_size`).
///
/// Returns a `DiscoveryReport` summarising the run + any lake-verified
/// theorems found.
/// Seed an initial GA population from random 1-step IntroduceAxiom
/// chains. Exposed as a separate function so callers (the worker)
/// can cluster the seed population externally and inject per-cluster
/// `cluster_id`s before evolution begins.
///
/// `report.total_candidates` is incremented by `population_size` to
/// match the bookkeeping of the legacy `run_discovery` path.
pub fn seed_population(
    store: &AxiomStore,
    config: &DiscoveryConfig,
    rng: &mut impl Rng,
    report: &mut DiscoveryReport,
) -> Vec<ChainIndividual> {
    let mut pop: Vec<ChainIndividual> = (0..config.population_size)
        .map(|_| {
            let chain = random_chain_seed(store, rng, report);
            let fit = crate::chain_ga::evaluate_chain_fitness_with_target(
                &chain,
                store,
                config.target.as_ref(),
            );
            ChainIndividual::new(chain, fit)
        })
        .collect();
    // Milestone 1: permanent elite is injected at index 0 so it's
    // guaranteed to be considered for clustering, tournament selection,
    // and Lake verification. The offspring loop in
    // `run_discovery_from_population` re-injects it every generation
    // regardless of fitness, so this seed-time placement is just to
    // give the cluster summariser something to cluster around.
    if let Some(elite_chain) = &config.permanent_elite {
        if !pop.is_empty() {
            let fit = crate::chain_ga::evaluate_chain_fitness_with_target(
                elite_chain,
                store,
                config.target.as_ref(),
            );
            pop[0] = ChainIndividual::new(elite_chain.clone(), fit);
        }
    }
    pop
}

pub fn run_discovery(
    store: &AxiomStore,
    config: &DiscoveryConfig,
    rng: &mut impl Rng,
) -> DiscoveryReport {
    let mut report = DiscoveryReport::default();

    // ── Seed initial population: each individual is a 1-step chain
    //    `[IntroduceAxiom(random_axiom)]`. The GA will compose more
    //    interesting chains via mutation/crossover.
    let population = seed_population(store, config, rng, &mut report);
    run_discovery_from_population(store, config, population, rng, report)
}

/// Variant of `run_discovery` that takes a pre-seeded initial
/// population. Used by the worker to externally cluster the seeds
/// and tag each individual's `cluster_id` before evolution starts;
/// the per-cluster mutation rate then fires inside the offspring
/// loop via `local_mutation_rate_for_cluster`.
pub fn run_discovery_from_population(
    store: &AxiomStore,
    config: &DiscoveryConfig,
    initial_population: Vec<ChainIndividual>,
    rng: &mut impl Rng,
    initial_report: DiscoveryReport,
) -> DiscoveryReport {
    let mut report = initial_report;
    let mut population = initial_population;

    // Dedup set keyed on canonical form of (final_expr) for verified
    // discoveries so we don't lake-build the same theorem twice.
    let mut verified_canonicals: HashSet<String> = HashSet::new();

    // ── Evolution loop
    // Number of best-fitness elites copied through unchanged each
    // generation, derived from `config.elitism_fraction` (clamped to
    // [0, 0.2] to match the steerer validator). 0.0 = no elitism =
    // legacy pure-replacement behaviour; 0.05 × pop=128 = 6 elites.
    let elite_count = ((config.elitism_fraction.clamp(0.0, 0.2) as f64
        * config.population_size as f64)
        .floor() as usize)
        .min(config.population_size.saturating_sub(1));

    // M1 production-droplet path: once a chain has been Verified AND the
    // lake budget is exhausted, exit the gen loop immediately so the
    // worker can submit to /api/ingest without burning ~30s of wasted
    // mutation/crossover/fitness work on a chunk that's already done.
    // Gated by `NASRUDIN_EARLY_EXIT_ON_VERIFIED` (default ON, set to "0"
    // to disable for research runs where statistics across all gens
    // matter). Read once here so the env lookup doesn't add per-gen cost.
    let early_exit_on_verified = std::env::var("NASRUDIN_EARLY_EXIT_ON_VERIFIED")
        .map(|v| v != "0")
        .unwrap_or(true);

    for gen_idx in 0..config.generations {
        report.generations_run = gen_idx + 1;

        // Generate offspring.
        let mut offspring: Vec<ChainIndividual> = Vec::with_capacity(config.population_size);

        // Milestone 1: permanent elite — locked in as offspring[0] every
        // generation, regardless of fitness ordering. Always evaluated
        // against the current target so its fitness components are
        // fresh. The fitness-based elitism below still gets to run for
        // the remaining slots.
        if let Some(elite_chain) = &config.permanent_elite {
            let fit = crate::chain_ga::evaluate_chain_fitness_with_target(
                elite_chain,
                store,
                config.target.as_ref(),
            );
            offspring.push(ChainIndividual::new(elite_chain.clone(), fit));
            report.total_candidates += 1;
        }

        // Elitism: copy top-N current population through unchanged
        // before generating the rest as offspring. The population
        // is pre-sorted by composite fitness at the end of the
        // previous generation (or by initial fitness on gen 0, since
        // the seed loop preserves insertion order).
        if elite_count > 0 {
            for ind in population.iter().take(elite_count) {
                if offspring.len() >= config.population_size {
                    break;
                }
                offspring.push(ind.clone());
                report.total_candidates += 1;
            }
        }

        while offspring.len() < config.population_size {
            let p1 = tournament_select(&population, config.tournament_size, rng);
            let p2 = tournament_select(&population, config.tournament_size, rng);
            // Inherit cluster_id from each parent. Children are
            // tagged with their parent's cluster so per-cluster
            // mutation rates apply consistently to the cluster's
            // descendants too. After several generations of
            // crossover the cluster becomes a soft attribute (the
            // chain itself drifts) but the lineage tag stays
            // useful as long as the cluster_multipliers are
            // populated for that id.
            let p1_cluster = p1.cluster_id;
            let p2_cluster = p2.cluster_id;
            let (mut c1, mut c2) = if rng.random_bool(config.crossover_rate) {
                splice_chains(&p1.chain, &p2.chain, rng)
            } else {
                (p1.chain.clone(), p2.chain.clone())
            };
            // Per-individual mutation rate honours per-cluster
            // multipliers when the worker has populated
            // `cluster_multipliers`; falls back to the global rate
            // otherwise. Clamped to [0.05, 0.30] inside the helper.
            let c1_rate = local_mutation_rate_for_cluster(config, p1_cluster);
            let c2_rate = local_mutation_rate_for_cluster(config, p2_cluster);
            let atom_pool_ref = config.atom_pool.as_deref();
            if rng.random_bool(c1_rate) {
                crate::chain_ga::mutate_chain_full(
                    &mut c1,
                    store,
                    rng,
                    config.mutation_priors.as_ref(),
                    config.suffix_bias,
                    atom_pool_ref,
                );
            }
            if rng.random_bool(c2_rate) {
                crate::chain_ga::mutate_chain_full(
                    &mut c2,
                    store,
                    rng,
                    config.mutation_priors.as_ref(),
                    config.suffix_bias,
                    atom_pool_ref,
                );
            }
            for (child, child_cluster) in [(c1, p1_cluster), (c2, p2_cluster)] {
                if child.is_empty() || child.len() > config.max_chain_len {
                    continue;
                }
                let fit = crate::chain_ga::evaluate_chain_fitness_with_target(
                    &child,
                    store,
                    config.target.as_ref(),
                );
                offspring.push(ChainIndividual::with_cluster(child, fit, child_cluster));
                report.total_candidates += 1;
                if offspring.len() >= config.population_size {
                    break;
                }
            }
        }

        // Phase 6.5.6: fitness sharing. Compute the *shared count* for
        // each candidate (how many others have the same final-expr
        // canonical). Divide composite fitness by `(1 + count)` so
        // duplicates get penalised. Without this, the GA converges on
        // ~7-8 simple multi-axiom chains whose final-expr is the last
        // loaded axiom (iter 11 finding).
        let canonicals: Vec<Option<String>> = offspring
            .iter()
            .map(|ind| run_chain_for_final(&ind.chain, store).map(|e| e.to_canonical()))
            .collect();
        let mut counts: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();
        for c in canonicals.iter().flatten() {
            *counts.entry(c.clone()).or_insert(0) += 1;
        }
        let shared_score: Vec<f64> = canonicals
            .iter()
            .map(|c| match c {
                Some(s) => 1.0 / counts.get(s).copied().unwrap_or(1) as f64,
                None => 0.0,
            })
            .collect();
        // Composite × shared-score for ranking.
        let mut ranked: Vec<(usize, f64)> = offspring
            .iter()
            .enumerate()
            .map(|(i, ind)| (i, composite(&ind.fitness) * shared_score[i]))
            .collect();
        ranked.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        let kept_indices: std::collections::BTreeSet<usize> = ranked
            .into_iter()
            .take(config.population_size)
            .map(|(i, _)| i)
            .collect();
        let mut new_offspring = Vec::with_capacity(config.population_size);
        for (i, ind) in offspring.into_iter().enumerate() {
            if kept_indices.contains(&i) {
                new_offspring.push(ind);
            }
        }
        let mut offspring = new_offspring;
        // Final sort by composite for tournament selection in next gen.
        offspring.sort_by(|a, b| {
            composite(&b.fitness)
                .partial_cmp(&composite(&a.fitness))
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // P-Task 11: harvest top-K novel candidates for server-side
        // chain-replay verification. We emit Lean source locally
        // (microseconds via emit_lean_file, no lake build) and push
        // each into report.verified. The worker's existing submit
        // path POSTs them to /api/ingest where the server's reverify
        // drain takes over.
        if config.submit_unverified_top_k > 0 {
            let mut harvested = 0usize;
            for ind in &offspring {
                if harvested >= config.submit_unverified_top_k {
                    break;
                }
                if ind.fitness.novelty < 1.0 || ind.fitness.nasrudin_relevance < 1.0 {
                    continue;
                }
                let final_expr = match run_chain_for_final(&ind.chain, store) {
                    Some(e) => e,
                    None => continue,
                };
                if config.dimension_hard_reject
                    && nasrudin_derive::equation_definitely_inconsistent(
                        &final_expr,
                        &config.dimension_var_dims,
                    )
                {
                    report.dim_rejected += 1;
                    continue;
                }
                let canonical = final_expr.to_canonical();
                if !verified_canonicals.insert(canonical.clone()) {
                    continue;
                }
                let canon_hash = nasrudin_core::canonical_hash(&canonical);
                if config.rejected_canonicals.contains(&canon_hash) {
                    continue;
                }
                // Emit Lean source — no lake build, just the text.
                let mut ctx = nasrudin_derive::DerivationContext::new();
                use nasrudin_derive::DerivationStrategy;
                if ind.chain.execute(store, &mut ctx).is_err() {
                    continue;
                }
                let theorem_name = format!("submit_gen{gen_idx}_{harvested}");
                let module_path =
                    format!("PhysicsGenerator.Derived.SubmitGen{gen_idx}_{harvested}");
                let cfg = nasrudin_derive::lean_emitter::LeanEmitConfig {
                    namespace: "PhysicsGenerator.Derived".into(),
                    theorem_name: theorem_name.clone(),
                    use_mathlib: true,
                };
                let lean_source = nasrudin_derive::lean_emitter::emit_lean_file(&ctx, &cfg);
                report.verified.push(VerifiedDiscovery {
                    chain: ind.chain.clone(),
                    final_expr,
                    canonical,
                    lean_source,
                    module_path,
                    generation: gen_idx,
                });
                harvested += 1;
            }
        }

        // Try lake-verify on the top novel candidate(s) of this gen.
        if let Some(ref prover_root) = config.prover_root {
            if report.lake_attempts < config.max_lake_verifications {
                if let Some(top) = pick_top_for_verify(
                    &offspring,
                    &verified_canonicals,
                    &config.rejected_canonicals,
                    config.novelty_bloom.as_deref(),
                    store,
                    config.dimension_hard_reject,
                    &config.dimension_var_dims,
                    config.target.as_ref(),
                    &mut report.pre_lake_rejected,
                ) {
                    report.lake_attempts += 1;
                    let basename = format!("DiscoverGen{gen_idx}");
                    let theorem_name = format!("discover_gen{gen_idx}");
                    if config.elaborator.is_some() {
                        report.persistent_attempts += 1;
                    }
                    match verify_chain_cached_full(
                        &top.chain,
                        store,
                        prover_root.as_path(),
                        &basename,
                        &theorem_name,
                        config.cache_ctx.as_ref(),
                        config.elaborator.as_ref(),
                    ) {
                        ChainVerifyOutcome::Verified {
                            lean_source,
                            module_path,
                        } => {
                            report.lake_passed += 1;
                            // Compute the final Expr again for the report.
                            let final_expr = run_chain_for_final(&top.chain, store)
                                .unwrap_or(Expr::Lit(0, 1));
                            let canonical = final_expr.to_canonical();
                            verified_canonicals.insert(canonical.clone());
                            report.verified.push(VerifiedDiscovery {
                                chain: top.chain.clone(),
                                final_expr,
                                canonical,
                                lean_source,
                                module_path,
                                generation: gen_idx,
                            });
                        }
                        ChainVerifyOutcome::LeanRejected { lean_source, stderr } => {
                            // M1 diagnostic: log the actual elaborator
                            // stderr + the first 2KB of source so we can
                            // see WHY Lake rejected and reproduce
                            // outside the worker.
                            let stderr_snip: String =
                                stderr.chars().take(1000).collect();
                            // Slice on a char boundary, not byte
                            // boundary — the emitter occasionally puts
                            // unicode (²·) in comment blocks and a
                            // mid-codepoint slice would panic.
                            let src_snip: String =
                                lean_source.chars().take(2048).collect();
                            tracing::warn!(
                                gen = gen_idx,
                                theorem = %theorem_name,
                                stderr = %stderr_snip,
                                "Lake/elaborator REJECTED chain"
                            );
                            // Only dump the source on the FIRST reject
                            // of each chunk to avoid swamping the
                            // journal. `report.lake_passed == 0` here
                            // because the success branch is the other
                            // arm of the match.
                            if report.lake_attempts == 1 {
                                eprintln!(
                                    "  ✗ Lake reject gen={gen_idx} thm={theorem_name} stderr:\n{stderr_snip}\n  --- emitted Lean (first 2KB) ---\n{src_snip}\n  --- end emit ---"
                                );
                            } else {
                                eprintln!(
                                    "  ✗ Lake reject gen={gen_idx} thm={theorem_name}: {stderr_snip}"
                                );
                            }
                        }
                        ChainVerifyOutcome::PreFilterFailed { reason } => {
                            tracing::debug!(
                                gen = gen_idx,
                                "pre-filter rejection: {reason}"
                            );
                        }
                        ChainVerifyOutcome::ToolchainError { message } => {
                            tracing::warn!(
                                gen = gen_idx,
                                "lean toolchain error: {message}"
                            );
                            eprintln!(
                                "  ✗ Lean toolchain error gen={gen_idx}: {message}"
                            );
                        }
                    }
                }
            }
        }

        // M1 early-exit: see `early_exit_on_verified` declaration above.
        // Conditions match the production-droplet contract: at least one
        // chain Verified this chunk AND the lake budget has been fully
        // spent. We still update `population = offspring;` first so the
        // final-population snapshot (if `collect_final_population` is
        // set) reflects the gen that produced the discovery.
        population = offspring;
        if early_exit_on_verified
            && !report.verified.is_empty()
            && report.lake_attempts >= config.max_lake_verifications
        {
            break;
        }
    }

    // Track unique executable count.
    let mut canon_set: HashSet<String> = HashSet::new();
    for ind in &population {
        if ind.fitness.novelty > 0.5 {
            if let Some(expr) = run_chain_for_final(&ind.chain, store) {
                canon_set.insert(expr.to_canonical());
            }
        }
    }
    report.unique_executable = canon_set.len();

    if let Some(top) = population.first() {
        if let Some(expr) = run_chain_for_final(&top.chain, store) {
            report.top_fitness_canonical = Some(expr.to_canonical());
        }
    }

    if config.collect_final_population {
        // Snapshot the final population for clustering / reporting.
        // Populated only when the worker has opted in (workers that
        // POST /api/cluster-report). Cost: one Chain clone per
        // individual + an axiom-name walk per chain.
        report.final_population.reserve(population.len());
        for ind in &population {
            let names: Vec<String> = ind
                .chain
                .0
                .iter()
                .filter_map(|s| match s {
                    RuleStep::IntroduceAxiom { axiom_name } => Some(axiom_name.clone()),
                    RuleStep::IntroduceTheorem { theorem_name } => Some(theorem_name.clone()),
                    _ => None,
                })
                .collect();
            // Map FitnessScore → 4-component vector aligned with the
            // steerer's `fitness_weights` (novelty, dimensional
            // elegance, length penalty, target proximity). All clamped
            // to [0,1] so the cluster-feature L2 distance is bounded.
            let f = &ind.fitness;
            let length_signal = (1.0 - (ind.chain.0.len() as f64 / 16.0).min(1.0))
                .clamp(0.0, 1.0);
            let comps = [
                f.novelty.clamp(0.0, 1.0) as f32,
                f.dimensional.clamp(0.0, 1.0) as f32,
                length_signal as f32,
                f.target_shape.max(f.ladder_progress).clamp(0.0, 1.0) as f32,
            ];
            report
                .final_population
                .push((ind.chain.clone(), comps, names, ind.cluster_id));
        }
    }

    report
}

fn random_chain_seed(
    store: &AxiomStore,
    rng: &mut impl Rng,
    _report: &mut DiscoveryReport,
) -> Chain {
    // **Iter 19 — seed-bank diversification.** ~20 % of seeds load
    // ALL upstream axioms (in shuffled order); the rest seed with
    // 3-5 random axioms as before. This is *not* domain hard-coding:
    // the seed-bank simply says "start with all the available
    // material loaded" — it doesn't tell the GA *what* to derive.
    // Without it, the GA rarely accumulates all 4 useful axioms
    // (four_momentum, mink, mass, rest_frame) in one chain.
    //
    // Cold-tier note: this routine intentionally pulls only from
    // the hot tier (hand-coded postulates + PhysLean catalog —
    // ~2-5 k entries). Pre-loading all 195 k Mathlib lemmas into a
    // single chain would explode chain length and search depth,
    // defeating the diversification goal. The 3-5-axiom random fill
    // path below still pulls from hot+cold via the bandwidth-
    // bounded two-stage pick.
    let hot_names_vec = store.iter_hot_names();
    let cold_names = store.cold_names();
    let names: Vec<String> = hot_names_vec.clone();
    if names.is_empty() && cold_names.is_empty() {
        return Chain::new();
    }
    if rng.random_bool(0.2) && !names.is_empty() {
        let mut shuffled = names.clone();
        // Fisher-Yates shuffle.
        for i in (1..shuffled.len()).rev() {
            let j = rng.random_range(0..=i);
            shuffled.swap(i, j);
        }
        let mut chain = Chain::new();
        for name in shuffled {
            chain.push(RuleStep::IntroduceAxiom { axiom_name: name });
        }
        return chain;
    }

    let n_axioms = rng.random_range(3..=5);
    let mut chain = Chain::new();
    let total = hot_names_vec.len() + cold_names.len();
    for _ in 0..n_axioms {
        if total == 0 {
            break;
        }
        let idx = rng.random_range(0..total);
        let name = if idx < hot_names_vec.len() {
            hot_names_vec[idx].clone()
        } else {
            cold_names[idx - hot_names_vec.len()].clone()
        };
        chain.push(RuleStep::IntroduceAxiom { axiom_name: name });
    }
    chain
}

fn tournament_select<'a>(
    pop: &'a [ChainIndividual],
    k: usize,
    rng: &mut impl Rng,
) -> &'a ChainIndividual {
    let mut best: Option<&ChainIndividual> = None;
    for _ in 0..k.max(1) {
        let idx = rng.random_range(0..pop.len());
        let cand = &pop[idx];
        if best
            .map(|b| composite(&cand.fitness) > composite(&b.fitness))
            .unwrap_or(true)
        {
            best = Some(cand);
        }
    }
    best.unwrap_or(&pop[0])
}

fn composite(f: &nasrudin_core::FitnessScore) -> f64 {
    // Phase 6.5.2: stronger weights on `depth` (rewards long chains)
    // and `connectivity` (rewards using multiple distinct axioms).
    // `complexity` is *low* for long chains, so we *down-weight* it
    // and rely on `depth` to push composition. Without these tweaks
    // the GA converges on length-1 single-axiom chains.
    //
    // Target-direction terms (`target_shape`, `ladder_progress`) get
    // heavy weight when set — this is the "don't settle for tautologies
    // in the right symbol set" pressure. They're zero when no target is
    // configured, so behaviour is unchanged for legacy runs.
    1.5 * f.novelty
        + 1.0 * f.nasrudin_relevance
        + 3.0 * f.depth          // ↑ from 1.0
        + 3.0 * f.connectivity   // ↑ from 1.0
        + 0.2 * f.complexity     // ↓ from 0.5 (don't reward terseness)
        + 0.5 * f.dimensional
        + 0.5 * f.symmetry
        + 6.0 * f.target_shape   // direction
        + 4.0 * f.ladder_progress
}

fn run_chain_for_final(chain: &Chain, store: &AxiomStore) -> Option<Expr> {
    let mut ctx = nasrudin_derive::DerivationContext::new();
    use nasrudin_derive::DerivationStrategy;
    chain.execute(store, &mut ctx).ok()
}

#[allow(clippy::too_many_arguments)]
fn pick_top_for_verify<'a>(
    offspring: &'a [ChainIndividual],
    seen: &HashSet<String>,
    rejected: &HashSet<Vec<u8>>,
    bloom: Option<&bloomfilter::Bloom<[u8]>>,
    store: &AxiomStore,
    dim_hard_reject: bool,
    dim_var_dims: &std::collections::HashMap<String, nasrudin_core::Dimension>,
    target: Option<&TargetSpec>,
    pre_lake_rejected: &mut usize,
) -> Option<&'a ChainIndividual> {
    let pre_lake = PreLakeFilters::from_env_once();
    for ind in offspring {
        if ind.fitness.novelty < 1.0 || ind.fitness.nasrudin_relevance < 1.0 {
            continue;
        }
        if let Some(expr) = run_chain_for_final(&ind.chain, store) {
            if dim_hard_reject
                && nasrudin_derive::equation_definitely_inconsistent(&expr, dim_var_dims)
            {
                continue;
            }
            // Cheap pre-lake-build gates. Order matches PreLakeFilters
            // priority: chain length first (sub-µs), then target-aware
            // checks (µs each). All four together dominated by the
            // canonicalize step that the lake-build path also pays.
            if let Some(reason) = pre_lake.check(&ind.chain, &expr, target) {
                *pre_lake_rejected += 1;
                tracing::debug!(
                    filter = "pre_lake",
                    reason,
                    chain_len = ind.chain.0.len(),
                    "candidate rejected before lake build"
                );
                continue;
            }
            let canon = expr.to_canonical();
            // Skip canonicals we've verified this run, AND canonicals
            // any peer worker has already rejected via lake build.
            // Bloom pre-check: when present, a bloom miss means
            // definitely-novel and we skip the HashSet probe entirely.
            // A bloom hit (which includes both true-positives and the
            // ~0.1% false-positive rate) falls through to the real
            // HashSet membership check.
            let canon_hash = nasrudin_core::canonical_hash(&canon);
            let in_rejected = match bloom {
                Some(b) if !b.check(canon_hash.as_slice()) => false,
                _ => rejected.contains(&canon_hash),
            };
            if !seen.contains(&canon) && !in_rejected {
                return Some(ind);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn upstream_store() -> AxiomStore {
        let mut s = AxiomStore::new();
        s.load_special_relativity_upstream();
        s
    }

    #[test]
    fn discovery_dry_run_populates_report() {
        let store = upstream_store();
        let config = DiscoveryConfig {
            population_size: 8,
            generations: 5,
            crossover_rate: 0.6,
            mutation_rate: 0.7,
            tournament_size: 3,
            max_chain_len: 8,
            prover_root: None, // no lake verify in unit tests
            max_lake_verifications: 0,
            target: None,
            rejected_canonicals: std::sync::Arc::new(HashSet::new()),
            cache_ctx: None,
            novelty_bloom: None,
            mutation_priors: None,
            submit_unverified_top_k: 0,
            dimension_hard_reject: false,
            dimension_var_dims: std::sync::Arc::new(std::collections::HashMap::new()),
            elaborator: None,
            suffix_bias: 0.0,
            elitism_fraction: 0.0,
            collect_final_population: false,
            cluster_multipliers: std::collections::HashMap::new(),
            cluster_assignments: vec![],
            atom_pool: None,
            permanent_elite: None,
        };
        let mut rng = rand::rng();
        let report = run_discovery(&store, &config, &mut rng);
        assert_eq!(report.generations_run, 5);
        assert!(report.total_candidates >= 8);
        // We ran no lake verifications.
        assert_eq!(report.lake_attempts, 0);
        assert!(report.verified.is_empty());
    }

    #[test]
    fn discovery_finds_at_least_some_executable_chains() {
        let store = upstream_store();
        let config = DiscoveryConfig {
            population_size: 16,
            generations: 20,
            crossover_rate: 0.5,
            mutation_rate: 0.7,
            tournament_size: 3,
            max_chain_len: 10,
            prover_root: None,
            max_lake_verifications: 0,
            target: None,
            rejected_canonicals: std::sync::Arc::new(HashSet::new()),
            cache_ctx: None,
            novelty_bloom: None,
            mutation_priors: None,
            submit_unverified_top_k: 0,
            dimension_hard_reject: false,
            dimension_var_dims: std::sync::Arc::new(std::collections::HashMap::new()),
            elaborator: None,
            suffix_bias: 0.0,
            elitism_fraction: 0.0,
            collect_final_population: false,
            cluster_multipliers: std::collections::HashMap::new(),
            cluster_assignments: vec![],
            atom_pool: None,
            permanent_elite: None,
        };
        let mut rng = rand::rng();
        let report = run_discovery(&store, &config, &mut rng);
        // After 20 generations from random IntroduceAxiom seeds, at
        // least *some* chains should still execute (since seeds
        // themselves do). If this fails, mutation has broken the
        // search space.
        assert!(
            report.unique_executable > 0,
            "no executable chains in final pop after 20 gens"
        );
    }

    #[test]
    fn permanent_elite_survives_every_generation() {
        // M1 mechanism test: when permanent_elite is set, the chain
        // appears in seed_population at index 0 AND is re-injected as
        // offspring[0] every generation, regardless of fitness. Without
        // this guarantee, the cluster-steerer's churn or aggressive
        // mutation can wipe the chain out and leave the GA blind.
        let store = upstream_store();
        let elite = nasrudin_derive::Chain::rest_energy_from_upstream();
        let mut config = DiscoveryConfig {
            population_size: 16,
            generations: 5,
            crossover_rate: 0.6,
            mutation_rate: 0.7,
            tournament_size: 3,
            max_chain_len: 12,
            prover_root: None,
            max_lake_verifications: 0,
            target: None,
            rejected_canonicals: std::sync::Arc::new(HashSet::new()),
            cache_ctx: None,
            novelty_bloom: None,
            mutation_priors: None,
            submit_unverified_top_k: 0,
            dimension_hard_reject: false,
            dimension_var_dims: std::sync::Arc::new(
                std::collections::HashMap::new(),
            ),
            elaborator: None,
            suffix_bias: 0.0,
            elitism_fraction: 0.0,
            collect_final_population: true,
            cluster_multipliers: std::collections::HashMap::new(),
            cluster_assignments: vec![],
            atom_pool: None,
            permanent_elite: Some(elite.clone()),
        };
        config.collect_final_population = true;
        let mut rng = rand::rng();
        let report = run_discovery(&store, &config, &mut rng);

        // Final population must contain the canonical elite chain.
        let elite_steps_json = serde_json::to_string(&elite.0).unwrap();
        let mut found = false;
        for (chain, _comps, _names, _cid) in &report.final_population {
            let steps_json = serde_json::to_string(&chain.0).unwrap();
            if steps_json == elite_steps_json {
                found = true;
                break;
            }
        }
        assert!(
            found,
            "permanent elite was not present in final population after {} gens",
            config.generations
        );
    }

    #[test]
    fn local_rate_with_no_assignments_uses_global() {
        let cfg = DiscoveryConfig::default();
        let r = local_mutation_rate(&cfg, 0);
        assert!((r - cfg.mutation_rate).abs() < 1e-9);
    }

    #[test]
    fn local_rate_with_cluster_multiplier_clamps() {
        let mut cfg = DiscoveryConfig::default();
        cfg.mutation_rate = 0.20;
        cfg.cluster_assignments = vec![0u32, 0, 1, 1];
        cfg.cluster_multipliers.insert(
            0,
            ClusterMultiplier {
                mutation_rate_mult: 2.0,
                ..Default::default()
            },
        );
        cfg.cluster_multipliers.insert(
            1,
            ClusterMultiplier {
                mutation_rate_mult: 0.0,
                ..Default::default()
            },
        );
        // 0.20 × 2.0 = 0.40 → clamped to 0.30
        assert!((local_mutation_rate(&cfg, 0) - 0.30).abs() < 1e-9);
        // 0.20 × 0.0 = 0.0 → clamped to 0.05
        assert!((local_mutation_rate(&cfg, 2) - 0.05).abs() < 1e-9);
    }

    #[test]
    fn local_rate_unknown_cluster_falls_back_to_global() {
        let mut cfg = DiscoveryConfig::default();
        cfg.mutation_rate = 0.10;
        cfg.cluster_assignments = vec![5u32];
        let r = local_mutation_rate(&cfg, 0);
        assert!((r - 0.10).abs() < 1e-9);
    }

    #[test]
    fn local_elitism_count_with_multiplier() {
        let mut cfg = DiscoveryConfig::default();
        cfg.population_size = 100;
        cfg.elitism_fraction = 0.05; // 5 elites globally
        cfg.cluster_assignments = vec![0u32; 100];
        cfg.cluster_multipliers.insert(
            0,
            ClusterMultiplier {
                elitism_mult: 2.0,
                ..Default::default()
            },
        );
        // 5 × 2.0 = 10 elites for cluster 0
        assert_eq!(elite_count_with_cluster_multiplier(&cfg, 0), 10);
    }

    #[test]
    fn early_exit_fires_when_chain_already_verified() {
        // M1 production-droplet contract: if a chain has already been
        // Verified and the lake budget is fully spent, the gen loop must
        // exit immediately instead of running the remaining gens'
        // mutation/crossover/fitness churn. We exercise this by seeding
        // `initial_report.verified` with a fake entry and setting
        // `max_lake_verifications = 0` so the trigger condition
        // (`verified non-empty AND lake_attempts >= max`) holds on gen 1.
        // Ensure env-var gate is ON for this test (default ON; harnesses
        // may have set it to "0" elsewhere).
        // SAFETY: env-var mutation in tests is single-threaded under
        // `cargo test --lib` only when tests don't race for the same
        // var. We restore the prior value at the end to be courteous to
        // any test that reads it later.
        let prior = std::env::var("NASRUDIN_EARLY_EXIT_ON_VERIFIED").ok();
        // SAFETY: tests in this module don't concurrently mutate this
        // env var. Restored at end.
        unsafe {
            std::env::set_var("NASRUDIN_EARLY_EXIT_ON_VERIFIED", "1");
        }

        let store = upstream_store();
        let config = DiscoveryConfig {
            population_size: 8,
            // 50 gens: if early-exit DOESN'T fire, the test will run all
            // 50 (and `generations_run` will be 50). With early-exit, it
            // should be 1.
            generations: 50,
            crossover_rate: 0.6,
            mutation_rate: 0.7,
            tournament_size: 3,
            max_chain_len: 8,
            prover_root: None,
            max_lake_verifications: 0,
            target: None,
            rejected_canonicals: std::sync::Arc::new(HashSet::new()),
            cache_ctx: None,
            novelty_bloom: None,
            mutation_priors: None,
            submit_unverified_top_k: 0,
            dimension_hard_reject: false,
            dimension_var_dims: std::sync::Arc::new(
                std::collections::HashMap::new(),
            ),
            elaborator: None,
            suffix_bias: 0.0,
            elitism_fraction: 0.0,
            collect_final_population: false,
            cluster_multipliers: std::collections::HashMap::new(),
            cluster_assignments: vec![],
            atom_pool: None,
            permanent_elite: None,
        };
        let mut rng = rand::rng();
        let mut initial_report = DiscoveryReport::default();
        // Pre-populate `verified` to simulate "a chain was Verified
        // upstream of this gen" — same observable state the production
        // path lands in after a Lake-success on gen 1.
        initial_report.verified.push(VerifiedDiscovery {
            chain: nasrudin_derive::Chain::new(),
            final_expr: nasrudin_core::Expr::Lit(0, 1),
            canonical: "stub".into(),
            lean_source: String::new(),
            module_path: "Stub".into(),
            generation: 0,
        });
        let population = seed_population(&store, &config, &mut rng, &mut initial_report);
        let report = run_discovery_from_population(
            &store,
            &config,
            population,
            &mut rng,
            initial_report,
        );

        // Early-exit must have fired on gen 1, not run all 50 gens.
        assert_eq!(
            report.generations_run, 1,
            "expected early-exit on gen 1 but got generations_run={}",
            report.generations_run
        );

        // Now verify the gate works: with the env var OFF, the loop
        // should run all 50 gens despite the pre-populated `verified`.
        // SAFETY: see note above.
        unsafe {
            std::env::set_var("NASRUDIN_EARLY_EXIT_ON_VERIFIED", "0");
        }
        let mut initial_report2 = DiscoveryReport::default();
        initial_report2.verified.push(VerifiedDiscovery {
            chain: nasrudin_derive::Chain::new(),
            final_expr: nasrudin_core::Expr::Lit(0, 1),
            canonical: "stub".into(),
            lean_source: String::new(),
            module_path: "Stub".into(),
            generation: 0,
        });
        let population2 = seed_population(&store, &config, &mut rng, &mut initial_report2);
        let report2 = run_discovery_from_population(
            &store,
            &config,
            population2,
            &mut rng,
            initial_report2,
        );
        assert_eq!(
            report2.generations_run, 50,
            "expected all 50 gens when gate is OFF but got generations_run={}",
            report2.generations_run
        );

        // Restore the env-var to whatever it was before this test ran.
        // SAFETY: see note above.
        unsafe {
            match prior {
                Some(v) => std::env::set_var("NASRUDIN_EARLY_EXIT_ON_VERIFIED", v),
                None => std::env::remove_var("NASRUDIN_EARLY_EXIT_ON_VERIFIED"),
            }
        }
    }

    #[test]
    fn cluster_multiplier_default_is_identity() {
        let m = ClusterMultiplier::default();
        assert!((m.mutation_rate_mult - 1.0).abs() < 1e-9);
        assert!((m.elitism_mult - 1.0).abs() < 1e-9);
        assert!((m.kill_fraction - 0.0).abs() < 1e-9);
        assert!((m.diversify_fraction - 0.0).abs() < 1e-9);
    }
}

// Suppress unused-import lint if Path import becomes redundant.
#[allow(dead_code)]
fn _path_used(_: &Path) {}
