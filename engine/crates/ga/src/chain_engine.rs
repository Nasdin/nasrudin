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
    ChainIndividual, ChainVerifyOutcome, mutate_chain, splice_chains,
    verify_chain_cached,
};
use nasrudin_core::Expr;
use nasrudin_derive::{AxiomStore, Chain, RuleStep};
use rand::Rng;
use rand::seq::IteratorRandom;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

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
    pub lake_attempts: usize,
    pub verified: Vec<VerifiedDiscovery>,
    pub top_fitness_canonical: Option<String>,
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
pub fn run_discovery(
    store: &AxiomStore,
    config: &DiscoveryConfig,
    rng: &mut impl Rng,
) -> DiscoveryReport {
    let mut report = DiscoveryReport::default();

    // ── Seed initial population: each individual is a 1-step chain
    //    `[IntroduceAxiom(random_axiom)]`. The GA will compose more
    //    interesting chains via mutation/crossover.
    let mut population: Vec<ChainIndividual> = (0..config.population_size)
        .map(|_| {
            let chain = random_chain_seed(store, rng, &mut report);
            let fit = crate::chain_ga::evaluate_chain_fitness_with_target(&chain, store, config.target.as_ref());
            ChainIndividual::new(chain, fit)
        })
        .collect();

    // Dedup set keyed on canonical form of (final_expr) for verified
    // discoveries so we don't lake-build the same theorem twice.
    let mut verified_canonicals: HashSet<String> = HashSet::new();

    // ── Evolution loop
    for gen_idx in 0..config.generations {
        report.generations_run = gen_idx + 1;

        // Generate offspring.
        let mut offspring: Vec<ChainIndividual> = Vec::with_capacity(config.population_size);
        while offspring.len() < config.population_size {
            let p1 = tournament_select(&population, config.tournament_size, rng);
            let p2 = tournament_select(&population, config.tournament_size, rng);
            let (mut c1, mut c2) = if rng.random_bool(config.crossover_rate) {
                splice_chains(&p1.chain, &p2.chain, rng)
            } else {
                (p1.chain.clone(), p2.chain.clone())
            };
            if rng.random_bool(config.mutation_rate) {
                mutate_chain(&mut c1, store, rng);
            }
            if rng.random_bool(config.mutation_rate) {
                mutate_chain(&mut c2, store, rng);
            }
            for child in [c1, c2] {
                if child.is_empty() || child.len() > config.max_chain_len {
                    continue;
                }
                let fit = crate::chain_ga::evaluate_chain_fitness_with_target(&child, store, config.target.as_ref());
                offspring.push(ChainIndividual::new(child, fit));
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

        // Try lake-verify on the top novel candidate(s) of this gen.
        if let Some(ref prover_root) = config.prover_root {
            if report.lake_attempts < config.max_lake_verifications {
                if let Some(top) = pick_top_for_verify(
                    &offspring,
                    &verified_canonicals,
                    &config.rejected_canonicals,
                    store,
                ) {
                    report.lake_attempts += 1;
                    let basename = format!("DiscoverGen{gen_idx}");
                    let theorem_name = format!("discover_gen{gen_idx}");
                    match verify_chain_cached(
                        &top.chain,
                        store,
                        prover_root.as_path(),
                        &basename,
                        &theorem_name,
                        config.cache_ctx.as_ref(),
                    ) {
                        ChainVerifyOutcome::Verified {
                            lean_source,
                            module_path,
                        } => {
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
                        _ => {
                            // Skip silently; pre-filter / Lean rejection /
                            // toolchain absence are all expected.
                        }
                    }
                }
            }
        }

        population = offspring;
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

    report
}

fn random_chain_seed(
    store: &AxiomStore,
    rng: &mut impl Rng,
    _report: &mut DiscoveryReport,
) -> Chain {
    let names: Vec<String> = store.names().into_iter().map(String::from).collect();
    if names.is_empty() {
        return Chain::new();
    }
    // **Iter 19 — seed-bank diversification.** ~20 % of seeds load
    // ALL upstream axioms (in shuffled order); the rest seed with
    // 3-5 random axioms as before. This is *not* domain hard-coding:
    // the seed-bank simply says "start with all the available
    // material loaded" — it doesn't tell the GA *what* to derive.
    // Without it, the GA rarely accumulates all 4 useful axioms
    // (four_momentum, mink, mass, rest_frame) in one chain.
    if rng.random_bool(0.2) {
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
    for _ in 0..n_axioms {
        let name = names.iter().choose(rng).unwrap().clone();
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

fn pick_top_for_verify<'a>(
    offspring: &'a [ChainIndividual],
    seen: &HashSet<String>,
    rejected: &HashSet<Vec<u8>>,
    store: &AxiomStore,
) -> Option<&'a ChainIndividual> {
    for ind in offspring {
        if ind.fitness.novelty < 1.0 || ind.fitness.nasrudin_relevance < 1.0 {
            continue;
        }
        if let Some(expr) = run_chain_for_final(&ind.chain, store) {
            let canon = expr.to_canonical();
            // Skip canonicals we've verified this run, AND canonicals
            // any peer worker has already rejected via lake build.
            // Both sets are local to this process; the rejected set
            // was populated at startup from `/api/rejected_hashes`.
            let canon_hash = nasrudin_core::canonical_hash(&canon);
            if !seen.contains(&canon) && !rejected.contains(&canon_hash) {
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
}

// Suppress unused-import lint if Path import becomes redundant.
#[allow(dead_code)]
fn _path_used(_: &Path) {}
