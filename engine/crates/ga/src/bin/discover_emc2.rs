//! Spontaneous E=mc² discovery driver — Phase 6.
//!
//! Runs the chain-based GA over the truly upstream SR axiom set with no
//! `DeriveRestEnergy*` strategy registered. The GA seeds populations
//! with random `[IntroduceAxiom(name)]` chains, evolves via mutation +
//! crossover + tournament selection, and (optionally) lake-verifies
//! the top novel candidate(s) per generation.
//!
//! Usage:
//!   discover_emc2                            # dry run (no lake)
//!   discover_emc2 --verify <prover_root>     # lake-verify top candidates
//!   discover_emc2 --gens N --pop M           # tune scale
//!
//! The driver is designed for *long-horizon* runs. With max_lake_verifications
//! at single digits per run, a fresh invocation usually finishes in seconds
//! (dry) or minutes (with lake). To genuinely *find* E=mc² spontaneously,
//! expect to run for hours-to-days of GA evolution and dozens of lake
//! verifications. This binary is the apparatus for that experiment.

use nasrudin_derive::axiom_store::AxiomStore;
use nasrudin_ga::chain_engine::{DiscoveryConfig, run_discovery};
use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let gens: usize = arg_value(&args, "--gens").unwrap_or(50);
    let pop: usize = arg_value(&args, "--pop").unwrap_or(32);
    let max_chain_len: usize = arg_value(&args, "--max-len").unwrap_or(12);
    let max_lake: usize = arg_value(&args, "--max-lake").unwrap_or(3);
    let prover_root: Option<PathBuf> = args
        .iter()
        .position(|a| a == "--verify")
        .and_then(|pos| args.get(pos + 1))
        .map(PathBuf::from);
    let domain: String = args
        .iter()
        .position(|a| a == "--domain")
        .and_then(|pos| args.get(pos + 1).cloned())
        .unwrap_or_else(|| "sr".to_string());

    println!("═══════════════════════════════════════════════════════");
    println!("  Nasrudin Spontaneous Physics Discovery — domain={domain}");
    println!("  No headline-result strategies. No headline axioms.");
    println!("  Pure combinatorics + GA over upstream postulates.");
    println!("═══════════════════════════════════════════════════════");
    println!();

    let mut store = AxiomStore::new();
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
        other => {
            eprintln!("✗ unknown domain `{other}` (try `sr` or `em`)");
            std::process::exit(2);
        }
    };

    println!("▶ Upstream axiom set ({} axioms):", store.len());
    for name in store.names() {
        println!("    • {name}");
    }
    println!();

    if store.get(forbidden_axiom).is_some() {
        eprintln!("✗ FAIL: {forbidden_axiom} leaked into the store. Cheating.");
        std::process::exit(2);
    }
    println!("  ✓ {forbidden_axiom} is NOT in the store. No cheating.");
    println!();

    let config = DiscoveryConfig {
        population_size: pop,
        generations: gens,
        crossover_rate: 0.6,
        mutation_rate: 0.7,
        tournament_size: 3,
        max_chain_len,
        prover_root: prover_root.clone(),
        max_lake_verifications: if prover_root.is_some() { max_lake } else { 0 },
    };

    println!("▶ Running discovery: pop={}, gens={}, max_chain_len={}, lake_budget={}",
        pop, gens, max_chain_len, config.max_lake_verifications);
    println!();

    let mut rng = rand::rng();
    let report = run_discovery(&store, &config, &mut rng);

    println!("▶ Run complete.");
    println!("    Generations:        {}", report.generations_run);
    println!("    Total candidates:   {}", report.total_candidates);
    println!("    Unique executable:  {}", report.unique_executable);
    println!("    Lake attempts:      {}", report.lake_attempts);
    println!("    Verified theorems:  {}", report.verified.len());
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
            if d.canonical.contains("(= v:E (* v:m (^ c:SpeedOfLight n:2)))")
                || d.canonical.contains("E = m * c^2")
                || d.canonical.contains("(= v:E (* (^ c:SpeedOfLight n:2) v:m))")
            {
                println!();
                println!("  ★ E = m·c² SPONTANEOUSLY DERIVED AND VERIFIED ★");
            }
        }
    }
    println!();
}

fn arg_value<T: std::str::FromStr>(args: &[String], flag: &str) -> Option<T> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|pos| args.get(pos + 1))
        .and_then(|s| s.parse().ok())
}
