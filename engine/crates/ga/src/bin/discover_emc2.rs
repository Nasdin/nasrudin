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
use nasrudin_ga::chain_engine::{DiscoveryConfig, VerifiedDiscovery, run_discovery};
use std::path::{Path, PathBuf};

const DEFAULT_API_URL: &str = "http://localhost:3001";
const DEFAULT_WORKER_ID: &str = "in-proc-worker-1";

#[tokio::main]
async fn main() {
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

    // ── Resolve API submission config (Task 7.1) ─────────────────────
    // Worker key is REQUIRED *only if* we're going to verify (otherwise
    // there are no discoveries to submit). For dry runs (no `--verify`),
    // we skip the check so devs can run the GA without the API up.
    let api_cfg = if prover_root.is_some() {
        match ApiSubmitConfig::from_env() {
            Ok(cfg) => {
                println!("▶ API submission target: {}", cfg.api_url);
                println!("    worker_id: {}", cfg.worker_id);
                Some(cfg)
            }
            Err(msg) => {
                eprintln!("✗ {msg}");
                eprintln!(
                    "  Set NASRUDIN_WORKER_KEY=nsk_worker_… to enable submission, or"
                );
                eprintln!("  drop the --verify flag for a dry run.");
                std::process::exit(2);
            }
        }
    } else {
        None
    };
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

    println!(
        "▶ Running discovery: pop={}, gens={}, max_chain_len={}, lake_budget={}",
        pop, gens, max_chain_len, config.max_lake_verifications
    );
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

        // ── Submit to /api/ingest, then erase the on-disk Discover*.lean
        //    files so nothing persists in `prover/PhysicsGenerator/Derived/`
        //    going forward (Phase 9 acceptance criterion #14).
        if let (Some(cfg), Some(prover)) = (api_cfg.as_ref(), prover_root.as_ref()) {
            println!();
            println!("▶ Submitting {} discoveries to {}", report.verified.len(), cfg.api_url);
            let domain_str = domain.clone();
            for d in &report.verified {
                match submit_discovery(cfg, &domain_str, d).await {
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

fn arg_value<T: std::str::FromStr>(args: &[String], flag: &str) -> Option<T> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|pos| args.get(pos + 1))
        .and_then(|s| s.parse().ok())
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
        let api_url = std::env::var("NASRUDIN_API_URL")
            .unwrap_or_else(|_| DEFAULT_API_URL.to_string());
        let worker_id = std::env::var("NASRUDIN_WORKER_ID")
            .unwrap_or_else(|_| DEFAULT_WORKER_ID.to_string());
        Ok(Self {
            api_url,
            worker_key,
            worker_id,
        })
    }
}

/// Build the JSON for a single chain. Mirrors the chain-step shape that
/// the API treats opaquely as `serde_json::Value`. We hand-build because
/// `RuleStep` doesn't derive Serialize.
fn chain_to_json(chain: &Chain) -> serde_json::Value {
    let steps: Vec<serde_json::Value> = chain
        .0
        .iter()
        .map(|step| match step {
            RuleStep::IntroduceAxiom { axiom_name } => serde_json::json!({
                "kind": "IntroduceAxiom",
                "axiom_name": axiom_name,
            }),
            RuleStep::SubstituteValue { var, value, reason } => serde_json::json!({
                "kind": "SubstituteValue",
                "var": var,
                "value": value.to_canonical(),
                "reason": reason,
            }),
            RuleStep::AlgebraicSimplify => serde_json::json!({
                "kind": "AlgebraicSimplify",
            }),
            RuleStep::RearrangeEquation { description, target } => serde_json::json!({
                "kind": "RearrangeEquation",
                "description": description,
                "target": target.to_canonical(),
            }),
            RuleStep::TakePositiveRoot => serde_json::json!({
                "kind": "TakePositiveRoot",
            }),
        })
        .collect();
    serde_json::Value::Array(steps)
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

/// POST a single verified discovery to `/api/ingest`.
async fn submit_discovery(
    cfg: &ApiSubmitConfig,
    domain: &str,
    d: &VerifiedDiscovery,
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
        }]
    });
    let client = reqwest::Client::new();
    let resp = client
        .post(format!("{api_url}/api/ingest"))
        .bearer_auth(worker_key)
        .json(&payload)
        .send()
        .await?;
    let status = resp.status();
    if status.is_success() || status == reqwest::StatusCode::CONFLICT {
        return Ok(());
    }
    let body = resp.text().await.unwrap_or_default();
    anyhow::bail!("ingest failed: {status} body={body}");
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
