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
    if let Some(api_url) = std::env::var("NASRUDIN_API_URL").ok().or_else(||
        api_cfg.as_ref().map(|c| c.api_url.clone()))
    {
        let domain_param = match domain.as_str() {
            "sr" => "SpecialRelativity",
            "em" => "Electromagnetism",
            _ => "",
        };
        match fetch_and_extend_store(&api_url, domain_param, &mut store).await {
            Ok((axioms_added, theorems_added)) => {
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
                if store.get(forbidden_axiom).is_some() {
                    eprintln!(
                        "✗ FAIL: peer-fed `{forbidden_axiom}` after seed-sync. Refusing."
                    );
                    std::process::exit(2);
                }
                nasrudin_derive::no_cheat_audit::audit_or_panic(
                    &store,
                    "worker post-seed-sync",
                );
            }
            Err(e) => {
                eprintln!(
                    "  ! seed-sync skipped: {e}\n    (worker will run with local axioms only)"
                );
            }
        }
        println!();
    }

    // Resolve target: --target sr_rest_energy is the canonical first POC.
    // The shape itself is *not* added to the AxiomStore — it's metadata
    // used to bias the search via target_shape + ladder_progress fitness.
    // The no-cheat audit confirms this invariant at boot.
    let target_name = std::env::args()
        .skip_while(|a| a != "--target")
        .nth(1)
        .or_else(|| std::env::var("NASRUDIN_TARGET").ok())
        .unwrap_or_else(|| match domain.as_str() {
            "sr" => "sr_rest_energy".into(),
            _ => String::new(),
        });
    let target_spec = if target_name.is_empty() {
        None
    } else {
        match nasrudin_ga::target::TargetSpec::lookup(&target_name) {
            Some(spec) => {
                println!("▶ Target: {} (ladder of {} rungs)", spec.name, spec.ladder.len());
                Some(spec)
            }
            None => {
                eprintln!("✗ Unknown target spec `{target_name}`. Available: sr_rest_energy");
                std::process::exit(2);
            }
        }
    };

    let config = DiscoveryConfig {
        population_size: pop,
        generations: gens,
        crossover_rate: 0.6,
        mutation_rate: 0.7,
        tournament_size: 3,
        max_chain_len,
        prover_root: prover_root.clone(),
        max_lake_verifications: if prover_root.is_some() { max_lake } else { 0 },
        target: target_spec,
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

/// Fetch `/api/seed?domain={d}&top=200` and fold the response into the
/// local AxiomStore. Returns `(axioms_added, peer_theorems_added)`.
///
/// **Axioms** that the server has but we don't are registered as-is.
/// **Peer theorems** with a non-empty replayable chain are replayed
/// locally to extract the final Expr; that Expr is registered as a
/// synthetic axiom named `theorem_<hex_id>`. Anything that fails to
/// parse / replay is silently skipped — we trust only the math we can
/// reproduce locally, not just whatever the API reports.
async fn fetch_and_extend_store(
    api_url: &str,
    domain: &str,
    store: &mut nasrudin_derive::AxiomStore,
) -> anyhow::Result<(usize, usize)> {
    use nasrudin_core::Expr;
    use nasrudin_derive::{Axiom, Chain, DerivationContext, RuleStep, strategies::DerivationStrategy};

    let url = if domain.is_empty() {
        format!("{api_url}/api/seed?top=200")
    } else {
        format!("{api_url}/api/seed?domain={domain}&top=200")
    };
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(15))
        .build()?;
    let resp = client.get(&url).send().await?;
    if !resp.status().is_success() {
        anyhow::bail!("seed http {}: {}", resp.status(), resp.text().await.unwrap_or_default());
    }
    let body: serde_json::Value = resp.json().await?;

    let mut axioms_added = 0usize;
    if let Some(arr) = body.get("axioms").and_then(|v| v.as_array()) {
        for entry in arr {
            let Some(name) = entry.get("name").and_then(|v| v.as_str()) else { continue };
            if store.get(name).is_some() { continue; }
            let Some(stmt_str) = entry.get("statement").and_then(|v| v.as_str()) else { continue };
            let Ok(stmt) = serde_json::from_str::<Expr>(stmt_str) else { continue };
            let domain_str = entry.get("domain").and_then(|v| v.as_str()).unwrap_or("");
            let parsed_domain = match domain_str {
                "SpecialRelativity" | "special_relativity" => nasrudin_core::Domain::SpecialRelativity,
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
            let chain_val = match t.get("chain_json") { Some(c) => c, None => continue };
            if chain_val.is_null() { continue; }
            let Ok(steps): Result<Vec<RuleStep>, _> = serde_json::from_value(chain_val.clone())
                else { continue };
            if steps.is_empty() { continue; }
            let chain = Chain(steps);
            let mut ctx = DerivationContext::new();
            let Ok(final_expr) = chain.execute(store, &mut ctx) else { continue };

            // Name keyed on canonical-statement bytes so re-pulls don't
            // duplicate. Falls back to the row id hex for robustness.
            let name = if let Some(canon) = t.get("canonical_statement").and_then(|v| v.as_str()) {
                format!("peer_{:016x}", xxhash_rust::xxh64::xxh64(canon.as_bytes(), 0))
            } else {
                continue;
            };
            if store.get(&name).is_some() { continue; }

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

    Ok((axioms_added, theorems_added))
}
