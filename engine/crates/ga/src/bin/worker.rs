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
        eprintln!(
            "  Submissions in this mode are flagged worker_verified=false; the server's"
        );
        eprintln!(
            "  lazy lake-promotion drain handles kernel confirmation, which is slower"
        );
        eprintln!("  and may produce cascade-rejects on bogus chains.");
    }
    let submit_top_k: usize = arg_value(&args, "--submit-top-k")
        .unwrap_or(if no_local_lake { 4 } else { 0 });
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
    if research_mode {
        println!("  ▶ research-mode ON — will poll /api/conjecture/claim");
    }
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
            // forbidden-axiom-by-name is moot here since we register
            // multiple domains; the canonical audit (audit_or_panic)
            // is the load-bearing check below.
            ""
        }
        other => {
            eprintln!("✗ unknown domain `{other}` (try `sr`, `em`, or `pure-math`)");
            std::process::exit(2);
        }
    };

    println!("▶ Upstream axiom set ({} axioms):", store.len());
    for name in store.names() {
        println!("    • {name}");
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
    if let Some(api_url) = std::env::var("NASRUDIN_API_URL").ok().or_else(||
        api_cfg.as_ref().map(|c| c.api_url.clone()))
    {
        let domain_param = match domain.as_str() {
            "sr" => "SpecialRelativity",
            "em" => "Electromagnetism",
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
                    println!("▶ Negative-result memo: {} pre-rejected canonicals will be skipped", set.len());
                    std::sync::Arc::new(set)
                }
                Err(e) => {
                    eprintln!("  ! rejected-hashes fetch failed: {e}; running without negative memo");
                    std::sync::Arc::new(std::collections::HashSet::new())
                }
            }
        } else {
            std::sync::Arc::new(std::collections::HashSet::new())
        }
    };

    // Bloom-filter pre-check over the rejected set. The bloom is sized
    // for ~100k entries with FPR 0.001. CPU-cache-friendly compared to
    // the HashSet probe, so even when the set is small the check is
    // faster. Only built when there's something to prepopulate; an
    // empty bloom would always-miss and regress to the HashSet path
    // anyway. Sized = max(rejected.len() * 4, 4096) so workers in
    // early-cluster days don't have a near-saturated filter.
    let novelty_bloom: Option<std::sync::Arc<bloomfilter::Bloom<[u8]>>> = {
        if rejected_canonicals.is_empty() {
            None
        } else {
            let n = std::cmp::max(rejected_canonicals.len() * 4, 4096);
            // `bloomfilter::Bloom::new_for_fp_rate` returns the Bloom
            // directly (no Result) in the version this workspace uses.
            let mut b = bloomfilter::Bloom::new_for_fp_rate(n, 0.001);
            for h in rejected_canonicals.iter() {
                b.set(h.as_slice());
            }
            println!(
                "▶ Novelty bloom: {} entries pre-loaded (capacity {n}, FPR ~0.1%)",
                rejected_canonicals.len()
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
            .map(|v| !matches!(v.trim().to_lowercase().as_str(), "0" | "false" | "no" | "off"))
            .unwrap_or(true);
    let primary_domain = match domain.as_str() {
        "sr" => nasrudin_core::Domain::SpecialRelativity,
        "em" => nasrudin_core::Domain::Electromagnetism,
        // Pure-math / mixed: no canonical var→dim table; gate becomes
        // a no-op because every var infers to None.
        _ => nasrudin_core::Domain::PureMath,
    };
    let dimension_var_dims = std::sync::Arc::new(
        nasrudin_derive::domain_variable_dimensions(&primary_domain),
    );
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
    let elaborator: Option<std::sync::Arc<nasrudin_lean_bridge::PersistentElaborator>> =
        if !no_persistent && prover_root.is_some() {
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
        } else {
            if no_persistent {
                println!("▶ Persistent elaborator DISABLED (lake-only path)");
            }
            None
        };

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
        prover_root: if no_local_lake { None } else { prover_root.clone() },
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
    };

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
        .or_else(|| std::env::var("NASRUDIN_CHUNKS").ok().and_then(|s| s.parse().ok()))
        .unwrap_or(4);
    let gens_per_chunk = (gens / chunks).max(1);
    let api_url_for_resync = std::env::var("NASRUDIN_API_URL").ok();
    let domain_param_for_resync = match domain.as_str() {
        "sr" => "SpecialRelativity",
        "em" => "Electromagnetism",
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
    let mut total_candidates = 0usize;
    let mut total_unique = 0usize;
    let mut current_rejected = rejected_canonicals.clone();
    // Latest steering snapshot from `/api/seed`. Updated on every
    // chunk-boundary re-sync; applied to the per-chunk DiscoveryConfig
    // via `apply_steering_knobs` so the LLM cluster steerer's
    // mutation rate / population size land on the next chunk's GA.
    let mut last_steering: Option<serde_json::Value> = None;

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
    // Slot count we report to the server on every paid claim. v1
    // uses `--max-lake` as a proxy; v2 should plug in a real
    // ResourceBudget detector.
    let paid_available_slots: u32 = (max_lake as u32).max(1);
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
    let paid_slice_store: std::sync::Arc<AxiomStore> =
        std::sync::Arc::new(store.clone());

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
                        eprintln!(
                            "  ! paid slice for {} failed: {e}; releasing",
                            job.job_id
                        );
                        let _ = client.release(job.job_id).await;
                    }
                    continue;
                }
                Ok(None) => {
                    tracing::debug!("paid-jobs claim: queue empty / floor protected");
                }
                Err(e) => {
                    tracing::warn!(
                        "paid-jobs claim failed: {e}; falling through"
                    );
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
                    tracing::warn!("research-mode claim failed: {e}; falling through to background");
                }
            }
        }


        // Periodic embed-index refresh. Cheap when index is current
        // (one HTTP HEAD-equivalent call per chunk). Off by default;
        // flip on with NASRUDIN_EMBED_AUTOPULL=1.
        if let Ok(autopull) = std::env::var("NASRUDIN_EMBED_AUTOPULL")
            && matches!(autopull.trim().to_lowercase().as_str(), "1" | "true" | "yes")
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
                    println!("▶ chunk {} rejected-set: +{delta} new pre-rejected canonicals", chunk_i + 1);
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
        if let Some(ref s) = last_steering {
            if nasrudin_ga::steering_knobs::apply_steering_knobs(&mut chunk_config, s) {
                tracing::debug!(
                    rate = chunk_config.mutation_rate,
                    pop = chunk_config.population_size,
                    "chunk config patched from steering"
                );
            }
        }
        let report = run_discovery(&store, &chunk_config, &mut rng);
        total_candidates += report.total_candidates;
        total_unique += report.unique_executable;
        total_lake += report.lake_attempts;
        total_lake_passed += report.lake_passed;
        total_persistent_attempts += report.persistent_attempts;
        total_dim_rejected += report.dim_rejected;
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
                    if let Err(e) =
                        submit_discovery(cfg, &domain, d, worker_verified).await
                    {
                        eprintln!("  ! chunk-submit failed: {e}");
                    }
                }
            }
        }
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
        verified: combined_verified,
        top_fitness_canonical: None,
    };

    println!("▶ Run complete.");
    println!("    Generations:         {}", report.generations_run);
    println!("    Total candidates:    {}", report.total_candidates);
    println!("    Unique executable:   {}", report.unique_executable);
    println!("    Dimension rejected:  {}", report.dim_rejected);
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
    use nasrudin_ga::chain_engine::{run_discovery, DiscoveryConfig};
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
    let mut filtered = AxiomStore::new();
    filtered.load_classical_mechanics_postulates();
    let mut missing = Vec::<String>::new();
    for name in &suggestion.axiom_set {
        if let Some(a) = full_store.get(name) {
            filtered.register(a.clone());
        } else {
            missing.push(name.clone());
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
    let research_dim_var_dims = std::sync::Arc::new(
        nasrudin_derive::domain_variable_dimensions(&research_domain),
    );
    let research_dim_hard_reject = std::env::var("NASRUDIN_DIMENSION_HARD_REJECT")
        .map(|v| !matches!(v.trim().to_lowercase().as_str(), "0" | "false" | "no" | "off"))
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

    let outcome = if submitted_any { "Verified" } else { "NoResult" };
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
/// Sync from `/api/seed`. Returns `(axioms_added, peer_theorems_added,
/// steering_payload)`. `steering_payload` is the full JSON value of
/// `body["steering"]` if the server included it, else `None`. The
/// caller passes it to `apply_steering_knobs` to bias the next chunk.
async fn fetch_and_extend_store(
    api_url: &str,
    domain: &str,
    store: &mut nasrudin_derive::AxiomStore,
) -> anyhow::Result<(usize, usize, Option<serde_json::Value>)> {
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

    // Cluster steering. The server folds the live `SteeringConfig`
    // into every `/api/seed` response alongside an etag; we log
    // visibility info here and bubble the payload up to the chunk
    // loop so it can call `apply_steering_knobs` on the next
    // DiscoveryConfig.
    let steering_payload = body.get("steering").cloned();
    if let Some(ref steering) = steering_payload {
        let etag = steering
            .get("etag")
            .and_then(|v| v.as_str())
            .unwrap_or("?");
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
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(15))
        .build()?;
    let resp = client
        .get(format!("{api_url}/api/rejected_hashes"))
        .send()
        .await?;
    if !resp.status().is_success() {
        anyhow::bail!("rejected_hashes http {}", resp.status());
    }
    let body: serde_json::Value = resp.json().await?;
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
        let cs_url = format!(
            "{}/api/embed/checksum",
            api_url.trim_end_matches('/')
        );
        let client = reqwest::Client::new();
        let resp = match client.get(&cs_url).send().await {
            Ok(r) => r,
            Err(e) => {
                tracing::debug!("embed checksum fetch failed: {e}");
                return Ok(false);
            }
        };
        if !resp.status().is_success() {
            return Ok(false);
        }
        #[derive(serde::Deserialize)]
        struct CsBody {
            hex: String,
        }
        let cs: CsBody = match resp.json().await {
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
        let bin_url = format!("{}/api/embed/index.bin", api_url.trim_end_matches('/'));
        let bytes = client.get(&bin_url).send().await?.bytes().await?;
        if let Some(parent) = local_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let tmp = with_tmp_suffix(local_path);
        std::fs::write(&tmp, &bytes)?;
        std::fs::rename(&tmp, local_path)?;
        tracing::info!(
            "embed: wrote {} bytes to {:?}",
            bytes.len(),
            local_path
        );
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
        use nasrudin_embed::index::{sidecar_path, CosinePoint};
        use nasrudin_embed::{IndexHeader, EMBED_DIM};

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
        let bytes = bincode::serialize(&hnsw)?;
        let sidecar = sidecar_path(main);
        std::fs::write(&sidecar, &bytes)?;
        Ok(())
    }
}
