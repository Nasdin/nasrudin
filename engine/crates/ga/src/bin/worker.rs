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
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

const DEFAULT_API_URL: &str = "http://localhost:3001";
const DEFAULT_WORKER_ID: &str = "in-proc-worker-1";

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
                                consecutive_failures =
                                    consecutive_failures.saturating_add(1);
                                tracing::warn!(
                                    status,
                                    body = %body,
                                    failures = consecutive_failures,
                                    "heartbeat non-2xx"
                                );
                            }
                            Err(e) => {
                                consecutive_failures =
                                    consecutive_failures.saturating_add(1);
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
                    let api_url_for_hydrate = std::env::var("NASRUDIN_API_URL").ok()
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
                    println!(
                        "▶ Worker cold-tier corpus already populated: {initial_count} axioms"
                    );
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
                eprintln!("    ! failed to open worker RocksDB at {}: {e}", rocks_path.display());
                eprintln!("      Falling back to hot-only AxiomStore for this session.");
                AxiomStore::new()
            }
        }
    };
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
        println!("    … ({} more, full set in cold-tier RocksDB)", total - preview.len());
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
            // 30 min connect window: the daemon may still be importing
            // Mathlib if both units came up together. Per-request
            // timeout matches the in-process path.
            match nasrudin_lean_bridge::PersistentElaborator::from_uds(
                uds_path,
                std::time::Duration::from_secs(1800),
                std::time::Duration::from_secs(30),
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
    let mut directive_traces: Vec<nasrudin_ga::clustering::DirectiveTrace> =
        Vec::new();
    // Rolling window of the last 50 centroid hashes seen at apply
    // time. Used to compute an intrinsic-motivation novelty bonus
    // for directives that target rarely-visited cluster lineages.
    let mut hash_history =
        nasrudin_ga::clustering::CentroidHashHistory::with_capacity(50);

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
                let scope_dom = d
                    .get("island_domain")
                    .and_then(|v| v.as_str());
                if let Some(dom) = scope_dom {
                    if dom != canonical_domain_for_compute {
                        continue;
                    }
                }
                let strength = d
                    .get("strength")
                    .and_then(|v| v.as_f64())
                    .unwrap_or(0.0)
                    as f32;
                let strength_bucket = (strength.clamp(0.0, 1.0) * 5.0)
                    .floor()
                    .min(4.0) as u8;
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
            let scaled_gens =
                (chunk_config.generations as f32 * compute_mult).clamp(8.0, 2000.0);
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
        let mut seed_summaries: Vec<nasrudin_ga::clustering::ClusterSummary> =
            Vec::new();

        // Build the report's bookkeeping placeholder once so we can
        // either run the legacy `run_discovery` path or the
        // pre-seeded `run_discovery_from_population` path with
        // matching `total_candidates` accounting.
        let mut initial_report =
            nasrudin_ga::chain_engine::DiscoveryReport::default();
        let report = if let Some(steering_val) = last_steering.as_ref()
            .filter(|_| api_cfg.is_some())
        {
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
                    let names = nasrudin_ga::clustering::extract_axiom_names(
                        &ind.chain,
                    );
                    let f = &ind.fitness;
                    let length_signal = (1.0
                        - (ind.chain.0.len() as f64 / 16.0).min(1.0))
                    .clamp(0.0, 1.0);
                    let comps = [
                        f.novelty.clamp(0.0, 1.0) as f32,
                        f.dimensional.clamp(0.0, 1.0) as f32,
                        length_signal as f32,
                        f.target_shape.max(f.ladder_progress).clamp(0.0, 1.0)
                            as f32,
                    ];
                    (ind.chain.clone(), comps, names)
                })
                .collect();
            let (s_summaries, s_assignment) =
                nasrudin_ga::clustering::cluster_and_summarise(
                    &chains_with_fitness,
                    k_for_island,
                    canonical_domain,
                    chunk_seed,
                );
            // Tag each individual with its seed cluster_id so child
            // lineage carries the cluster through crossover.
            for (i, ind) in seed_pop.iter_mut().enumerate() {
                ind.cluster_id =
                    *s_assignment.assignments.get(i).unwrap_or(&0);
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
                let strength = d
                    .get("strength")
                    .and_then(|v| v.as_f64())
                    .unwrap_or(0.0)
                    as f32;
                let strength_bucket =
                    (strength.clamp(0.0, 1.0) * 5.0).floor().min(4.0) as u8;
                let Some(cid) =
                    nasrudin_ga::clustering::match_directive_to_cluster(
                        hash,
                        &centroids,
                        0.10,
                    )
                else {
                    continue;
                };
                let arms = directive_arms_for_slot(
                    steering_val,
                    canonical_domain,
                    &action,
                    strength_bucket,
                );
                let multiplier_choice =
                    pick_multiplier_choice(&arms, strength);
                let mult_value =
                    lookup_action_multiplier(&action, multiplier_choice);
                let m = chunk_config
                    .cluster_multipliers
                    .entry(cid)
                    .or_default();
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
                (chunk_config.mutation_rate * aggregate_mut_mult)
                    .clamp(0.05, 0.30);
            chunk_config.elitism_fraction =
                (chunk_config.elitism_fraction as f64 * aggregate_elite_mult)
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
            run_discovery(&store, &chunk_config, &mut rng)
        };

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
            let (summaries, _assignment) =
                nasrudin_ga::clustering::cluster_and_summarise(
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
            if let Err(e) = post_cluster_report(
                api_cfg_for_cluster,
                chunk_i as i64,
                k_for_island as i16,
                canonical_domain,
                &summaries,
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
                                    *trace
                                        .samples
                                        .last()
                                        .unwrap_or(&trace.mean_fitness_at_apply),
                                ),
                            None => *trace
                                .samples
                                .last()
                                .unwrap_or(&trace.mean_fitness_at_apply),
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
                    if let Err(e) = post_directive_feedback(
                        api_cfg_for_cluster,
                        &feedback_batch,
                    )
                    .await
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
                for (dom, bucket, choice, _pop_at_apply) in
                    pending_compute_pulls.iter()
                {
                    feedback_batch.push(serde_json::json!({
                        "island_domain": dom,
                        "strength_bucket": bucket,
                        "multiplier_choice": choice,
                        "reward": reward,
                    }));
                }
                if let Err(e) =
                    post_compute_feedback(api_cfg_for_cluster, &feedback_batch).await
                {
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
                    if let Err(e) =
                        submit_discovery(cfg, &domain, d, worker_verified).await
                    {
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
    };

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
) -> anyhow::Result<()> {
    let summaries_json: Vec<serde_json::Value> = summaries
        .iter()
        .map(|s| serde_json::to_value(s).unwrap_or(serde_json::Value::Null))
        .collect();
    // The endpoint stores worker_id as PG UUID. Production workers
    // typically have a string identifier (e.g. "pool-worker-1"); derive
    // a deterministic UUID v5 in the DNS namespace so reports from
    // the same logical worker collapse to the same row regardless of
    // restart, and we never need server-side worker provisioning just
    // for cluster reports.
    let worker_uuid = uuid::Uuid::new_v5(
        &uuid::Uuid::NAMESPACE_DNS,
        cfg.worker_id.as_bytes(),
    );
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
            && slot.get("strength_bucket").and_then(|v| v.as_i64())
                == Some(strength_bucket as i64)
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
    let blend = ((total as f64 - 50.0) / (LINUCB_FULL_WEIGHT_AT - 50.0))
        .clamp(0.0, 1.0);
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
            && slot.get("strength_bucket").and_then(|v| v.as_i64())
                == Some(strength_bucket as i64)
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
async fn fetch_and_extend_store(
    api_url: &str,
    domain: &str,
    store: &mut nasrudin_derive::AxiomStore,
) -> anyhow::Result<(usize, usize, Option<serde_json::Value>)> {
    use nasrudin_core::Expr;
    use nasrudin_derive::{Axiom, Chain, DerivationContext, RuleStep, strategies::DerivationStrategy};

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
        let bytes = postcard::to_allocvec(&hnsw)?;
        let sidecar = sidecar_path(main);
        std::fs::write(&sidecar, &bytes)?;
        Ok(())
    }
}
