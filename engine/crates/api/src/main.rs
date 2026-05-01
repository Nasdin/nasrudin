//! Physics Generator HTTP API server.
//!
//! Full daemon: REST endpoints, SSE discovery stream, GA evolution thread,
//! and Lean4 verification workers.

use physics_api::{auth, handlers, rate_limit, state::{AppState, SharedAxiomStore}};

use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use axum::{
    Json, Router,
    extract::{Path, Query, State},
    http::{HeaderValue, Method},
    routing::get,
};
use serde::Deserialize;
use tower_governor::GovernorLayer;
use tower_http::cors::CorsLayer;
use tower_http::compression::CompressionLayer;
use tower_http::trace::TraceLayer;
use tower_sessions::{MemoryStore, SessionManagerLayer};
use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

use nasrudin_core::{Domain, Theorem, TheoremId, VerificationStatus};
use nasrudin_derive::AxiomStore;
use nasrudin_ga::{DiscoveryEvent, GaConfig, GaEngine, GaStatusSnapshot};
use nasrudin_lean_bridge::LeanBridge;
use nasrudin_rocks::TheoremDb;

use axum::routing::{delete, post};

// GaStatusSnapshot is now imported from nasrudin_ga

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // Initialize tracing
    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with(tracing_subscriber::fmt::layer())
        .init();

    tracing::info!("Starting Physics Generator API server");

    // Load environment from .env in project root (parent of engine/)
    let env_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.env");
    match dotenvy::from_path(&env_path) {
        Ok(_) => tracing::info!("Loaded .env from {}", env_path.display()),
        Err(e) => tracing::warn!("No .env loaded ({}): using existing env vars", e),
    }

    // Connect to PostgreSQL (optional — auth features require it)
    let pg = match std::env::var("DATABASE_URL") {
        Ok(database_url) => {
            match nasrudin_pg::connect_and_migrate(&nasrudin_pg::PgConfig::new(&database_url)).await
            {
                Ok(conn) => {
                    tracing::info!("PostgreSQL connected");
                    Some(conn)
                }
                Err(e) => {
                    tracing::warn!("PostgreSQL connection failed ({e}): auth endpoints disabled");
                    None
                }
            }
        }
        Err(_) => {
            tracing::info!("DATABASE_URL not set: running without PostgreSQL (auth disabled)");
            None
        }
    };

    // Open RocksDB (use env var or default path)
    let db_path = std::env::var("ROCKS_DB_PATH").unwrap_or_else(|_| "./data/theorems.db".into());
    let db = Arc::new(TheoremDb::new(&db_path)?);
    tracing::info!("RocksDB opened at {db_path}");

    // Phase 9 disaster-recovery: if Postgres is connected and RocksDB is empty,
    // repopulate the embedded store from the relational mirror. Runs exactly
    // once before the Axum router starts. Hydration failures are logged and
    // boot continues — the operator can wipe /data/rocks and retry.
    if let Some(ref pg_conn) = pg {
        if let Err(e) = physics_api::hydration::hydrate_rocks_from_pg_if_empty(&db, pg_conn).await {
            tracing::error!("RocksDB hydration from Postgres failed: {e}; continuing startup");
        }
    }

    // ── AxiomStore boot — two-tier hot/cold construction ────────────
    //
    // Hot tier: hand-coded postulates + PhysLean catalog (~2-5 k
    // axioms, ~10 MB resident). Cold tier: the ~195 k Mathlib +
    // Unknown corpus, RocksDB-backed via the same shared block cache
    // as the theorem store. First boot streams math_corpus.json into
    // the cold tier (~30 s, ~50 MB peak); subsequent boots see
    // `is_hydrated() == true` and skip the JSON parse entirely.
    //
    // This keeps the API process resident under ~500 MB on the 2 GB
    // production droplet, where the previous eager-load peaked at
    // ~3.8 GB during `serde_json::from_str` of the corpus file and
    // OOMed.
    let prover_root = std::env::var("PROVER_ROOT").unwrap_or_else(|_| "../prover".into());
    let math_corpus_path =
        std::path::Path::new(&prover_root).join("../physlean-extract/output/math_corpus.json");
    const MATHLIB_MIN_ENTRIES: u64 = 10_000;

    let corpus_db: Arc<dyn nasrudin_rocks::CorpusBackend> = Arc::new(
        nasrudin_rocks::CorpusDb::on_existing_db(db.shared_db()),
    );

    // First-boot cold-tier hydration. Idempotent — running on an
    // already-hydrated DB is a no-op (we still bail loudly if the
    // JSON is missing AND the cold tier is empty).
    let already_hydrated = corpus_db.is_hydrated().unwrap_or(false);
    if !already_hydrated {
        tracing::warn!(
            "Cold-tier corpus not hydrated. Streaming {} into RocksDB \
             (one-time cost, ~30 s)...",
            math_corpus_path.display()
        );
        let hydrate_path = math_corpus_path.clone();
        let hydrate_corpus = Arc::clone(&corpus_db);
        let hydrated = tokio::task::spawn_blocking(move || {
            AxiomStore::hydrate_math_corpus_to_cold(
                &*hydrate_corpus,
                &hydrate_path,
            )
        })
        .await
        .map_err(|e| anyhow::anyhow!("hydration task join: {e}"))?;
        match hydrated {
            Ok(count) => {
                if count < MATHLIB_MIN_ENTRIES {
                    panic!(
                        "Mathlib corpus too small after hydration ({count} entries, \
                         need ≥{MATHLIB_MIN_ENTRIES}). Re-run `just extract-mathlib`."
                    );
                }
                tracing::info!(
                    count,
                    "Cold-tier corpus hydration complete (one-time cost amortised)"
                );
            }
            Err(e) => {
                panic!(
                    "Mathlib corpus REQUIRED at boot. Hydration failed for {}: {e}\n\
                     Run `just extract-mathlib` first.",
                    math_corpus_path.display()
                );
            }
        }
    } else {
        let count = corpus_db.count().unwrap_or(0);
        if count < MATHLIB_MIN_ENTRIES {
            panic!(
                "Cold-tier corpus too small ({count} entries, need ≥{MATHLIB_MIN_ENTRIES}). \
                 Re-hydrate by wiping the corpus_axiom / corpus_domain / corpus_meta CFs \
                 and re-running boot, or wipe ROCKS_DB_PATH and re-import."
            );
        }
        tracing::info!(count, "Cold-tier corpus already hydrated");
    }

    // Hot tier: PhysLean catalog + hand-coded postulates. Each
    // loader is O(few thousand) and runs in <100 ms.
    let mut axiom_store = AxiomStore::with_corpus(Arc::clone(&corpus_db));
    let catalog_path =
        std::path::Path::new(&prover_root).join("../physlean-extract/output/catalog.json");
    match axiom_store.load_from_catalog(&catalog_path) {
        Ok(count) => tracing::info!("Loaded {count} axioms from {} into hot tier", catalog_path.display()),
        Err(e) => tracing::warn!("Failed to load catalog ({e}): continuing with upstream only"),
    }
    axiom_store.load_special_relativity_upstream();
    axiom_store.load_electromagnetism_upstream();
    // Classical mechanics — postulates only (Newton's laws, momentum
    // definition, kinetic energy, work). Required for the ladder a
    // worker traverses on the way from Lorentz invariance to E=mc².
    // Until PhysLean ships these upstream they live in
    // `nasrudin_derive::postulates_classical`.
    axiom_store.load_classical_mechanics_postulates();
    // Quantum mechanics — Schrödinger evolution, [x,p]=iℏ, Born rule,
    // Hermitian observables, unitarity, normalization. PhysLean's QM
    // namespace is Standard-Model surface; the *foundations* are
    // upstream of PhysLean and live in `postulates_quantum`.
    axiom_store.load_quantum_mechanics_postulates();
    // Thermodynamics — laws + ideal gas + free-energy / enthalpy /
    // Gibbs definitions. Scalar form for chain composability.
    axiom_store.load_thermodynamics_postulates();
    // Statistical mechanics — Boltzmann entropy, Gibbs distribution,
    // partition function ↔ free energy, equipartition.
    axiom_store.load_statistical_mechanics_postulates();
    // General relativity — Einstein field equations, geodesic
    // equation, equivalence principle, Newtonian limit.
    axiom_store.load_general_relativity_postulates();

    tracing::info!(
        "AxiomStore boot complete — hot: {} entries, cold: {} entries (Mathlib + Unknown)",
        axiom_store.iter_hot_names().len(),
        corpus_db.count().unwrap_or(0),
    );

    // No-cheat audit: hard-fail boot if any registered axiom matches a
    // known headline result. Headline results (E=mc², photon dispersion,
    // mass-shell) must be *derived* by the GA, not loaded as starting
    // blocks — otherwise the rediscovery proof-of-concept is vacuous.
    nasrudin_derive::no_cheat_audit::audit_or_panic(&axiom_store, "physics-api boot");
    tracing::info!("No-cheat audit passed: 0 forbidden headlines in AxiomStore");

    let axiom_store = SharedAxiomStore::new(axiom_store);

    // Admin token for `/api/admin/*` endpoints (corpus reload).
    // When unset, admin endpoints return 503 — production deployments
    // must set this in the systemd unit / .env.
    let admin_token = std::env::var("ADMIN_TOKEN").ok().filter(|s| !s.is_empty());
    if admin_token.is_some() {
        tracing::info!("ADMIN_TOKEN configured — admin endpoints enabled");
    } else {
        tracing::warn!("ADMIN_TOKEN unset — /api/admin/* endpoints disabled");
    }

    let firebase_project_id = std::env::var("FIREBASE_PROJECT_ID")
        .ok()
        .filter(|s| !s.is_empty());
    let firebase_jwks = Arc::new(physics_api::firebase_auth::JwksCache::new());
    if firebase_project_id.is_some() {
        // Pre-warm the JWKs cache so the first sign-in doesn't pay a
        // ~200ms HTTP round-trip latency. Failure here is non-fatal —
        // the cache will lazily retry on first /api/auth/firebase-session
        // call. We just log and continue.
        let jwks_for_warm = Arc::clone(&firebase_jwks);
        tokio::spawn(async move {
            match jwks_for_warm.warm().await {
                Ok(_) => tracing::info!("firebase JWKs pre-warmed"),
                Err(e) => tracing::warn!(error = %e, "firebase JWKs pre-warm failed; will lazy-fetch"),
            }
        });
        tracing::info!("Firebase Auth configured");
    } else {
        tracing::info!(
            "FIREBASE_PROJECT_ID unset — /api/auth/firebase-session returns 503"
        );
    }

    // Cache layer (Phase A.5). Constructed unconditionally; per-flag
    // gating (NASRUDIN_CACHE_ATTEMPTS=1, etc.) happens at the call sites.
    let cache_ctx = match physics_api::cache::CacheCtx::build(&db) {
        Ok(c) => {
            tracing::info!(
                "cache layer built (attempts={}, tactic_priors={}, persistent_lean={})",
                c.config.attempts_enabled,
                c.config.tactic_priors_enabled,
                c.config.persistent_lean_enabled,
            );
            Some(Arc::new(c))
        }
        Err(e) => {
            tracing::warn!("cache layer init failed ({e}); continuing without caches");
            None
        }
    };

    // Embedding index (Phase B). Off by default; flip on with
    // NASRUDIN_EMBED_ENABLED=1.
    let embed_enabled = std::env::var("NASRUDIN_EMBED_ENABLED")
        .map(|v| matches!(v.trim().to_lowercase().as_str(), "1" | "true" | "yes"))
        .unwrap_or(false);
    let embed_path: Option<std::path::PathBuf> = if embed_enabled {
        Some(
            std::env::var("NASRUDIN_EMBED_OUT")
                .map(std::path::PathBuf::from)
                .unwrap_or_else(|_| {
                    let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
                    std::path::PathBuf::from(home).join(".nasrudin/embed/corpus.embed")
                }),
        )
    } else {
        None
    };
    let embed: Option<Arc<nasrudin_embed::EmbeddingIndex>> =
        embed_path.as_ref().and_then(|p| {
            if !p.exists() {
                tracing::info!("embed: index not yet built at {p:?}; serving without");
                return None;
            }
            match nasrudin_embed::EmbeddingIndex::open(p) {
                Ok(i) => Some(Arc::new(i)),
                Err(e) => {
                    tracing::warn!("embed: open {p:?} failed: {e}");
                    None
                }
            }
        });

    // Concept search: load the fastembed Embedder eagerly when the index
    // is open. ~1 s cold start; we'd rather pay it at boot than on the
    // first user request. NASRUDIN_SKIP_EMBED_DOWNLOAD=1 short-circuits
    // this for environments without the model cached (CI, etc.).
    let embedder: Option<Arc<nasrudin_embed::Embedder>> = if embed.is_some()
        && std::env::var("NASRUDIN_SKIP_EMBED_DOWNLOAD").is_err()
    {
        match nasrudin_embed::Embedder::new() {
            Ok(e) => {
                tracing::info!("embedder loaded (BGE-small-en-v1.5, ~150 MB resident)");
                Some(Arc::new(e))
            }
            Err(e) => {
                tracing::warn!("embedder init failed: {e}; concept search disabled");
                None
            }
        }
    } else {
        None
    };

    if embed_enabled {
        if let Some(p) = embed_path.as_ref() {
            let cron =
                Arc::new(physics_api::embed_cron::EmbedCron::new(Arc::clone(&db), p.clone()));
            tokio::spawn(Arc::clone(&cron).run());
            tracing::info!("embed_cron spawned (out_path = {p:?})");
        }
    }

    // LLM key vault (Phase C). Decode the AES-256-GCM key once; when
    // unset, /api/me/llm-keys returns 503.
    let llm_encrypt_key = nasrudin_llm::encryption::load_encrypt_key_from_env();
    if llm_encrypt_key.is_some() {
        tracing::info!("NASRUDIN_KEY_ENCRYPT configured — /api/me/llm-keys enabled");
    } else {
        tracing::warn!("NASRUDIN_KEY_ENCRYPT unset — /api/me/llm-keys returns 503");
    }

    // Channels
    let (candidates_tx, candidates_rx) = std::sync::mpsc::channel::<Vec<Theorem>>();
    let (verified_tx, verified_rx) = std::sync::mpsc::channel::<Vec<Theorem>>();
    let (discovery_tx, _discovery_rx) = tokio::sync::broadcast::channel::<DiscoveryEvent>(256);

    // Shutdown signal
    let shutdown = Arc::new(AtomicBool::new(false));

    // In-process GA. Phase 9 distributed mode: workers run worker
    // externally and POST to /api/ingest, so the API daemon is a pure
    // membrane by default. Set NASRUDIN_API_RUN_INPROC_GA=1 to also run a
    // GA thread inside the API process (legacy single-node mode; contends
    // with external workers for the prover lake build cache).
    let inproc_ga = std::env::var("NASRUDIN_API_RUN_INPROC_GA")
        .map(|v| !v.is_empty() && v != "0")
        .unwrap_or(false);
    let ga_status = Arc::new(std::sync::Mutex::new(GaStatusSnapshot {
        running: inproc_ga,
        ..Default::default()
    }));

    if inproc_ga {
        tracing::info!("In-process GA enabled (NASRUDIN_API_RUN_INPROC_GA=1)");
        let ga_config = GaConfig::default();
        let ga_db = Arc::clone(&db);
        let ga_axiom_store = (*axiom_store.load()).clone();
        let ga_discovery_tx = discovery_tx.clone();
        let ga_shutdown = Arc::clone(&shutdown);
        let ga_status_ref = Arc::clone(&ga_status);
        std::thread::Builder::new()
            .name("ga-engine".into())
            .spawn(move || {
                let engine = GaEngine::new(ga_config, ga_db, ga_axiom_store);
                engine.run_with_status(
                    candidates_tx,
                    verified_rx,
                    ga_discovery_tx,
                    ga_shutdown,
                    ga_status_ref,
                );
            })?;

        let verify_db = Arc::clone(&db);
        let verify_discovery_tx = discovery_tx.clone();
        tokio::spawn(async move {
            run_verification_workers(candidates_rx, verified_tx, verify_db, verify_discovery_tx)
                .await;
        });
    } else {
        tracing::info!(
            "In-process GA disabled — API is a pure ingest membrane. Workers should POST to /api/ingest."
        );
        // Drop the unused channel ends so cargo doesn't warn.
        drop(candidates_tx);
        drop(candidates_rx);
        drop(verified_tx);
        drop(verified_rx);
    }

    // Phase 9: construct LakeBuilder + (optionally) ReverifyQueue before
    // AppState. The drain loop is only spawned when Postgres is configured,
    // because the queue's flip-verified path writes through to PG.
    let prover_root_path: std::path::PathBuf =
        std::env::var("PROVER_ROOT").unwrap_or_else(|_| "../prover".into()).into();
    let lake_workspace_root: std::path::PathBuf = std::env::var("LAKE_WORKSPACE_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| std::env::temp_dir());
    let lake = Arc::new(physics_api::lake_builder::LakeBuilder::new(
        prover_root_path,
        lake_workspace_root,
        2,
    ));

    // Warm the prover's `.lake/build/` so the first verification doesn't
    // pay the multi-minute cold-cache cost. Spawned in the background —
    // we don't block the listener on `lake build`. Workers may submit
    // before warmup finishes; their first verifications will pay full
    // build cost, subsequent ones reuse the warm cache.
    {
        let lake = Arc::clone(&lake);
        tokio::spawn(async move {
            if let Err(e) = lake.warmup().await {
                tracing::warn!("lake warmup failed: {e}");
            }
        });
    }

    let (reverify_event_tx, _reverify_event_rx) =
        tokio::sync::broadcast::channel::<physics_api::reverify::DiscoveryEvent>(256);

    let (conjecture_event_tx, _conjecture_event_rx) = tokio::sync::broadcast::channel::<
        physics_api::conjecture::ConjectureEvent,
    >(256);

    let reverify = pg.as_ref().map(|pg_conn| {
        Arc::new(physics_api::reverify::ReverifyQueue {
            rocks: Arc::clone(&db),
            pg: pg_conn.clone(),
            lake: Arc::clone(&lake),
            axiom_store: axiom_store.clone(),
            discovery_tx: reverify_event_tx.clone(),
            cache_ctx: cache_ctx.clone(),
        })
    });

    // Lazy lake-build promotion (P-Task 2). Spawned only when PG is
    // available since the drain fetches `lean_source` from PG to feed
    // the lake-builder.
    let lake_promotion = pg.as_ref().map(|pg_conn| {
        Arc::new(physics_api::lake_promotion::LakePromotion::new(
            Arc::clone(&db),
            pg_conn.clone(),
            Arc::clone(&lake),
            reverify_event_tx.clone(),
        ))
    });

    // Phase 9 Task 4.1: per-worker token-bucket limiter (60 req/min default).
    let worker_rate_limiter = Arc::new(physics_api::rate_limit::WorkerRateLimiter::new(60));

    // Stripe billing — optional. Without env vars the /api/billing/* routes
    // return 503 but the rest of the API works.
    let billing = match physics_api::billing::stripe_client::BillingClient::from_env() {
        Ok(c) => {
            tracing::info!("Stripe billing client configured");
            Some(c)
        }
        Err(e) => {
            tracing::info!("Stripe billing disabled: {e}");
            None
        }
    };

    // Cluster steerer + paid-job state — initialised at boot to a
    // sane default and rotated by the steerer task (`steerer::cycle`).
    let initial_steering = physics_api::steerer::schema::default_config();
    let initial_body = serde_json::to_vec(&initial_steering).unwrap_or_default();
    let initial_etag = xxhash_rust::xxh64::xxh64(&initial_body, 0);
    let initial_snapshot = physics_api::state::SteeringSnapshot {
        config: serde_json::to_value(&initial_steering)
            .unwrap_or(serde_json::Value::Null),
        etag: initial_etag,
        started_at: chrono::Utc::now(),
    };

    // Trust-bypass plumbing (admin panel).
    let trust_cache = physics_api::trust::TrustCache::new(
        std::time::Duration::from_secs(30),
        4096,
    );
    let (trust_invalidation_tx, _) =
        tokio::sync::broadcast::channel::<physics_api::trust::CacheInvalidation>(256);
    let trusted_spot_check_rate: u32 = std::env::var("TRUSTED_SPOT_CHECK_RATE")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(50);

    let state = Arc::new(AppState {
        db,
        pg,
        axiom_store,
        discovery_tx,
        ga_status,
        lake,
        reverify_event_tx,
        reverify,
        worker_rate_limiter,
        admin_token,
        cache_ctx: cache_ctx.clone(),
        embed,
        embedder,
        embed_path,
        llm_encrypt_key,
        conjecture_event_tx,
        lake_promotion,
        billing,
        seed_cache: Arc::new(std::sync::Mutex::new(
            std::collections::HashMap::new(),
        )),
        steering: Arc::new(arc_swap::ArcSwap::from_pointee(initial_snapshot)),
        cluster_config: Arc::new(arc_swap::ArcSwap::from_pointee(
            physics_api::state::ClusterConfigSnapshot::default(),
        )),
        directive_arms: Arc::new(arc_swap::ArcSwap::from_pointee(
            physics_api::state::DirectiveArmsSnapshot::default(),
        )),
        compute_arms: Arc::new(arc_swap::ArcSwap::from_pointee(
            physics_api::state::ComputeArmsSnapshot::default(),
        )),
        capacity: Arc::new(physics_api::jobs::capacity::CapacityTracker::new()),
        job_events: Arc::new(dashmap::DashMap::new()),
        landing_stats: Arc::new(physics_api::handlers::stats::LandingStatsCache::new()),
        workers_list_cache: Arc::new(physics_api::handlers::workers::WorkersListCache::new()),
        contributors_list_cache: Arc::new(physics_api::handlers::contributors::ContributorsListCache::new()),
        theorems_recent_cache: Arc::new(
            physics_api::handlers::theorems::TheoremsRecentCache::new(),
        ),
        firebase_project_id,
        firebase_jwks,
        stripe_http: reqwest::Client::new(),
        stripe_base_url: std::env::var("STRIPE_BASE_URL")
            .unwrap_or_else(|_| "https://api.stripe.com".into()),
        stripe_secret: std::env::var("STRIPE_SECRET_KEY").unwrap_or_default(),
        impersonation_signing_key: std::env::var("IMPERSONATION_SIGNING_KEY")
            .ok()
            .and_then(|hex_key| hex::decode(hex_key.trim()).ok())
            .filter(|b| b.len() >= 16),
        bulk_run_progress_tx: tokio::sync::broadcast::channel(256).0,
        trust_cache: trust_cache.clone(),
        trust_invalidation_tx: trust_invalidation_tx.clone(),
        trusted_spot_check_rate,
    });

    // Reseed CapacityTracker.paid_slots from the DB. The counter is
    // purely in-memory and resets to 0 across restarts; without this
    // reseed, the explorer-floor enforcement under-reports committed
    // paid capacity until existing leases either heartbeat-renew or
    // get reaped — which can take minutes and lets paid jobs eat into
    // the explorer-fleet floor that's supposed to be reserved.
    if let Some(pg) = state.pg.as_ref() {
        match nasrudin_pg::query::conjecture_jobs::sum_in_flight_paid_slots(pg).await {
            Ok(n) if n > 0 => {
                let n_u32 = u32::try_from(n).unwrap_or(u32::MAX);
                state.capacity.add_paid_slots(n_u32);
                tracing::info!(
                    paid_slots = n_u32,
                    "Reseeded CapacityTracker.paid_slots from in-flight conjecture_jobs",
                );
            }
            Ok(_) => {
                tracing::info!("No in-flight paid jobs at startup; CapacityTracker starts at 0");
            }
            Err(e) => {
                tracing::warn!(error = %e, "Failed to reseed paid_slots; starting at 0");
            }
        }
    }

    // Trust-cache invalidation listener: subscribed to the same broadcast
    // channel; purges affected entries when admin endpoints commit a
    // trust-altering mutation. Surgical for ApiKey/User; wholesale for All.
    {
        let cache = trust_cache.clone();
        let mut rx = trust_invalidation_tx.subscribe();
        let pg_for_listener = state.pg.clone();
        tokio::spawn(async move {
            use physics_api::trust::CacheInvalidation as I;
            while let Ok(msg) = rx.recv().await {
                match msg {
                    I::ApiKey(id) => cache.invalidate(&id),
                    I::User(user_id) => {
                        if let Some(pg) = &pg_for_listener
                            && let Ok(rows) =
                                nasrudin_pg::query::api_keys::list_by_user(pg, user_id).await
                        {
                            for r in rows {
                                cache.invalidate(&r.id);
                            }
                        }
                    }
                    I::All => cache.purge_all(),
                }
            }
        });
    }

    // Phase 9 Task 3.4: spawn the reverify drain loop iff Postgres is wired.
    if let Some(ref reverify) = state.reverify {
        tokio::spawn(Arc::clone(reverify).drain_loop());
        tracing::info!("Reverify drain loop spawned");
    } else {
        tracing::info!("Reverify drain loop disabled (no PostgreSQL)");
    }

    // Phase E: spawn the conjecture lease reaper iff Postgres is wired.
    // Requeues stale `state='Running' AND lease_expires_at < NOW()` jobs
    // every 30s and emits `worker_lost` events so SSE subscribers see it.
    if state.pg.is_some() {
        let reaper = Arc::new(physics_api::conjecture::reaper::ConjectureLeaseReaper::new(
            Arc::clone(&state),
        ));
        tokio::spawn(Arc::clone(&reaper).run());
        tracing::info!("Conjecture lease reaper spawned");
    } else {
        tracing::info!("Conjecture lease reaper disabled (no PostgreSQL)");
    }

    // Bulk-runs restart reaper. On startup, mark any rows still
    // status='running' from before the restart as 'aborted' so the UI
    // doesn't show a fake live run.
    if let Some(pg) = state.pg.clone() {
        tokio::spawn(async move {
            if let Ok(n) = nasrudin_pg::query::bulk_runs::reap_stale(&pg).await
                && n > 0
            {
                tracing::warn!("Reaped {n} stale bulk_runs at startup");
            }
        });
    }

    // Impersonation expiry tick — 60s. Marks ended_at + writes a
    // system audit row for sessions whose expires_at has passed without
    // a manual end.
    if let Some(pg) = state.pg.clone() {
        physics_api::admin::impersonation_expiry::spawn(pg);
    }

    // Refund reconciler. Walks `refund_records` rows still pending after
    // 90s and asks Stripe whether they actually went through; mirrors
    // the result back into refund_records.status. No-op when
    // STRIPE_SECRET_KEY is unset.
    if state.pg.is_some() {
        physics_api::billing::refund_reconciler::spawn(
            state.pg.as_ref().unwrap().clone(),
            state.stripe_http.clone(),
            state.stripe_base_url.clone(),
            state.stripe_secret.clone(),
        );
    }

    // Sponsorship backfill. Opt-in via BACKFILL_SPONSORSHIPS=1; when
    // set, paginates Stripe `customers.list`, joins on
    // `users.stripe_customer_id`, and upserts every active
    // subscription + recent (<=90d) one-time charge into
    // `user_sponsorships`. Only useful for cold-starting a fresh
    // environment that already has live customers — once webhooks are
    // delivering, the live path keeps the table current.
    if let (Some(pg), Some(billing)) = (state.pg.clone(), state.billing.clone()) {
        physics_api::billing::sponsorship_backfill::spawn_if_enabled(
            pg,
            billing,
            state.stripe_secret.clone(),
            state.stripe_base_url.clone(),
        );
    }

    // RocksDB-primary ingest write-behind: spawn the PG drain loop iff
    // Postgres is wired. The hot ingest path persists to RocksDB +
    // pg_insert_queue synchronously; this task drains the queue every
    // 500ms and batch-inserts into PG. On API restart, the queue is
    // walked at boot so anything not yet flushed gets a fresh attempt.
    if let Some(ref pg) = state.pg {
        let rocks = Arc::clone(&state.db);
        let pg = pg.clone();
        tokio::spawn(physics_api::pg_drain::drain_loop(rocks, pg));
        tracing::info!("PG drain loop spawned (RocksDB-primary ingest)");
    }

    // Lazy lake-build promotion drain + background crawler (P-Task 2).
    // The drain handles synchronous + seed-triggered + manual-button
    // promotions; the crawler ensures every ChainVerified row eventually
    // graduates to LakeVerified or Rejected even without consumption
    // pressure.
    if let Some(ref promotion) = state.lake_promotion {
        let p = Arc::clone(promotion);
        tokio::spawn(physics_api::lake_promotion::drain_loop(p));
        let p = Arc::clone(promotion);
        tokio::spawn(physics_api::lake_promotion::crawler_loop(p));
        tracing::info!("Lake-promotion drain + crawler spawned");
    }

    // Cluster steerer + paid-job reaper. Both require PostgreSQL.
    // The steerer is gated on the `GRADIENT_API_KEY` env var being
    // present; when absent (or `STEERER_DISABLED=1`) we keep the
    // default `default_config()` snapshot live and skip the LLM
    // call entirely. Useful for local dev without a Gradient key.
    if let Some(ref pg) = state.pg {
        let pg_for_reaper = pg.clone();
        tokio::spawn(async move {
            // ±10 % jitter on every tick. With multiple API instances
            // running, fixed-cadence ticks march in lockstep and dogpile
            // PG; randomising the period spreads load evenly.
            use rand::Rng as _;
            loop {
                let jitter_ms: u64 = rand::rng().random_range(0..12_000);
                let period =
                    std::time::Duration::from_secs(54) + std::time::Duration::from_millis(jitter_ms);
                tokio::time::sleep(period).await;
                match physics_api::jobs::reaper::reap_dead_leases(&pg_for_reaper).await {
                    Ok(n) if n > 0 => {
                        tracing::info!(n, "reaped expired conjecture-job leases")
                    }
                    Ok(_) => {}
                    Err(e) => tracing::error!(error=%e, "lease reaper failed"),
                }
            }
        });
        tracing::info!("Conjecture lease reaper (paid jobs) spawned");

        // Worker status reaper: mark workers as inactive if they haven't
        // been seen in the last 60 seconds. This ensures the "active workers"
        // metric on the landing page reflects actual recent activity.
        let pg_for_worker_reaper = pg.clone();
        tokio::spawn(async move {
            // ±10 % jitter — same rationale as the lease reaper above.
            use rand::Rng as _;
            loop {
                let jitter_ms: u64 = rand::rng().random_range(0..6_000);
                let period =
                    std::time::Duration::from_secs(27) + std::time::Duration::from_millis(jitter_ms);
                tokio::time::sleep(period).await;
                match physics_api::jobs::reaper::mark_stale_workers(&pg_for_worker_reaper).await {
                    Ok(n) if n > 0 => {
                        tracing::info!(n, "marked stale workers as inactive")
                    }
                    Ok(_) => {}
                    Err(e) => tracing::error!(error=%e, "worker status reaper failed"),
                }
            }
        });
        tracing::info!("Worker status reaper spawned");

        // Materialise UCB1 bandit arms for every (island_domain, K).
        // Idempotent — pre-existing rows are left alone, so this is
        // safe to call every boot. Without this the cycle's first
        // round of UCB1 selection would see an empty arm list and
        // fall through to DEFAULT_K for every island.
        if let Err(e) = physics_api::steerer::bandit::ensure_all_arms(pg).await {
            tracing::warn!(error=%e, "bandit ensure_all_arms failed; \
                cluster K will fall back to default until next boot");
        } else {
            tracing::info!("Cluster bandit arms ensured");
        }

        // Materialise the per-(island, action, strength_bucket,
        // multiplier_choice) UCB1 arm rows for the directive bandit.
        // 600 rows; idempotent. Without this the worker's UCB1
        // selection sees an empty slot and the static-formula
        // fallback handles every directive — correct but no learning.
        if let Err(e) = physics_api::steerer::directive_bandit::ensure_all_arms(pg).await {
            tracing::warn!(error=%e, "directive_bandit ensure_all_arms failed; \
                per-cluster multipliers will fall back to static formula until next boot");
        } else {
            tracing::info!("Cluster directive bandit arms ensured");
        }

        // Compute-scaling bandit: 6 islands × 5 strength buckets ×
        // 5 multiplier choices = 150 rows. Idempotent.
        if let Err(e) =
            physics_api::steerer::directive_bandit::ensure_all_compute_arms(pg).await
        {
            tracing::warn!(error=%e, "compute bandit ensure_all_compute_arms failed; \
                test-time-compute scaling will fall back to baseline until next boot");
        } else {
            tracing::info!("Cluster compute bandit arms ensured");
        }

        // LinUCB contextual bandit sufficient-statistics rows: 24
        // rows (6 islands × 4 actions). Each row starts at A = λ·I,
        // b = 0. Math is pure CPU, runs inline in directive_feedback.
        if let Err(e) =
            physics_api::steerer::directive_bandit::ensure_all_linucb_rows(pg).await
        {
            tracing::warn!(error=%e, "LinUCB ensure_all_linucb_rows failed; \
                contextual generalisation falls back to discrete UCB1 only");
        } else {
            tracing::info!("LinUCB sufficient-statistics rows ensured");
        }

        // Compute-bandit LinUCB rows (6 islands).
        if let Err(e) =
            physics_api::steerer::directive_bandit::ensure_all_compute_linucb_rows(pg)
                .await
        {
            tracing::warn!(error=%e, "compute LinUCB ensure_all_compute_linucb_rows \
                failed; compute scaling falls back to discrete UCB1");
        } else {
            tracing::info!("Compute LinUCB sufficient-statistics rows ensured");
        }

        // Hourly purge of cluster_reports older than 7 days. Bandit
        // arms hold the long-running statistics; the per-chunk rows
        // are only needed for the most-recent prompt + reward window.
        let pg_for_cluster_purge = pg.clone();
        tokio::spawn(async move {
            let mut tick = tokio::time::interval(std::time::Duration::from_secs(3600));
            tick.tick().await; // skip the immediate first tick
            loop {
                tick.tick().await;
                let cutoff = chrono::Utc::now() - chrono::Duration::days(7);
                match nasrudin_pg::query::cluster_reports::purge_older_than(
                    &pg_for_cluster_purge,
                    cutoff,
                )
                .await
                {
                    Ok(n) if n > 0 => {
                        tracing::info!(n, "purged old cluster_reports rows")
                    }
                    Ok(_) => {}
                    Err(e) => tracing::warn!(error=%e, "cluster_reports purge failed"),
                }
            }
        });

        // Daily purge of directive_pull_events older than 30 days.
        // The bandit's running aggregate (cluster_directive_arms)
        // holds the long-running statistics; the event log is for
        // offline training only and a 30-day window is plenty.
        let pg_for_events_purge = pg.clone();
        tokio::spawn(async move {
            let mut tick = tokio::time::interval(std::time::Duration::from_secs(86_400));
            tick.tick().await; // skip the immediate first tick
            loop {
                tick.tick().await;
                let cutoff = chrono::Utc::now() - chrono::Duration::days(30);
                match nasrudin_pg::query::directive_pull_events::purge_older_than(
                    &pg_for_events_purge,
                    cutoff,
                )
                .await
                {
                    Ok(n) if n > 0 => {
                        tracing::info!(n, "purged old directive_pull_events rows")
                    }
                    Ok(_) => {}
                    Err(e) => tracing::warn!(error=%e,
                        "directive_pull_events purge failed"),
                }
            }
        });

        let steerer_disabled = std::env::var("STEERER_DISABLED").is_ok();
        if !steerer_disabled {
            match nasrudin_llm::GradientProvider::from_env() {
                Ok(provider) => {
                    let model_id = std::env::var("STEERER_MODEL")
                        .unwrap_or_else(|_| "kimi-k2.5".into());
                    match provider.list_models().await {
                        Ok(models) => {
                            if !models.iter().any(|m| m == &model_id) {
                                tracing::warn!(
                                    model=%model_id, available=?models,
                                    "STEERER_MODEL not in Gradient catalog; \
                                     steerer will still run but may 4xx"
                                );
                            } else {
                                tracing::info!(model=%model_id, "steerer model verified");
                            }
                        }
                        Err(e) => tracing::warn!(
                            error=%e,
                            "Gradient /v1/models probe failed; steerer will run anyway"
                        ),
                    }
                    let cadence_s: u64 = std::env::var("STEERER_CADENCE_SECONDS")
                        .ok()
                        .and_then(|s| s.parse().ok())
                        .unwrap_or(600);
                    let pg_for_steerer = pg.clone();
                    let state_for_steerer = Arc::clone(&state);
                    let caller = physics_api::steerer::cycle::GradientCaller::new(
                        provider,
                        model_id.clone(),
                    );
                    tokio::spawn(async move {
                        let mut tick = tokio::time::interval(
                            std::time::Duration::from_secs(cadence_s),
                        );
                        // Skip the immediate first tick — give the
                        // rest of the daemon a moment to settle and
                        // workers a chance to register their slots.
                        tick.tick().await;
                        loop {
                            tick.tick().await;
                            match physics_api::steerer::cycle::run_one_cycle(
                                &state_for_steerer,
                                &pg_for_steerer,
                                &caller,
                                &model_id,
                            )
                            .await
                            {
                                Ok(id) => {
                                    tracing::info!(cycle_id = %id, "steerer cycle persisted")
                                }
                                Err(e) => {
                                    tracing::error!(error=%e, "steerer cycle failed")
                                }
                            }
                        }
                    });
                    tracing::info!(cadence_s, "cluster steerer spawned");
                }
                Err(e) => {
                    tracing::info!(
                        error = %e,
                        "GRADIENT_API_KEY unset; cluster steerer disabled \
                         (default_config snapshot remains live)"
                    );
                }
            }
        } else {
            tracing::info!("STEERER_DISABLED set; cluster steerer disabled");
        }
    }

    // CORS configuration — origin is env-driven so dev keeps localhost:3000
    // and prod (https://nasrudin.org) doesn't have to be hot-patched at the
    // reverse proxy. Set CORS_ALLOWED_ORIGIN in the environment.
    let cors_origin = std::env::var("CORS_ALLOWED_ORIGIN")
        .unwrap_or_else(|_| "http://localhost:3000".to_string());
    let cors = CorsLayer::new()
        .allow_origin(cors_origin.parse::<HeaderValue>()?)
        .allow_methods([Method::GET, Method::POST, Method::DELETE, Method::OPTIONS])
        .allow_headers([
            axum::http::header::CONTENT_TYPE,
            axum::http::header::AUTHORIZATION,
            axum::http::header::ACCEPT,
            axum::http::header::COOKIE,
        ])
        .allow_credentials(true);

    // Build grouped sub-routers with per-group rate limits.
    // Each group gets its own GovernorLayer (GCRA, per-IP keying).

    // API-standard: core read API (60 req/min, burst 20)
    //
    // Theorem read endpoints are served by `handlers::theorems::*` against the
    // PostgreSQL mirror (Phase 9 Task 5.1). The legacy RocksDB-backed
    // `recent_theorems` / `search_theorems` / `get_theorem` are intentionally
    // unwired — they remain in this file as fallbacks for the lineage/proof
    // routes which still consume RocksDB-only graph data.
    //
    // Route ordering note: `/api/theorems/{hash}/lean` and
    // `/api/theorems/{id}/lineage` etc. are sibling-specific paths under the
    // generic `/api/theorems/{id}` — axum's matchit picks them by specificity
    // regardless of declaration order, but we still register the more
    // specific routes first for readability.
    let api = Router::new()
        .route("/api/ga/status", get(ga_status_handler))
        .route("/api/featured", get(handlers::featured::featured))
        .route(
            "/api/theorems/{hash}/lean",
            get(handlers::theorems::lean_download),
        )
        .route("/api/theorems/recent", get(handlers::theorems::recent))
        .route("/api/theorems/{id}/lineage", get(get_lineage))
        .route("/api/theorems/{id}/proof", get(get_proof))
        // P-Task 4: manual "Verify with Lake" button. POST is
        // user-triggered, GET is the polling status endpoint.
        .route(
            "/api/theorems/{id}/verify",
            post(handlers::manual_verify::verify),
        )
        .route(
            "/api/theorems/{id}/verify-status",
            get(handlers::manual_verify::verify_status),
        )
        .route("/api/theorems/{id}", get(handlers::theorems::by_id))
        .route("/api/theorems/{id}", delete(delete_theorem_handler))
        .route("/api/theorems", get(handlers::theorems::list))
        // Negative-result memo: list of canonical_hash bytes for every
        // Rejected theorem. Workers pull this to skip pre-rejected
        // chains during fitness eval — see worker's
        // RejectedSet on startup. Closes the "every worker re-tries
        // the same losing chains independently" gap.
        .route(
            "/api/rejected_hashes",
            get(handlers::theorems::rejected_hashes),
        )
        .route("/api/domains", get(list_domains))
        .route("/api/axioms", get(list_axioms))
        .route("/api/seed", get(handlers::seed::seed))
        // Cold-tier corpus dump for worker hydration. Streams every
        // entry of `CF_CORPUS_AXIOM` as line-delimited JSON. Workers
        // call this once on first boot to populate their local
        // RocksDB; subsequent boots short-circuit on the ETag.
        // ~150 MB transfer, ~30 s on a typical home connection.
        .route("/api/corpus/dump", get(handlers::corpus_dump::corpus_dump))
        .route("/api/steering", get(handlers::steering::steering))
        .route("/api/search", post(handlers::search::search))
        .route(
            "/api/search/concept",
            get(handlers::concept_search::concept_search),
        )
        .layer(GovernorLayer::new(rate_limit::api_standard()));

    // Health-relaxed: monitoring & liveness (120 req/min, burst 30)
    let health = Router::new()
        .route("/api/health", get(self::health))
        .route("/api/stats", get(stats))
        .route("/api/stats/landing", get(handlers::stats::landing))
        // P-Task 9: Prometheus exposition for Grafana scraping. No
        // auth gate; Caddy restricts source IPs in production.
        .route("/metrics", get(physics_api::metrics::metrics))
        .layer(GovernorLayer::new(rate_limit::health_relaxed()));

    // Admin panel. Every route is gated by the `RequireAdmin` extractor
    // (session OR ADMIN_TOKEN bearer) and every mutation writes a row
    // through `perform_audited`. Same rate-limit bucket as auth-strict —
    // a stolen admin session is the threat, brute-force is.
    let admin = Router::new()
        .route(
            "/api/admin/reload_corpus",
            post(handlers::admin::corpus::reload_corpus),
        )
        .route(
            "/api/admin/steering/recent",
            get(handlers::admin::steering::steering_recent),
        )
        .route(
            "/api/admin/steering/force",
            post(handlers::admin::steering::steering_force),
        )
        .route("/api/admin/users", get(handlers::admin::users::list))
        .route(
            "/api/admin/users/{id}",
            get(handlers::admin::users::detail),
        )
        .route(
            "/api/admin/users/{id}/admin",
            post(handlers::admin::users::set_admin),
        )
        .route(
            "/api/admin/users/{id}/trust",
            post(handlers::admin::users::set_trust),
        )
        .route(
            "/api/admin/users/{id}/spot_check_rate",
            post(handlers::admin::users::set_spot_check_rate),
        )
        .route(
            "/api/admin/users/{id}/plan",
            post(handlers::admin::users::set_plan),
        )
        .route(
            "/api/admin/users/{id}/credits",
            post(handlers::admin::users::adjust_credits),
        )
        .route(
            "/api/admin/api_keys/{id}",
            delete(handlers::admin::api_keys::revoke),
        )
        .route(
            "/api/admin/api_keys/{id}/trust",
            post(handlers::admin::api_keys::set_trust),
        )
        .route(
            "/api/admin/jobs/{id}/cancel",
            post(handlers::admin::jobs::cancel),
        )
        .route(
            "/api/admin/users/{id}/refund",
            post(handlers::admin::refund::refund),
        )
        .route(
            "/api/admin/users/{id}/impersonate",
            post(handlers::admin::impersonate::start),
        )
        .route(
            "/api/admin/impersonate/end",
            post(handlers::admin::impersonate::end_impersonation),
        )
        .route(
            "/api/admin/users/bulk",
            post(handlers::admin::bulk::start),
        )
        .route(
            "/api/admin/users/bulk/{run_id}/stream",
            get(handlers::admin::bulk::stream),
        )
        .route("/api/admin/audit", get(handlers::admin::audit_log::list))
        .route("/api/admin/stats", get(handlers::admin::stats::stats))
        // Reject every admin route while an impersonation session is in
        // flight. The marker is set by `impersonation_layer`; when present,
        // this guard returns 403 before RequireAdmin even runs.
        .layer(axum::middleware::from_fn(
            physics_api::impersonation::block_during_impersonation,
        ))
        .layer(GovernorLayer::new(rate_limit::auth_strict()));

    // SSE: no rate limit (long-lived connection)
    let sse = Router::new()
        .route(
            "/api/events/discoveries",
            get(handlers::events::discoveries),
        )
        .route("/api/events/stats", get(handlers::events::stats));

    // Embed: read-only public access to the corpus index (Phase B).
    // Workers poll checksum on heartbeat and download index.bin on
    // mismatch — both safe to expose without auth (the index content
    // is derived from the public corpus).
    let embed_routes = Router::new()
        .route("/api/embed/checksum", get(handlers::embed::checksum))
        .route("/api/embed/index.bin", get(handlers::embed::index_bin))
        .layer(GovernorLayer::new(rate_limit::api_standard()));

    // Public workers list — readable without auth (returns [] if PG unavailable).
    let workers_public = Router::new()
        .route("/api/workers", get(handlers::workers::list))
        // Public contributors leaderboard — users ranked by theorems
        .route("/api/contributors", get(handlers::contributors::list))
        .route("/api/contributors/{id}", get(handlers::contributors::get_user_workers))
        // Public profile + sponsorship summary. No auth — these are
        // intentionally world-readable so contributors can link to
        // their profile pages from anywhere. Sensitive fields
        // (email, plan_tier, stripe ids) are filtered in the
        // handler.
        .route("/api/users/{id}", get(handlers::users::public_profile))
        .route(
            "/api/users/{id}/sponsorship",
            get(handlers::users::public_sponsorship),
        )
        .layer(GovernorLayer::new(rate_limit::api_standard()));

    // Start with core routes
    let mut app = Router::new()
        .merge(api)
        .merge(health)
        .merge(admin)
        .merge(sse)
        .merge(embed_routes)
        .merge(workers_public);

    // Add auth routes only if PostgreSQL is available
    if state.pg.is_some() {
        let session_store = MemoryStore::default();
        let session_layer = SessionManagerLayer::new(session_store).with_secure(false); // TODO: set true behind TLS in production

        // Auth-strict: brute-force protection (5 req/min, burst 5).
        // Impersonation block: an impersonating admin must not be able to
        // start a new auth session masquerading as the target.
        let auth_strict = Router::new()
            .route(
                "/api/auth/firebase-session",
                axum::routing::post(auth::firebase_session),
            )
            .layer(axum::middleware::from_fn(
                physics_api::impersonation::block_during_impersonation,
            ))
            .layer(GovernorLayer::new(rate_limit::auth_strict()));

        // Auth-session: lightweight session ops (30 req/min, burst 10).
        // Logout blocked during impersonation (would log out the *admin*,
        // not the impersonated user — confusing semantics). /api/auth/me
        // intentionally NOT blocked: the frontend uses it to render the
        // banner.
        let auth_session = Router::new()
            .route(
                "/api/auth/logout",
                axum::routing::post(auth::logout).layer(axum::middleware::from_fn(
                    physics_api::impersonation::block_during_impersonation,
                )),
            )
            .route("/api/auth/me", get(auth::me))
            .layer(GovernorLayer::new(rate_limit::auth_session()));

        // Platform-user: authenticated user CRUD on api keys, saved searches,
        // preferences, and per-user stats. Cookie or Bearer nsk_live_ tokens.
        //
        // A sub-router covers the *sensitive* surface that must be blocked
        // during impersonation (mint/revoke API keys, billing, preferences
        // write). Anything that's a read or a non-credential write
        // (saved-searches, library, conjecture progress) stays in the main
        // platform_user router and is allowed during impersonation — the
        // AuthUser substitution makes those reads naturally scoped to the
        // target.
        let block_imp = || {
            axum::middleware::from_fn(physics_api::impersonation::block_during_impersonation)
        };
        let platform_user_sensitive = Router::new()
            .route(
                "/api/api-keys",
                axum::routing::post(handlers::api_keys::create),
            )
            .route("/api/api-keys/{id}", delete(handlers::api_keys::revoke))
            .route(
                "/api/preferences",
                axum::routing::patch(handlers::preferences::patch),
            )
            .route("/api/billing/checkout", post(handlers::billing::checkout))
            .route("/api/billing/portal", post(handlers::billing::portal))
            .layer(block_imp());

        let platform_user = Router::new()
            .route("/api/api-keys", get(handlers::api_keys::list))
            .route(
                "/api/saved-searches",
                axum::routing::post(handlers::saved_searches::create),
            )
            .route("/api/saved-searches", get(handlers::saved_searches::list))
            .route(
                "/api/saved-searches/{id}",
                delete(handlers::saved_searches::delete),
            )
            .route(
                "/api/saved-searches/{id}",
                axum::routing::patch(handlers::saved_searches::patch_label),
            )
            .route("/api/preferences", get(handlers::preferences::get))
            .route("/api/me/stats", get(handlers::me::stats))
            .route("/api/me/profile", get(handlers::me::get_profile))
            .route(
                "/api/me/profile",
                axum::routing::patch(handlers::me::update_profile),
            )
            .route("/api/me/workers", get(handlers::me::workers))
            .route("/api/me/llm-keys", get(handlers::llm_keys::list))
            .route("/api/me/llm-keys", post(handlers::llm_keys::set_key))
            .route(
                "/api/me/llm-keys/{provider}",
                delete(handlers::llm_keys::revoke),
            )
            .route("/api/conjecture", post(handlers::conjecture::create))
            .route(
                "/api/conjecture/{id}",
                get(handlers::conjecture::get_one),
            )
            .route(
                "/api/conjecture/{id}/start",
                post(handlers::conjecture::start),
            )
            .route(
                "/api/conjecture/{id}/sse",
                get(handlers::conjecture::sse),
            )
            .route(
                "/api/conjecture/{id}/paper",
                post(handlers::conjecture::start_paper_draft),
            )
            .route(
                "/api/conjecture/{id}/paper.md",
                get(handlers::conjecture::get_paper),
            )
            .route("/api/me/conjectures", get(handlers::conjecture::list_mine))
            .route(
                "/api/me/library/theorems",
                post(handlers::me_library::save_theorem)
                    .get(handlers::me_library::list_saved),
            )
            .route(
                "/api/me/library/theorems/{id}",
                delete(handlers::me_library::unsave_theorem)
                    .patch(handlers::me_library::patch_saved),
            )
            .route(
                "/api/me/library/folders",
                post(handlers::me_library::create_folder)
                    .get(handlers::me_library::list_folders),
            )
            .route(
                "/api/me/library/folders/{id}",
                delete(handlers::me_library::delete_folder)
                    .patch(handlers::me_library::patch_folder),
            )
            .route(
                "/api/research/jobs",
                post(handlers::research_jobs::create)
                    .get(handlers::research_jobs::list),
            )
            .route(
                "/api/research/jobs/{id}",
                get(handlers::research_jobs::detail),
            )
            .route(
                "/api/research/jobs/{id}/events",
                get(handlers::research_jobs::events),
            )
            .route(
                "/api/research/jobs/{id}/cancel",
                post(handlers::research_jobs::cancel),
            )
            .route("/api/billing/me", get(handlers::billing::me))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                physics_api::billing::api_quota_layer::api_quota,
            ))
            .layer(GovernorLayer::new(rate_limit::platform_user()));

        // Platform-worker: worker registration + heartbeat + ingest. Bearer nsk_worker_.
        // /api/ingest does its own per-worker rate limiting via WorkerRateLimiter
        // (Phase 9 Task 4.2); the IP-based GovernorLayer here is harmless extra
        // backstop for spammy IPs.
        let platform_worker = Router::new()
            .route(
                "/api/workers/register",
                axum::routing::post(handlers::workers::register),
            )
            .route(
                "/api/workers/heartbeat",
                axum::routing::post(handlers::workers::heartbeat),
            )
            .route(
                "/api/ingest",
                axum::routing::post(handlers::ingest::ingest),
            )
            // Per-chunk per-cluster summaries pushed by workers; the
            // steerer reads recent rows for both UCB1 reward and the
            // LLM prompt's cluster_summaries field.
            .route(
                "/api/cluster-report",
                axum::routing::post(handlers::cluster_report::handler),
            )
            // Per-cluster directive bandit reward feedback. Workers
            // POST a batch of (arm_key, reward) tuples after they've
            // observed the cluster's mean-fitness delta one chunk
            // after the directive landed.
            .route(
                "/api/directive-feedback",
                axum::routing::post(handlers::directive_feedback::handler),
            )
            // Test-time-compute scaling bandit reward feedback.
            // Workers POST a batch of (island, strength_bucket,
            // multiplier_choice, reward) tuples after observing the
            // chunk's discoveries-per-pop.
            .route(
                "/api/compute-feedback",
                axum::routing::post(handlers::compute_feedback::handler),
            )
            // Phase E: conjecture worker endpoints (claim/heartbeat/submit/complete).
            // Each consumes from the same per-worker rate-limit bucket as /api/ingest.
            .route(
                "/api/conjecture/claim",
                axum::routing::post(handlers::conjecture::claim),
            )
            .route(
                "/api/conjecture/{id}/heartbeat",
                axum::routing::post(handlers::conjecture::heartbeat),
            )
            .route(
                "/api/conjecture/{id}/submit",
                axum::routing::post(handlers::conjecture::submit),
            )
            .route(
                "/api/conjecture/{id}/complete",
                axum::routing::post(handlers::conjecture::complete_handler),
            )
            // Paid-Researcher worker endpoints (Phase 4 of cluster-steerer
            // plan). Distinct from the legacy /api/conjecture/* claim path
            // because these run against the new {queued, claimed, running,
            // proved, budget_exhausted, cancelled} state machine.
            .route(
                "/api/jobs/claim",
                axum::routing::post(handlers::jobs_claim::claim),
            )
            .route(
                "/api/jobs/{id}/heartbeat",
                axum::routing::post(handlers::jobs_claim::heartbeat),
            )
            .route(
                "/api/jobs/{id}/release",
                axum::routing::post(handlers::jobs_claim::release),
            )
            .route(
                "/api/jobs/{id}/mark_proved",
                axum::routing::post(handlers::jobs_claim::mark_proved),
            )
            .layer(GovernorLayer::new(rate_limit::platform_worker()));

        // Stripe webhook — Stripe-authed (signature header), not user-authed.
        // Lives outside the auth_layer so it doesn't get a 401 from missing
        // session, and outside platform_user's IP rate-limit so a busy
        // webhook delivery isn't throttled.
        let billing_webhook = Router::new()
            .route("/api/billing/webhook", post(handlers::billing::webhook));

        // Impersonation layer: looks for X-Impersonate-Token, validates
        // it, and on a hit injects the target user's `AuthUser` into
        // request extensions. Downstream extractors (AuthOrApiKey, the
        // admin guard) read from extensions first. The middleware is a
        // no-op when no token is present, so it's safe to apply broadly.
        let with_imp = axum::middleware::from_fn_with_state(
            state.clone(),
            physics_api::impersonation::impersonation_layer,
        );

        app = app
            .merge(auth_strict)
            .merge(auth_session)
            .merge(platform_user_sensitive)
            .merge(platform_user)
            .merge(platform_worker)
            .layer(with_imp)
            .layer(session_layer)
            .merge(billing_webhook);

        tracing::info!("Auth endpoints enabled (PostgreSQL available)");
    } else {
        tracing::info!("Auth endpoints disabled (no PostgreSQL)");
    }

    // P-Task 7: response compression (gzip + brotli) negotiated via
    // Accept-Encoding. JSON payloads — `/api/seed` especially —
    // compress 12-15× with gzip. Caddy in front already gzips
    // outgoing bytes, but enabling at the origin means Cloudflare
    // also gets a compressed payload to cache, and SSE clients that
    // hit the origin directly via `origin.nasrudin.org` get
    // compression too.
    let app = app
        .layer(cors)
        .layer(CompressionLayer::new())
        .layer(TraceLayer::new_for_http())
        .with_state(state.clone());

    // Bind and serve with graceful shutdown.
    // PORT env override lets parallel dev/test servers coexist on one host.
    let port = std::env::var("PORT")
        .ok()
        .and_then(|s| s.parse::<u16>().ok())
        .unwrap_or(3001);
    let addr = format!("0.0.0.0:{port}");
    let tcp_listener = tokio::net::TcpListener::bind(&addr).await?;
    tracing::info!("Listening on {addr} (TCP)");

    // Unix-domain-socket listener (admin-panel trust-bypass entry point).
    // The co-located worker connects via `unix:///run/nasrudin/api-local.sock`
    // and is auto-trusted because Caddy never proxies to this socket.
    // `NASRUDIN_LOCAL_SOCK_PATH=` (empty string) disables the listener — useful
    // when running in a container that doesn't share /run with the worker.
    let sock_path_env = std::env::var("NASRUDIN_LOCAL_SOCK_PATH")
        .unwrap_or_else(|_| "/run/nasrudin/api-local.sock".to_string());
    let sock_path: Option<std::path::PathBuf> = if sock_path_env.is_empty() {
        None
    } else {
        Some(sock_path_env.into())
    };

    let uds_listener: Option<tokio::net::UnixListener> = match sock_path.as_ref() {
        None => {
            tracing::info!("Unix socket listener disabled (NASRUDIN_LOCAL_SOCK_PATH=\"\")");
            None
        }
        Some(p) => {
            if let Some(parent) = p.parent() {
                let _ = std::fs::create_dir_all(parent);
            }
            if p.exists() {
                let _ = std::fs::remove_file(p);
            }
            match tokio::net::UnixListener::bind(p) {
                Ok(l) => {
                    use std::os::unix::fs::PermissionsExt;
                    if let Ok(meta) = std::fs::metadata(p) {
                        let mut perms = meta.permissions();
                        perms.set_mode(0o660);
                        let _ = std::fs::set_permissions(p, perms);
                    }
                    tracing::info!(
                        "Listening on {} (UDS, mode 0660 — auto-trusted)",
                        p.display()
                    );
                    Some(l)
                }
                Err(e) => {
                    tracing::warn!(
                        "Could not bind unix socket at {}: {e}. Co-located worker auto-trust disabled.",
                        p.display()
                    );
                    None
                }
            }
        }
    };

    // Two app instances share routes + state but the UDS variant inserts
    // a `LocalSocket` extension marker so trust resolution can flip the
    // request into the bypass path.
    let tcp_app = app.clone();
    let uds_app = app.layer(axum::middleware::from_fn(
        |mut req: axum::extract::Request, next: axum::middleware::Next| async move {
            req.extensions_mut()
                .insert(physics_api::trust::LocalSocket);
            next.run(req).await
        },
    ));

    let shutdown_for_tcp = Arc::clone(&shutdown);
    let shutdown_for_uds = Arc::clone(&shutdown);
    let tcp_handle = tokio::spawn(async move {
        let _ = axum::serve(
            tcp_listener,
            tcp_app.into_make_service_with_connect_info::<SocketAddr>(),
        )
        .with_graceful_shutdown(async move {
            tokio::signal::ctrl_c().await.ok();
            tracing::info!("Received shutdown signal (TCP)");
            shutdown_for_tcp.store(true, Ordering::Relaxed);
        })
        .await;
    });

    let uds_handle = uds_listener.map(|listener| {
        tokio::spawn(async move {
            let _ = axum::serve(listener, uds_app.into_make_service())
                .with_graceful_shutdown(async move {
                    tokio::signal::ctrl_c().await.ok();
                    tracing::info!("Received shutdown signal (UDS)");
                    shutdown_for_uds.store(true, Ordering::Relaxed);
                })
                .await;
        })
    });

    let _ = tcp_handle.await;
    if let Some(h) = uds_handle {
        let _ = h.await;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Verification worker
// ---------------------------------------------------------------------------

/// Run verification workers that pull candidates from the GA engine,
/// attempt Lean4 verification, and return results.
///
/// Runs the blocking mpsc recv in a dedicated blocking thread.
async fn run_verification_workers(
    candidates_rx: std::sync::mpsc::Receiver<Vec<Theorem>>,
    verified_tx: std::sync::mpsc::Sender<Vec<Theorem>>,
    db: Arc<TheoremDb>,
    _discovery_tx: tokio::sync::broadcast::Sender<DiscoveryEvent>,
) {
    // Move the blocking receiver into a dedicated thread that forwards
    // batches via a tokio mpsc channel.
    let (async_tx, mut async_rx) = tokio::sync::mpsc::channel::<Vec<Theorem>>(32);

    tokio::task::spawn_blocking(move || {
        while let Ok(batch) = candidates_rx.recv() {
            if async_tx.blocking_send(batch).is_err() {
                break;
            }
        }
    });

    let lean_bridge = LeanBridge::new().unwrap_or_else(|e| {
        tracing::warn!("LeanBridge init failed ({e}), verification disabled");
        LeanBridge::default()
    });

    tracing::info!(
        "Verification worker started (lean bridge available: {})",
        lean_bridge.is_available()
    );

    while let Some(batch) = async_rx.recv().await {
        let mut verified_batch: Vec<Theorem> = Vec::new();

        for mut theorem in batch {
            // Check if already in DB
            if let Ok(true) = db.theorem_exists(&theorem.id) {
                continue;
            }

            // Attempt verification via ProcessVerifier (generates .lean → lake build)
            match lean_bridge.verify_theorem(&theorem) {
                Ok(nasrudin_lean_bridge::VerifyResult::Verified { proof_term }) => {
                    theorem.verified = VerificationStatus::Verified {
                        proof_term,
                        tactic_used: "lake_build".to_string(),
                    };
                    tracing::info!("Verified theorem {}", hex::encode(theorem.id));
                }
                Ok(nasrudin_lean_bridge::VerifyResult::Rejected { reason }) => {
                    theorem.verified = VerificationStatus::Rejected { reason };
                }
                Ok(nasrudin_lean_bridge::VerifyResult::Timeout) => {
                    theorem.verified = VerificationStatus::Rejected {
                        reason: "verification timed out".to_string(),
                    };
                }
                Ok(nasrudin_lean_bridge::VerifyResult::ParseError { message }) => {
                    theorem.verified = VerificationStatus::Rejected {
                        reason: format!("parse error: {message}"),
                    };
                }
                Ok(nasrudin_lean_bridge::VerifyResult::FfiError { message }) => {
                    // No backend available — store as pending
                    tracing::debug!("Lean verification unavailable: {message}");
                    theorem.verified = VerificationStatus::Pending;
                }
                Err(e) => {
                    tracing::debug!("Lean verification error: {e}");
                    theorem.verified = VerificationStatus::Pending;
                }
            }

            // Store in DB regardless of verification status
            if let Err(e) = db.put_theorem(&theorem) {
                tracing::error!("Failed to store theorem: {e}");
                continue;
            }

            verified_batch.push(theorem);
        }

        if !verified_batch.is_empty() && verified_tx.send(verified_batch).is_err() {
            tracing::info!("Verified channel closed, stopping worker");
            break;
        }
    }

    tracing::info!("Verification worker stopped");
}

// ---------------------------------------------------------------------------
// Handlers
// ---------------------------------------------------------------------------

/// Health check endpoint. Phase 9: includes db/rocks status, reverify queue depth,
/// and total theorem count for monitoring + the smoke-test contract.
async fn health(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let db = if state.pg.is_some() { "ok" } else { "down" };
    let queue_depth = state.db.reverify_queue_depth().unwrap_or(usize::MAX);
    let stats = state.db.get_stats().unwrap_or_default();
    Json(serde_json::json!({
        "status": "ok",
        "version": env!("CARGO_PKG_VERSION"),
        "db": db,
        "rocks": "ok",
        "queue_depth": queue_depth,
        "theorems_total": stats.total_theorems,
    }))
}

/// Engine statistics.
async fn stats(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    match state.db.get_stats() {
        Ok(stats) => Json(serde_json::to_value(stats).unwrap_or_default()),
        Err(e) => Json(serde_json::json!({
            "error": format!("Failed to get stats: {e}")
        })),
    }
}

/// GA engine status.
async fn ga_status_handler(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let snapshot = state.ga_status.lock().unwrap_or_else(|e| e.into_inner());
    Json(serde_json::to_value(&*snapshot).unwrap_or_default())
}

/// Parse a domain string (snake_case or PascalCase) into a `Domain`.
fn parse_domain(s: &str) -> Option<Domain> {
    match s.to_lowercase().replace('-', "_").as_str() {
        "pure_math" | "puremath" => Some(Domain::PureMath),
        "classical_mechanics" | "classicalmechanics" => Some(Domain::ClassicalMechanics),
        "electromagnetism" => Some(Domain::Electromagnetism),
        "special_relativity" | "specialrelativity" => Some(Domain::SpecialRelativity),
        "general_relativity" | "generalrelativity" => Some(Domain::GeneralRelativity),
        "quantum_mechanics" | "quantummechanics" => Some(Domain::QuantumMechanics),
        "quantum_field_theory" | "quantumfieldtheory" => Some(Domain::QuantumFieldTheory),
        "statistical_mechanics" | "statisticalmechanics" => Some(Domain::StatisticalMechanics),
        "thermodynamics" => Some(Domain::Thermodynamics),
        "optics" => Some(Domain::Optics),
        "fluid_dynamics" | "fluiddynamics" => Some(Domain::FluidDynamics),
        _ => None,
    }
}

/// Parse a hex-encoded theorem ID string into a `TheoremId`.
fn parse_theorem_id(hex_str: &str) -> Option<TheoremId> {
    let bytes = hex::decode(hex_str).ok()?;
    if bytes.len() == 8 {
        let mut arr = [0u8; 8];
        arr.copy_from_slice(&bytes);
        Some(arr)
    } else {
        None
    }
}

/// Get the lineage (parents + children) of a theorem.
async fn get_lineage(
    State(state): State<Arc<AppState>>,
    Path(id_hex): Path<String>,
) -> Json<serde_json::Value> {
    let id = match parse_theorem_id(&id_hex) {
        Some(id) => id,
        None => {
            return Json(serde_json::json!({
                "error": "Invalid theorem ID: expected 16-char hex string"
            }));
        }
    };

    match state.db.get_lineage(&id) {
        Ok(Some(lineage)) => Json(serde_json::to_value(lineage).unwrap_or_default()),
        Ok(None) => Json(serde_json::json!({ "error": "Lineage not found" })),
        Err(e) => Json(serde_json::json!({ "error": format!("{e}") })),
    }
}

/// Get the proof tree of a theorem.
async fn get_proof(
    State(state): State<Arc<AppState>>,
    Path(id_hex): Path<String>,
) -> Json<serde_json::Value> {
    let id = match parse_theorem_id(&id_hex) {
        Some(id) => id,
        None => {
            return Json(serde_json::json!({
                "error": "Invalid theorem ID: expected 16-char hex string"
            }));
        }
    };

    match state.db.get_proof(&id) {
        Ok(Some(proof)) => Json(serde_json::to_value(proof).unwrap_or_default()),
        Ok(None) => Json(serde_json::json!({ "error": "Proof not found" })),
        Err(e) => Json(serde_json::json!({ "error": format!("{e}") })),
    }
}

/// Delete a theorem by hex ID.
async fn delete_theorem_handler(
    State(state): State<Arc<AppState>>,
    Path(id_hex): Path<String>,
) -> Json<serde_json::Value> {
    let id = match parse_theorem_id(&id_hex) {
        Some(id) => id,
        None => {
            return Json(serde_json::json!({
                "error": "Invalid theorem ID: expected 16-char hex string"
            }));
        }
    };

    match state.db.delete_theorem(&id) {
        Ok(()) => Json(serde_json::json!({ "deleted": true, "id": id_hex })),
        Err(e) => Json(serde_json::json!({ "error": format!("{e}") })),
    }
}

/// List all domains with their theorem counts.
async fn list_domains(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    match state.db.count_by_domain() {
        Ok(counts) => Json(serde_json::to_value(counts).unwrap_or_default()),
        Err(e) => Json(serde_json::json!({ "error": format!("{e}") })),
    }
}

/// Query parameters for axiom listing.
#[derive(Debug, Deserialize)]
struct AxiomParams {
    domain: Option<String>,
}

/// List seed axioms.
///
/// **Cold-tier policy:** when `domain` is unset this returns the
/// hot tier only (~few thousand axioms). Listing the full
/// hot+cold (~195 k) would balloon the response and is rarely what
/// callers want — for cold-tier browsing pass an explicit `domain`,
/// which range-scans the secondary index. Capped at 5 000 entries
/// per response to keep the bandwidth bounded.
async fn list_axioms(
    State(state): State<Arc<AppState>>,
    Query(params): Query<AxiomParams>,
) -> Json<serde_json::Value> {
    let store = state.axiom_store.load();
    const LIST_AXIOMS_CAP: usize = 5_000;
    let axioms: Vec<serde_json::Value> = if let Some(ref domain_str) = params.domain {
        match parse_domain(domain_str) {
            Some(domain) => store
                .by_domain(&domain)
                .into_iter()
                .take(LIST_AXIOMS_CAP)
                .map(|a| {
                    serde_json::json!({
                        "name": a.name,
                        "domain": a.domain.to_string(),
                        "description": a.description,
                    })
                })
                .collect(),
            None => vec![],
        }
    } else {
        // Hot-tier-only path. Walking the cold tier here would mean
        // shipping ~195 k axioms in a single JSON payload — the
        // existing /api/seed handler caps at 5 k for a reason. If
        // the operator needs to enumerate the full corpus, pass
        // `?domain=pure_math` explicitly.
        store
            .iter_hot_names()
            .into_iter()
            .filter_map(|name| store.get(&name))
            .map(|a| {
                serde_json::json!({
                    "name": a.name,
                    "domain": a.domain.to_string(),
                    "description": a.description,
                })
            })
            .collect()
    };

    let total = axioms.len();
    Json(serde_json::json!({
        "axioms": axioms,
        "total": total,
    }))
}

// ---------------------------------------------------------------------------
// Response types
// ---------------------------------------------------------------------------

