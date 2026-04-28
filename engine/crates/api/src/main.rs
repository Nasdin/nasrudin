//! Physics Generator HTTP API server.
//!
//! Full daemon: REST endpoints, SSE discovery stream, GA evolution thread,
//! and Lean4 verification workers.

use physics_api::{auth, handlers, rate_limit, state::AppState};

use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use axum::{
    Json, Router,
    extract::{Path, Query, State},
    http::{HeaderValue, Method},
    routing::get,
};
use axum_login::AuthManagerLayerBuilder;
use serde::Deserialize;
use tower_governor::GovernorLayer;
use tower_http::cors::CorsLayer;
use tower_http::trace::TraceLayer;
use tower_sessions::{MemoryStore, SessionManagerLayer};
use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

use nasrudin_core::{Domain, Theorem, TheoremId, VerificationStatus};
use nasrudin_derive::AxiomStore;
use nasrudin_ga::{DiscoveryEvent, GaConfig, GaEngine, GaStatusSnapshot};
use nasrudin_lean_bridge::LeanBridge;
use nasrudin_rocks::TheoremDb;

use axum::routing::delete;

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

    // Load PhysLean axioms from catalog
    let mut axiom_store = AxiomStore::new();
    let prover_root = std::env::var("PROVER_ROOT").unwrap_or_else(|_| "../prover".into());
    let catalog_path =
        std::path::Path::new(&prover_root).join("../physlean-extract/output/catalog.json");
    match axiom_store.load_from_catalog(&catalog_path) {
        Ok(count) => tracing::info!("Loaded {count} axioms from {}", catalog_path.display()),
        Err(e) => tracing::warn!(
            "Failed to load catalog ({}): GA will seed with random only",
            e
        ),
    }
    let axiom_store = Arc::new(axiom_store);

    // Channels
    let (candidates_tx, candidates_rx) = std::sync::mpsc::channel::<Vec<Theorem>>();
    let (verified_tx, verified_rx) = std::sync::mpsc::channel::<Vec<Theorem>>();
    let (discovery_tx, _discovery_rx) = tokio::sync::broadcast::channel::<DiscoveryEvent>(256);

    // Shutdown signal
    let shutdown = Arc::new(AtomicBool::new(false));

    // GA status snapshot (updated by GA thread)
    let ga_status = Arc::new(std::sync::Mutex::new(GaStatusSnapshot {
        running: true,
        ..Default::default()
    }));

    // Spawn GA thread (CPU-bound, std::thread)
    let ga_config = GaConfig::default();
    let ga_db = Arc::clone(&db);
    let ga_axiom_store = (*axiom_store).clone();
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

    // Spawn verification workers (process candidates via Lean4)
    let verify_db = Arc::clone(&db);
    let verify_discovery_tx = discovery_tx.clone();
    tokio::spawn(async move {
        run_verification_workers(candidates_rx, verified_tx, verify_db, verify_discovery_tx).await;
    });

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

    let (reverify_event_tx, _reverify_event_rx) =
        tokio::sync::broadcast::channel::<physics_api::reverify::DiscoveryEvent>(256);

    let reverify = pg.as_ref().map(|pg_conn| {
        Arc::new(physics_api::reverify::ReverifyQueue {
            rocks: Arc::clone(&db),
            pg: pg_conn.clone(),
            lake: Arc::clone(&lake),
            axiom_store: Arc::clone(&axiom_store),
            discovery_tx: reverify_event_tx.clone(),
        })
    });

    // Phase 9 Task 4.1: per-worker token-bucket limiter (60 req/min default).
    let worker_rate_limiter = Arc::new(physics_api::rate_limit::WorkerRateLimiter::new(60));

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
    });

    // Phase 9 Task 3.4: spawn the reverify drain loop iff Postgres is wired.
    if let Some(ref reverify) = state.reverify {
        tokio::spawn(Arc::clone(reverify).drain_loop());
        tracing::info!("Reverify drain loop spawned");
    } else {
        tracing::info!("Reverify drain loop disabled (no PostgreSQL)");
    }

    // CORS configuration
    let cors = CorsLayer::new()
        .allow_origin("http://localhost:3000".parse::<HeaderValue>()?)
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
        .route(
            "/api/theorems/{hash}/lean",
            get(handlers::theorems::lean_download),
        )
        .route("/api/theorems/recent", get(handlers::theorems::recent))
        .route("/api/theorems/{id}/lineage", get(get_lineage))
        .route("/api/theorems/{id}/proof", get(get_proof))
        .route("/api/theorems/{id}", get(handlers::theorems::by_id))
        .route("/api/theorems/{id}", delete(delete_theorem_handler))
        .route("/api/theorems", get(handlers::theorems::list))
        .route("/api/domains", get(list_domains))
        .route("/api/axioms", get(list_axioms))
        .route("/api/seed", get(handlers::seed::seed))
        .layer(GovernorLayer::new(rate_limit::api_standard()));

    // Health-relaxed: monitoring & liveness (120 req/min, burst 30)
    let health = Router::new()
        .route("/api/health", get(self::health))
        .route("/api/stats", get(stats))
        .layer(GovernorLayer::new(rate_limit::health_relaxed()));

    // SSE: no rate limit (long-lived connection)
    let sse = Router::new()
        .route(
            "/api/events/discoveries",
            get(handlers::events::discoveries),
        )
        .route("/api/events/stats", get(handlers::events::stats));

    // Public workers list — readable without auth (returns [] if PG unavailable).
    let workers_public = Router::new()
        .route("/api/workers", get(handlers::workers::list))
        .layer(GovernorLayer::new(rate_limit::api_standard()));

    // Start with core routes
    let mut app = Router::new()
        .merge(api)
        .merge(health)
        .merge(sse)
        .merge(workers_public);

    // Add auth routes only if PostgreSQL is available
    if let Some(ref pg_conn) = state.pg {
        let session_store = MemoryStore::default();
        let session_layer = SessionManagerLayer::new(session_store).with_secure(false); // TODO: set true behind TLS in production

        let auth_backend = auth::Backend::new(pg_conn.clone());
        let auth_layer = AuthManagerLayerBuilder::new(auth_backend, session_layer).build();

        // Auth-strict: brute-force protection (5 req/min, burst 5)
        let auth_strict = Router::new()
            .route("/api/auth/register", axum::routing::post(auth::register))
            .route("/api/auth/login", axum::routing::post(auth::login))
            .layer(GovernorLayer::new(rate_limit::auth_strict()));

        // Auth-session: lightweight session ops (30 req/min, burst 10)
        let auth_session = Router::new()
            .route("/api/auth/logout", axum::routing::post(auth::logout))
            .route("/api/auth/me", get(auth::me))
            .layer(GovernorLayer::new(rate_limit::auth_session()));

        // Platform-user: authenticated user CRUD on api keys, saved searches,
        // preferences, and per-user stats. Cookie or Bearer nsk_live_ tokens.
        let platform_user = Router::new()
            .route(
                "/api/api-keys",
                axum::routing::post(handlers::api_keys::create),
            )
            .route("/api/api-keys", get(handlers::api_keys::list))
            .route("/api/api-keys/{id}", delete(handlers::api_keys::revoke))
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
            .route(
                "/api/preferences",
                axum::routing::patch(handlers::preferences::patch),
            )
            .route("/api/me/stats", get(handlers::me::stats))
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
            .layer(GovernorLayer::new(rate_limit::platform_worker()));

        app = app
            .merge(auth_strict)
            .merge(auth_session)
            .merge(platform_user)
            .merge(platform_worker)
            .layer(auth_layer);

        tracing::info!("Auth endpoints enabled (PostgreSQL available)");
    } else {
        tracing::info!("Auth endpoints disabled (no PostgreSQL)");
    }

    let app = app
        .layer(cors)
        .layer(TraceLayer::new_for_http())
        .with_state(state.clone());

    // Bind and serve with graceful shutdown
    let addr = "0.0.0.0:3001";
    tracing::info!("Listening on {addr}");
    let listener = tokio::net::TcpListener::bind(addr).await?;

    let shutdown_flag = Arc::clone(&shutdown);
    axum::serve(
        listener,
        app.into_make_service_with_connect_info::<SocketAddr>(),
    )
    .with_graceful_shutdown(async move {
        tokio::signal::ctrl_c()
            .await
            .expect("Failed to listen for ctrl+c");
        tracing::info!("Received shutdown signal, stopping...");
        shutdown_flag.store(true, Ordering::Relaxed);
    })
    .await?;

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

/// List seed axioms loaded from the PhysLean catalog.
async fn list_axioms(
    State(state): State<Arc<AppState>>,
    Query(params): Query<AxiomParams>,
) -> Json<serde_json::Value> {
    let axioms: Vec<serde_json::Value> = if let Some(ref domain_str) = params.domain {
        match parse_domain(domain_str) {
            Some(domain) => state
                .axiom_store
                .by_domain(&domain)
                .into_iter()
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
        state
            .axiom_store
            .names()
            .into_iter()
            .filter_map(|name| state.axiom_store.get(name))
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

