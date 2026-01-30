//! Physics Generator HTTP API server.
//!
//! Full daemon: REST endpoints, SSE discovery stream, GA evolution thread,
//! and Lean4 verification workers.

mod auth;
mod rate_limit;

use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use axum::{
    Json, Router,
    extract::{Path, Query, State},
    http::{HeaderValue, Method},
    response::{
        Sse,
        sse::{Event, KeepAlive},
    },
    routing::get,
};
use axum_login::AuthManagerLayerBuilder;
use tower_sessions::{MemoryStore, SessionManagerLayer};
use serde::{Deserialize, Serialize};
use tokio_stream::StreamExt as _;
use tokio_stream::wrappers::BroadcastStream;
use tower_governor::GovernorLayer;
use tower_http::cors::CorsLayer;
use tower_http::trace::TraceLayer;
use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

use nasrudin_core::{Domain, Theorem, TheoremId, VerificationStatus};
use nasrudin_ga::{DiscoveryEvent, GaConfig, GaEngine};
use nasrudin_lean_bridge::LeanBridge;
use nasrudin_pg::sea_orm::DatabaseConnection;
use nasrudin_rocks::TheoremDb;

use axum::routing::delete;

/// Shared application state.
struct AppState {
    db: Arc<TheoremDb>,
    pg: DatabaseConnection,
    discovery_tx: tokio::sync::broadcast::Sender<DiscoveryEvent>,
    ga_status: Arc<std::sync::Mutex<GaStatusSnapshot>>,
}

/// A snapshot of GA engine status, updated periodically.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
struct GaStatusSnapshot {
    pub total_generations: u64,
    pub total_population: usize,
    pub num_islands: usize,
    pub candidates_sent: u64,
    pub verified_discoveries: u64,
    pub running: bool,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // Initialize tracing
    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with(tracing_subscriber::fmt::layer())
        .init();

    tracing::info!("Starting Physics Generator API server");

    // Load environment from .env in project root (parent of engine/)
    let env_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.env");
    match dotenvy::from_path(&env_path) {
        Ok(_) => tracing::info!("Loaded .env from {}", env_path.display()),
        Err(e) => tracing::warn!("No .env loaded ({}): using existing env vars", e),
    }

    // Connect to PostgreSQL and run migrations
    let database_url = std::env::var("DATABASE_URL")
        .expect("DATABASE_URL must be set (in .env or environment)");
    let pg = nasrudin_pg::connect_and_migrate(
        &nasrudin_pg::PgConfig::new(&database_url),
    )
    .await?;

    // Open RocksDB (use env var or default path)
    let db_path = std::env::var("ROCKS_DB_PATH").unwrap_or_else(|_| "./data/theorems.db".into());
    let db = Arc::new(TheoremDb::new(&db_path)?);
    tracing::info!("RocksDB opened at {db_path}");

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
    let ga_discovery_tx = discovery_tx.clone();
    let ga_shutdown = Arc::clone(&shutdown);
    let ga_status_ref = Arc::clone(&ga_status);

    std::thread::Builder::new()
        .name("ga-engine".into())
        .spawn(move || {
            let engine = GaEngine::new(ga_config, ga_db);

            // Capture initial status
            {
                let status = engine.status();
                if let Ok(mut snapshot) = ga_status_ref.lock() {
                    snapshot.total_generations = status.total_generations;
                    snapshot.total_population = status.total_population;
                    snapshot.num_islands = status.num_islands;
                    snapshot.candidates_sent = status.candidates_sent;
                    snapshot.verified_discoveries = status.verified_discoveries;
                    snapshot.running = true;
                }
            }

            engine.run(candidates_tx, verified_rx, ga_discovery_tx, ga_shutdown);

            if let Ok(mut snapshot) = ga_status_ref.lock() {
                snapshot.running = false;
            }
        })?;

    // Spawn verification workers (process candidates via Lean4)
    let verify_db = Arc::clone(&db);
    let verify_discovery_tx = discovery_tx.clone();
    tokio::spawn(async move {
        run_verification_workers(candidates_rx, verified_tx, verify_db, verify_discovery_tx).await;
    });

    let state = Arc::new(AppState {
        db,
        pg,
        discovery_tx,
        ga_status,
    });

    // Session store (in-memory; swap to SQL/Redis store for persistence)
    let session_store = MemoryStore::default();
    let session_layer = SessionManagerLayer::new(session_store)
        .with_secure(false); // TODO: set true behind TLS in production

    // Auth layer
    let auth_backend = auth::Backend::new(state.pg.clone());
    let auth_layer = AuthManagerLayerBuilder::new(auth_backend, session_layer).build();

    // CORS configuration
    let cors = CorsLayer::new()
        .allow_origin("http://localhost:3000".parse::<HeaderValue>()?)
        .allow_methods([Method::GET, Method::POST, Method::DELETE, Method::OPTIONS])
        .allow_headers(tower_http::cors::Any)
        .allow_credentials(true);

    // Build grouped sub-routers with per-group rate limits.
    // Each group gets its own GovernorLayer (GCRA, per-IP keying).

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

    // API-standard: core read API (60 req/min, burst 20)
    let api = Router::new()
        .route("/api/ga/status", get(ga_status_handler))
        .route("/api/theorems/recent", get(recent_theorems))
        .route("/api/theorems/{id}", get(get_theorem))
        .route("/api/theorems/{id}", delete(delete_theorem_handler))
        .route("/api/theorems/{id}/lineage", get(get_lineage))
        .route("/api/theorems/{id}/proof", get(get_proof))
        .route("/api/theorems", get(search_theorems))
        .route("/api/domains", get(list_domains))
        .layer(GovernorLayer::new(rate_limit::api_standard()));

    // Health-relaxed: monitoring & liveness (120 req/min, burst 30)
    let health = Router::new()
        .route("/api/health", get(self::health))
        .route("/api/stats", get(stats))
        .layer(GovernorLayer::new(rate_limit::health_relaxed()));

    // SSE: no rate limit (long-lived connection)
    let sse = Router::new()
        .route("/api/events/discoveries", get(discovery_stream));

    let app = Router::new()
        .merge(auth_strict)
        .merge(auth_session)
        .merge(api)
        .merge(health)
        .merge(sse)
        .layer(cors)
        .layer(TraceLayer::new_for_http())
        .layer(auth_layer)
        .with_state(state.clone());

    // Bind and serve with graceful shutdown
    let addr = "0.0.0.0:3001";
    tracing::info!("Listening on {addr}");
    let listener = tokio::net::TcpListener::bind(addr).await?;

    let shutdown_flag = Arc::clone(&shutdown);
    axum::serve(listener, app.into_make_service_with_connect_info::<SocketAddr>())
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

    let lean_bridge = LeanBridge::default();
    let prover_root = std::env::var("PROVER_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| std::path::PathBuf::from("../prover"));

    tracing::info!("Verification worker started (prover root: {})", prover_root.display());

    while let Some(batch) = async_rx.recv().await {
        let mut verified_batch: Vec<Theorem> = Vec::new();

        for mut theorem in batch {
            // Check if already in DB
            if let Ok(true) = db.theorem_exists(&theorem.id) {
                continue;
            }

            // Attempt verification via lake build
            let module_name = format!("GA_{}", hex::encode(theorem.id));
            match lean_bridge.verify_via_lake(&prover_root, &module_name) {
                Ok(true) => {
                    theorem.verified = VerificationStatus::Verified {
                        proof_term: vec![],
                        tactic_used: "lake_build".to_string(),
                    };
                    tracing::info!("Verified theorem {}", hex::encode(theorem.id));
                }
                Ok(false) => {
                    theorem.verified = VerificationStatus::Rejected {
                        reason: "lake build failed".to_string(),
                    };
                }
                Err(e) => {
                    // Lean not available — store as pending
                    tracing::debug!("Lean verification unavailable: {e}");
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

        if !verified_batch.is_empty() {
            if verified_tx.send(verified_batch).is_err() {
                tracing::info!("Verified channel closed, stopping worker");
                break;
            }
        }
    }

    tracing::info!("Verification worker stopped");
}

// ---------------------------------------------------------------------------
// Handlers
// ---------------------------------------------------------------------------

/// Health check endpoint.
async fn health() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "ok".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
    })
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

/// Get a theorem by hex ID.
async fn get_theorem(
    State(state): State<Arc<AppState>>,
    Path(id_hex): Path<String>,
) -> Json<serde_json::Value> {
    let id_bytes = match parse_theorem_id(&id_hex) {
        Some(id) => id,
        None => {
            return Json(serde_json::json!({
                "error": "Invalid theorem ID: expected 16-char hex string"
            }));
        }
    };

    match state.db.get_theorem(&id_bytes) {
        Ok(Some(thm)) => Json(serde_json::to_value(thm).unwrap_or_default()),
        Ok(None) => Json(serde_json::json!({ "error": "Theorem not found" })),
        Err(e) => Json(serde_json::json!({ "error": format!("{e}") })),
    }
}

/// Query parameters for theorem search.
#[derive(Debug, Deserialize)]
struct SearchParams {
    domain: Option<String>,
    depth: Option<u32>,
    generation: Option<u64>,
    latex: Option<String>,
    axiom: Option<String>,
    verified: Option<bool>,
    limit: Option<usize>,
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

/// Search theorems with optional filters using indexed queries.
async fn search_theorems(
    State(state): State<Arc<AppState>>,
    Query(params): Query<SearchParams>,
) -> Json<serde_json::Value> {
    let limit = params.limit.unwrap_or(50).min(200);

    // Helper: resolve a list of TheoremIds into Theorems
    let resolve_ids = |ids: Vec<TheoremId>| -> Vec<Theorem> {
        ids.iter()
            .filter_map(|id| state.db.get_theorem(id).ok().flatten())
            .collect()
    };

    // Use indexed queries with limit pushed down to the storage layer
    let result: anyhow::Result<Vec<Theorem>> = (|| {
        if let Some(ref domain_str) = params.domain {
            return match parse_domain(domain_str) {
                Some(domain) => {
                    let ids = state.db.list_by_domain_limit(&domain, limit)?;
                    Ok(resolve_ids(ids))
                }
                None => Ok(vec![]),
            };
        }
        if let Some(depth) = params.depth {
            let ids = state.db.list_by_depth_limit(depth, limit)?;
            return Ok(resolve_ids(ids));
        }
        if let Some(generation) = params.generation {
            let ids = state.db.list_by_generation_limit(generation, limit)?;
            return Ok(resolve_ids(ids));
        }
        if let Some(ref prefix) = params.latex {
            let ids = state.db.search_latex_limit(prefix, limit)?;
            return Ok(resolve_ids(ids));
        }
        if let Some(ref axiom_hex) = params.axiom {
            return match parse_theorem_id(axiom_hex) {
                Some(axiom_id) => {
                    let ids = state.db.list_by_axiom_limit(&axiom_id, limit)?;
                    Ok(resolve_ids(ids))
                }
                None => Ok(vec![]),
            };
        }
        // Fallback: recent theorems (avoids full table scan at scale)
        state.db.list_recent(limit)
    })();

    match result {
        Ok(mut theorems) => {
            // Apply verified filter as a post-filter (works across all index paths)
            if let Some(verified) = params.verified {
                theorems.retain(|thm| {
                    let is_verified = matches!(thm.verified, VerificationStatus::Verified { .. });
                    is_verified == verified
                });
            }

            let total = theorems.len();
            Json(serde_json::json!({
                "theorems": theorems,
                "total": total,
            }))
        }
        Err(e) => Json(serde_json::json!({
            "error": format!("Search failed: {e}"),
            "theorems": [],
            "total": 0,
        })),
    }
}

/// Get recently created theorems.
async fn recent_theorems(
    State(state): State<Arc<AppState>>,
    Query(params): Query<SearchParams>,
) -> Json<serde_json::Value> {
    let limit = params.limit.unwrap_or(20).min(200);
    match state.db.list_recent(limit) {
        Ok(theorems) => {
            let total = theorems.len();
            Json(serde_json::json!({
                "theorems": theorems,
                "total": total,
            }))
        }
        Err(e) => Json(serde_json::json!({
            "error": format!("Failed to get recent theorems: {e}"),
        })),
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
async fn list_domains(
    State(state): State<Arc<AppState>>,
) -> Json<serde_json::Value> {
    match state.db.count_by_domain() {
        Ok(counts) => Json(serde_json::to_value(counts).unwrap_or_default()),
        Err(e) => Json(serde_json::json!({ "error": format!("{e}") })),
    }
}


/// Server-Sent Events stream for live discovery notifications.
async fn discovery_stream(
    State(state): State<Arc<AppState>>,
) -> Sse<impl tokio_stream::Stream<Item = Result<Event, std::convert::Infallible>>> {
    let rx = state.discovery_tx.subscribe();
    let stream = BroadcastStream::new(rx).filter_map(|result| match result {
        Ok(event) => {
            let data = serde_json::to_string(&event).unwrap_or_default();
            Some(Ok(Event::default().event("discovery").data(data)))
        }
        Err(_) => None,
    });

    Sse::new(stream).keep_alive(KeepAlive::default())
}

// ---------------------------------------------------------------------------
// Response types
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
struct HealthResponse {
    status: String,
    version: String,
}
