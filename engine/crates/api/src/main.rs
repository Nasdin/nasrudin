//! Physics Generator HTTP API server.
//!
//! Full daemon: REST endpoints, SSE discovery stream, GA evolution thread,
//! and Lean4 verification workers.

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
use serde::{Deserialize, Serialize};
use tokio_stream::StreamExt as _;
use tokio_stream::wrappers::BroadcastStream;
use tower_http::cors::CorsLayer;
use tower_http::trace::TraceLayer;
use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

use nasrudin_core::{Theorem, VerificationStatus};
use nasrudin_ga::{DiscoveryEvent, GaConfig, GaEngine};
use nasrudin_lean_bridge::LeanBridge;
use nasrudin_rocks::TheoremDb;

/// Shared application state.
struct AppState {
    db: Arc<TheoremDb>,
    discovery_tx: tokio::sync::broadcast::Sender<DiscoveryEvent>,
    ga_status: Arc<std::sync::Mutex<GaStatusSnapshot>>,
    // pg will be added when PostgreSQL is connected:
    // pg: sea_orm::DatabaseConnection,
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
        discovery_tx,
        ga_status,
    });

    // CORS configuration
    let cors = CorsLayer::new()
        .allow_origin("http://localhost:3000".parse::<HeaderValue>()?)
        .allow_methods([Method::GET, Method::POST, Method::OPTIONS])
        .allow_headers(tower_http::cors::Any);

    // Build router
    let app = Router::new()
        // Health & stats
        .route("/api/health", get(health))
        .route("/api/stats", get(stats))
        // GA status
        .route("/api/ga/status", get(ga_status_handler))
        // Theorems
        .route("/api/theorems/{id}", get(get_theorem))
        .route("/api/theorems", get(search_theorems))
        // Auth (stubs)
        .route("/api/auth/register", axum::routing::post(register))
        .route("/api/auth/login", axum::routing::post(login))
        // SSE stream
        .route("/api/events/discoveries", get(discovery_stream))
        // Middleware
        .layer(cors)
        .layer(TraceLayer::new_for_http())
        .with_state(state.clone());

    // Bind and serve with graceful shutdown
    let addr = "0.0.0.0:3001";
    tracing::info!("Listening on {addr}");
    let listener = tokio::net::TcpListener::bind(addr).await?;

    let shutdown_flag = Arc::clone(&shutdown);
    axum::serve(listener, app)
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
    let id_bytes = match hex::decode(&id_hex) {
        Ok(b) if b.len() == 8 => {
            let mut arr = [0u8; 8];
            arr.copy_from_slice(&b);
            arr
        }
        _ => {
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
    verified: Option<bool>,
    limit: Option<usize>,
}

/// Search theorems with optional filters.
async fn search_theorems(
    State(state): State<Arc<AppState>>,
    Query(params): Query<SearchParams>,
) -> Json<serde_json::Value> {
    let limit = params.limit.unwrap_or(50).min(200);

    match state.db.list_theorems() {
        Ok(all) => {
            let filtered: Vec<_> = all
                .into_iter()
                .filter(|thm| {
                    // Domain filter
                    if let Some(ref domain) = params.domain {
                        let thm_domain = format!("{:?}", thm.domain);
                        if !thm_domain.eq_ignore_ascii_case(domain) {
                            return false;
                        }
                    }
                    // Verified filter
                    if let Some(verified) = params.verified {
                        let is_verified =
                            matches!(thm.verified, VerificationStatus::Verified { .. });
                        if is_verified != verified {
                            return false;
                        }
                    }
                    true
                })
                .take(limit)
                .collect();

            let total = filtered.len();
            Json(serde_json::json!({
                "theorems": filtered,
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

/// Register a new user (stub).
async fn register(Json(_body): Json<serde_json::Value>) -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "error": "Registration not yet implemented"
    }))
}

/// Login (stub).
async fn login(Json(_body): Json<serde_json::Value>) -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "error": "Login not yet implemented"
    }))
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
