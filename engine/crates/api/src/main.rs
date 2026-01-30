//! Physics Generator HTTP API server.
//!
//! Provides REST endpoints for theorem browsing, search, user auth,
//! and a Server-Sent Events stream for live discovery notifications.

use std::sync::Arc;
use std::time::Duration;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::{HeaderValue, Method},
    response::{
        Sse,
        sse::{Event, KeepAlive},
    },
    routing::get,
};
use serde::{Deserialize, Serialize};
use tokio_stream::StreamExt as _;
use tower_http::cors::CorsLayer;
use tower_http::trace::TraceLayer;
use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

use physics_rocks::TheoremDb;

/// Shared application state.
struct AppState {
    db: TheoremDb,
    // pg will be added when PostgreSQL is connected:
    // pg: sea_orm::DatabaseConnection,
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
    let db = TheoremDb::new(&db_path)?;
    tracing::info!("RocksDB opened at {db_path}");

    let state = Arc::new(AppState { db });

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
        .with_state(state);

    // Bind and serve
    let addr = "0.0.0.0:3001";
    tracing::info!("Listening on {addr}");
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    Ok(())
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

/// Search theorems (stub).
async fn search_theorems() -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "theorems": [],
        "total": 0,
        "note": "Search not yet implemented"
    }))
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
async fn discovery_stream() -> Sse<impl tokio_stream::Stream<Item = Result<Event, std::convert::Infallible>>>
{
    let stream = tokio_stream::wrappers::IntervalStream::new(tokio::time::interval(
        Duration::from_secs(5),
    ))
    .map(|_| {
        Ok(Event::default()
            .event("ping")
            .data(r#"{"type":"ping","timestamp":""}"#))
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
