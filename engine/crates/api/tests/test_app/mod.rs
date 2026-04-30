//! Shared integration-test harness for `physics-api` HTTP handlers.
//!
//! `build()` returns a fully-wired `Router` and the `AppState` it carries,
//! plus the live PostgreSQL test connection. It does *not* spawn the GA
//! engine, the verification workers, or the reverify drain loop — those are
//! orthogonal to the HTTP-level tests that consume this harness.
//!
//! All write operations to PostgreSQL go through the same migration path as
//! production. The harness DROPs and recreates the schema on each `build()`
//! call so tests can assume a clean database; tests in different files share
//! the database serialised by `TEST_LOCK`.
//!
//! `build()` returns `None` (gracefully) when the test database can't be
//! reached — this keeps `cargo test` working on machines without the dev
//! compose stack running. CI and the dev box should still set
//! `TEST_DATABASE_URL` so the suite actually runs.

#![allow(dead_code)] // Helpers used selectively by individual test files.

use std::sync::Arc;

use axum::Router;
use axum::body::{Body, to_bytes};
use axum::http::{Request, StatusCode};
use axum_login::AuthManagerLayerBuilder;
use sea_orm::{ConnectionTrait, DatabaseConnection};
use tempfile::TempDir;
use tokio::sync::Mutex;
use tower::util::ServiceExt;
use tower_sessions::{MemoryStore, SessionManagerLayer};

use nasrudin_derive::AxiomStore;
use nasrudin_ga::{DiscoveryEvent as GaDiscoveryEvent, GaStatusSnapshot};
use nasrudin_pg::{connect_simple, query::theorems as theorem_q, run_migrations};
use nasrudin_rocks::TheoremDb;

use physics_api::auth as api_auth;
use physics_api::handlers;
use physics_api::lake_builder::LakeBuilder;
use physics_api::rate_limit::WorkerRateLimiter;
use physics_api::reverify::DiscoveryEvent as ReverifyDiscoveryEvent;
use physics_api::state::AppState;

/// Process-wide async lock serialising tests that share the test database.
/// PostgreSQL DDL (CREATE/DROP TABLE) serialises globally on
/// `pg_type_typname_nsp_index`, so concurrent migrations race; this lock
/// prevents that.
pub static TEST_LOCK: Mutex<()> = Mutex::const_new(());

const RESET_SQL: &str = "DROP TABLE IF EXISTS user_saved_theorems CASCADE; \
     DROP TABLE IF EXISTS library_folders CASCADE; \
     DROP TABLE IF EXISTS cluster_steering CASCADE; \
     DROP TABLE IF EXISTS conjecture_events CASCADE; \
     DROP TABLE IF EXISTS conjecture_jobs CASCADE; \
     DROP TABLE IF EXISTS manual_verifications CASCADE; \
     DROP TABLE IF EXISTS targeted_search_usage CASCADE; \
     DROP TABLE IF EXISTS api_usage_daily CASCADE; \
     DROP TABLE IF EXISTS billing_events CASCADE; \
     DROP TABLE IF EXISTS user_llm_keys CASCADE; \
     DROP TABLE IF EXISTS theorems CASCADE; \
     DROP TABLE IF EXISTS workers CASCADE; \
     DROP TABLE IF EXISTS api_keys CASCADE; \
     DROP TABLE IF EXISTS sessions CASCADE; \
     DROP TABLE IF EXISTS user_preferences CASCADE; \
     DROP TABLE IF EXISTS saved_searches CASCADE; \
     DROP TABLE IF EXISTS users CASCADE; \
     DROP TABLE IF EXISTS seaql_migrations CASCADE;";

fn test_db_url() -> String {
    std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    })
}

/// A fully-wired test app. Holds the `Router` plus the resources (PG conn,
/// tempdir, lock guard) that must outlive every request.
pub struct TestApp {
    pub router: Router,
    pub pg: DatabaseConnection,
    /// Reverify-side broadcast handle, exposed so SSE tests can publish
    /// `theorem_*` events and verify they round-trip through the stream.
    pub reverify_event_tx: tokio::sync::broadcast::Sender<ReverifyDiscoveryEvent>,
    /// Direct handle to the AppState the router holds. Used by tests
    /// that need to mutate state directly (e.g. the LLM steering e2e
    /// test invokes run_one_cycle which needs &Arc<AppState>) and
    /// then read back through the same router.
    pub state: Arc<AppState>,
    /// Holding the guard for the test's lifetime serialises against other
    /// tests that share the database.
    _guard: tokio::sync::MutexGuard<'static, ()>,
    /// Tempdir backing the in-memory RocksDB; dropped at end of test.
    _rocks_dir: TempDir,
}

impl TestApp {
    /// Convenience: clone the AppState handle (cheap — `Arc<AppState>`).
    pub fn state(&self) -> Arc<AppState> {
        Arc::clone(&self.state)
    }
}

/// Response captured from the test router. Body is fully buffered.
pub struct Resp {
    pub status: StatusCode,
    pub body: Vec<u8>,
}

/// Per-test overrides for the harness. Defaults match `build()`.
#[derive(Default)]
pub struct BuildOpts {
    pub firebase_project_id: Option<String>,
    pub firebase_jwks: Option<std::sync::Arc<physics_api::firebase_auth::JwksCache>>,
}

/// Convenience for tests that need to inject a known JWKs key set.
pub async fn build_with_jwks(
    project_id: &str,
    jwks: std::collections::HashMap<String, jsonwebtoken::DecodingKey>,
) -> Option<TestApp> {
    build_with_opts(BuildOpts {
        firebase_project_id: Some(project_id.into()),
        firebase_jwks: Some(std::sync::Arc::new(
            physics_api::firebase_auth::JwksCache::for_test(jwks),
        )),
    })
    .await
}

/// Build a router with just the four Phase-9 theorem read endpoints wired.
///
/// Returns `None` if the test database can't be reached — callers should
/// `let Some(app) = build().await else { return };` to skip gracefully.
pub async fn build() -> Option<TestApp> {
    build_with_opts(BuildOpts::default()).await
}

/// Like `build()` but with per-test overrides for Firebase config / JWKs.
pub async fn build_with_opts(opts: BuildOpts) -> Option<TestApp> {
    let guard = TEST_LOCK.lock().await;

    let pg = match connect_simple(&test_db_url()).await {
        Ok(p) => p,
        Err(_) => return None,
    };
    pg.execute_unprepared(RESET_SQL).await.ok()?;
    run_migrations(&pg).await.ok()?;

    // Seed a known worker row so the public list endpoint has something to
    // return and so tests asserting "id_mismatch" on heartbeat have a real
    // counter-party in PG.
    nasrudin_pg::query::workers::register(&pg, "test-worker", Some("test-worker"), Some("localhost"))
        .await
        .ok()?;

    let rocks_dir = tempfile::tempdir().ok()?;
    let rocks = Arc::new(TheoremDb::new(rocks_dir.path().to_str()?).ok()?);

    let (ga_discovery_tx, _) = tokio::sync::broadcast::channel::<GaDiscoveryEvent>(16);
    let (reverify_event_tx, _) = tokio::sync::broadcast::channel::<ReverifyDiscoveryEvent>(16);
    let reverify_event_tx_for_test = reverify_event_tx.clone();
    let (conjecture_event_tx, _) = tokio::sync::broadcast::channel::<
        physics_api::conjecture::ConjectureEvent,
    >(16);

    let lake = Arc::new(LakeBuilder::new(
        std::env::temp_dir(),
        std::env::temp_dir(),
        1,
    ));
    let axiom_store = physics_api::state::SharedAxiomStore::new(AxiomStore::new());

    let initial_steering = physics_api::steerer::schema::default_config();
    let initial_body = serde_json::to_vec(&initial_steering).unwrap_or_default();
    let initial_etag = xxhash_rust::xxh64::xxh64(&initial_body, 0);
    let initial_snapshot = physics_api::state::SteeringSnapshot {
        config: serde_json::to_value(&initial_steering)
            .unwrap_or(serde_json::Value::Null),
        etag: initial_etag,
        started_at: chrono::Utc::now(),
    };

    let state = Arc::new(AppState {
        db: rocks,
        pg: Some(pg.clone()),
        axiom_store,
        discovery_tx: ga_discovery_tx,
        ga_status: Arc::new(std::sync::Mutex::new(GaStatusSnapshot::default())),
        lake,
        reverify_event_tx,
        reverify: None,
        worker_rate_limiter: Arc::new(WorkerRateLimiter::new(60)),
        admin_token: None,
        cache_ctx: None,
        embed: None,
        embedder: None,
        embed_path: None,
        llm_encrypt_key: Some([7u8; 32]),
        conjecture_event_tx,
        lake_promotion: None,
        billing: None,
        seed_cache: Arc::new(std::sync::Mutex::new(
            std::collections::HashMap::new(),
        )),
        steering: Arc::new(arc_swap::ArcSwap::from_pointee(initial_snapshot)),
        cluster_config: Arc::new(arc_swap::ArcSwap::from_pointee(
            physics_api::state::ClusterConfigSnapshot::default(),
        )),
        capacity: Arc::new(physics_api::jobs::capacity::CapacityTracker::new()),
        job_events: Arc::new(dashmap::DashMap::new()),
        landing_stats: Arc::new(physics_api::handlers::stats::LandingStatsCache::new()),
        firebase_project_id: opts
            .firebase_project_id
            .or_else(|| Some("test-project".into())),
        firebase_jwks: opts
            .firebase_jwks
            .unwrap_or_else(|| Arc::new(physics_api::firebase_auth::JwksCache::new())),
        trust_cache: physics_api::trust::TrustCache::new(
            std::time::Duration::from_secs(30),
            128,
        ),
        trust_invalidation_tx: tokio::sync::broadcast::channel(16).0,
        trusted_spot_check_rate: 50,
    });

    // Auth layer: needed by the `/api/me/*` routes which use the
    // `AuthOrApiKey` + `AuthSess` extractors. Routes that don't touch auth
    // happily ignore it.
    let session_store = MemoryStore::default();
    let session_layer = SessionManagerLayer::new(session_store).with_secure(false);
    let auth_backend = api_auth::Backend::new(pg.clone());
    let auth_layer = AuthManagerLayerBuilder::new(auth_backend, session_layer).build();

    let router = Router::new()
        .route(
            "/api/theorems/{hash}/lean",
            axum::routing::get(handlers::theorems::lean_download),
        )
        .route(
            "/api/theorems/recent",
            axum::routing::get(handlers::theorems::recent),
        )
        .route(
            "/api/theorems/{id}",
            axum::routing::get(handlers::theorems::by_id),
        )
        .route(
            "/api/theorems",
            axum::routing::get(handlers::theorems::list),
        )
        .route(
            "/api/events/discoveries",
            axum::routing::get(handlers::events::discoveries),
        )
        .route(
            "/api/events/stats",
            axum::routing::get(handlers::events::stats),
        )
        .route(
            "/api/seed",
            axum::routing::get(handlers::seed::seed),
        )
        .route(
            "/api/workers",
            axum::routing::get(handlers::workers::list),
        )
        .route(
            "/api/workers/heartbeat",
            axum::routing::post(handlers::workers::heartbeat),
        )
        .route(
            "/api/me/stats",
            axum::routing::get(handlers::me::stats),
        )
        .route(
            "/api/stats/landing",
            axum::routing::get(handlers::stats::landing),
        )
        .route(
            "/api/auth/firebase-session",
            axum::routing::post(physics_api::auth::firebase_session),
        )
        .route(
            "/api/auth/me",
            axum::routing::get(physics_api::auth::me),
        )
        .route(
            "/api/me/llm-keys",
            axum::routing::get(handlers::llm_keys::list),
        )
        .route(
            "/api/me/llm-keys",
            axum::routing::post(handlers::llm_keys::set_key),
        )
        .route(
            "/api/me/llm-keys/{provider}",
            axum::routing::delete(handlers::llm_keys::revoke),
        )
        .route(
            "/api/conjecture",
            axum::routing::post(handlers::conjecture::create),
        )
        .route(
            "/api/conjecture/{id}",
            axum::routing::get(handlers::conjecture::get_one),
        )
        .route(
            "/api/conjecture/{id}/start",
            axum::routing::post(handlers::conjecture::start),
        )
        .route(
            "/api/conjecture/{id}/sse",
            axum::routing::get(handlers::conjecture::sse),
        )
        .route(
            "/api/conjecture/{id}/paper",
            axum::routing::post(handlers::conjecture::start_paper_draft),
        )
        .route(
            "/api/conjecture/{id}/paper.md",
            axum::routing::get(handlers::conjecture::get_paper),
        )
        .route(
            "/api/me/conjectures",
            axum::routing::get(handlers::conjecture::list_mine),
        )
        // Phase E worker endpoints
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
        .layer(auth_layer)
        .with_state(Arc::clone(&state));

    Some(TestApp {
        router,
        pg,
        reverify_event_tx: reverify_event_tx_for_test,
        state,
        _guard: guard,
        _rocks_dir: rocks_dir,
    })
}

/// Issue a `GET` request through the in-memory router, buffering the
/// response body. Up to 1 MiB body — enough for any read endpoint we test.
pub async fn get(app: &TestApp, path: &str) -> Resp {
    let req = Request::builder()
        .method("GET")
        .uri(path)
        .body(Body::empty())
        .unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let body_bytes = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap().to_vec();
    Resp {
        status,
        body: body_bytes,
    }
}

/// Issue a `POST` request with a JSON body through the in-memory router.
/// `bearer` is an optional `Authorization: Bearer …` token.
pub async fn post(
    app: &TestApp,
    path: &str,
    body: &serde_json::Value,
    bearer: Option<&str>,
) -> Resp {
    let mut builder = Request::builder()
        .method("POST")
        .uri(path)
        .header(axum::http::header::CONTENT_TYPE, "application/json");
    if let Some(tok) = bearer {
        builder = builder.header(axum::http::header::AUTHORIZATION, format!("Bearer {tok}"));
    }
    let req = builder
        .body(Body::from(serde_json::to_vec(body).unwrap()))
        .unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let body_bytes = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap().to_vec();
    Resp {
        status,
        body: body_bytes,
    }
}

/// Insert `n` `Verified` theorems with deterministic distinct hashes and
/// return their hex-encoded canonical hashes (which are also the primary
/// keys, since `id == canonical_hash` in Phase 9).
///
/// Each theorem's `verified_at` is staggered by 1µs (via the natural
/// `mark_verified` clock) so the cursor pagination has a deterministic
/// newest-first ordering even on fast machines.
pub async fn seed_verified_theorems(app: &TestApp, n: usize) -> Vec<String> {
    let mut hexes = Vec::with_capacity(n);
    for i in 0..n {
        let canonical = format!("seed_theorem_{i}");
        let id = nasrudin_core::canonical_hash(&canonical);
        let row = theorem_q::NewTheorem {
            id: id.clone(),
            canonical_hash: id.clone(),
            canonical_statement: canonical.clone(),
            domain: "PureMath".into(),
            lean_source: format!("theorem t{i} : True := trivial"),
            chain_json: serde_json::json!([]),
            engine_git_sha: "test".into(),
            lean_version: "4.27.0".into(),
            contributor_id: "test".into(),
            ..Default::default()
        };
        theorem_q::insert_pending(&app.pg, row).await.unwrap();
        theorem_q::mark_verified(&app.pg, &id, "A", "rfl", 1)
            .await
            .unwrap();
        hexes.push(hex::encode(&id));
    }
    hexes
}
