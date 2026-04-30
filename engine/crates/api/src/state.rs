//! Shared application state.

use std::sync::{Arc, Mutex, RwLock};

use nasrudin_derive::AxiomStore;
use nasrudin_ga::{DiscoveryEvent, GaStatusSnapshot};
use nasrudin_rocks::TheoremDb;

/// Hot-swappable AxiomStore handle.
///
/// `Arc<RwLock<Arc<AxiomStore>>>` under the hood: cheap snapshot on read
/// (clone the inner Arc, drop the lock immediately), atomic replace on
/// write (`POST /api/admin/reload_corpus`). Workers continue holding the
/// old `Arc` for the duration of an in-flight chain replay; the next
/// `.load()` returns the freshly-loaded store.
#[derive(Clone)]
pub struct SharedAxiomStore(Arc<RwLock<Arc<AxiomStore>>>);

impl SharedAxiomStore {
    pub fn new(store: AxiomStore) -> Self {
        Self(Arc::new(RwLock::new(Arc::new(store))))
    }

    /// Take a snapshot. The returned `Arc` is independent — even if the
    /// store is replaced, the caller's reference stays valid.
    pub fn load(&self) -> Arc<AxiomStore> {
        self.0.read().unwrap_or_else(|e| e.into_inner()).clone()
    }

    /// Atomically replace the active store.
    pub fn replace(&self, store: AxiomStore) {
        let mut guard = self.0.write().unwrap_or_else(|e| e.into_inner());
        *guard = Arc::new(store);
    }
}

pub struct AppState {
    pub db: Arc<TheoremDb>,
    pub pg: Option<nasrudin_pg::sea_orm::DatabaseConnection>,
    /// Hot-swappable AxiomStore. Read via `.load()`; replaced atomically
    /// by `POST /api/admin/reload_corpus` after a fresh
    /// `lake exe extract` run.
    pub axiom_store: SharedAxiomStore,
    /// GA-side discovery channel — broadcasts [`nasrudin_ga::DiscoveryEvent`]
    /// to the `/api/events/discoveries` SSE stream.
    pub discovery_tx: tokio::sync::broadcast::Sender<DiscoveryEvent>,
    pub ga_status: Arc<Mutex<GaStatusSnapshot>>,

    // Phase 9 additions ---------------------------------------------------

    /// Lake builder pool (verifies submitted Lean against the trusted
    /// `prover/` template). Shared with the reverify queue and the future
    /// `/api/submit` ingest path.
    pub lake: Arc<crate::lake_builder::LakeBuilder>,
    /// Reverify-side broadcast channel — distinct from `discovery_tx` because
    /// it carries a different event type ([`crate::reverify::DiscoveryEvent`])
    /// and serves a different SSE stream slated for Phase 5.2.
    pub reverify_event_tx: tokio::sync::broadcast::Sender<crate::reverify::DiscoveryEvent>,
    /// Reverify queue + drain. `None` when PostgreSQL is not configured —
    /// the drain loop only runs when PG is wired up.
    pub reverify: Option<Arc<crate::reverify::ReverifyQueue>>,
    /// Per-worker token-bucket limiter (keyed by `worker_id`). Consumed by
    /// the `/api/ingest` handler (Phase 9 Task 4.2) at one token per
    /// submitted theorem; default 60/min per worker.
    pub worker_rate_limiter: Arc<crate::rate_limit::WorkerRateLimiter>,
    /// Shared secret for `/api/admin/*` endpoints (corpus reload, etc.).
    /// Set via `ADMIN_TOKEN` env var. When `None`, admin endpoints are
    /// disabled (return 503).
    pub admin_token: Option<String>,
    /// Server-side cache bundle (Phase A.5 wiring). `None` during early
    /// boot if [`crate::cache::CacheCtx::build`] fails — the GA / reverify
    /// paths fall back to direct verification. Populated unconditionally
    /// in production; the per-flag gating happens at the call site via
    /// `cache_ctx.config.attempts_enabled` etc.
    pub cache_ctx: Option<Arc<crate::cache::CacheCtx>>,
    /// Embedding index over the verified-theorem corpus (Phase B). `None`
    /// when `NASRUDIN_EMBED_ENABLED` is unset or the file isn't on disk.
    pub embed: Option<Arc<nasrudin_embed::EmbeddingIndex>>,
    /// fastembed Embedder (BGE-small-en-v1.5). Loaded eagerly at boot
    /// alongside the index when embed is enabled — first-request latency
    /// would otherwise eat ~1 s on the cold model load. ~150 MB resident.
    /// Used by `/api/search/concept`.
    pub embedder: Option<Arc<nasrudin_embed::Embedder>>,
    /// Filesystem path where the index lives. Used by the
    /// `/api/embed/index.bin` handler to stream the file directly.
    pub embed_path: Option<std::path::PathBuf>,
    /// 32-byte AES-256-GCM key, decoded once at boot from
    /// `NASRUDIN_KEY_ENCRYPT` (base64). When `None`, the
    /// `/api/me/llm-keys` endpoints all return 503 with
    /// `key_encrypt_unset` — production deployments must set this.
    pub llm_encrypt_key: Option<[u8; 32]>,
    /// Phase D conjecture-loop event channel. Senders: handlers that
    /// transition `conjecture_jobs` rows + (Phase E) worker progress
    /// callbacks. Receivers: per-job `/api/conjecture/{id}/sse`
    /// subscribers, filtered by `job_id`. Persisted twin lives in
    /// `conjecture_events` for replay.
    pub conjecture_event_tx:
        tokio::sync::broadcast::Sender<crate::conjecture::ConjectureEvent>,
    /// Lazy lake-build promotion (P-Task 2). Hot path is chain-replay
    /// primary; this drain promotes ChainVerified theorems to
    /// LakeVerified on consumption (download, seed-inclusion, manual
    /// trigger, background crawler). `None` when PG is not configured —
    /// promotion needs PG to fetch lean_source.
    pub lake_promotion: Option<Arc<crate::lake_promotion::LakePromotion>>,
    /// Stripe billing client. `None` when STRIPE_SECRET_KEY is unset —
    /// `/api/billing/*` endpoints return 503 in that case so the rest of
    /// the API still works for local dev without billing config.
    pub billing: Option<crate::billing::stripe_client::BillingClient>,
    /// In-memory `/api/seed` response cache, keyed by `(domain, top)`.
    /// Each entry holds `(generated_at, response_body_arc)`. TTL is
    /// applied at read time; the cache is invalidated wholesale by
    /// `/api/admin/reload_corpus` so a freshly-loaded AxiomStore is
    /// reflected immediately. With 4 workers polling /api/seed every
    /// chunk boundary (~60s), this saves ~13MB/min of redundant JSON
    /// serialisation work.
    pub seed_cache: Arc<
        Mutex<
            std::collections::HashMap<
                SeedCacheKey,
                (std::time::Instant, Arc<String>),
            >,
        >,
    >,
    /// Latest LLM-driven cluster steering snapshot. Initialised at
    /// boot to a `default_config()` snapshot; mutated atomically by
    /// the steerer task at every cycle. Read by `/api/steering` and
    /// folded into `/api/seed` so workers hot-reload the config.
    pub steering: Arc<arc_swap::ArcSwap<SteeringSnapshot>>,
    /// Per-island K assignment chosen by the UCB1 bandit. Updated
    /// every cycle alongside `steering` and folded into `/api/seed`
    /// so workers know how many clusters to k-means each chunk.
    pub cluster_config: Arc<arc_swap::ArcSwap<ClusterConfigSnapshot>>,
    /// Aggregate cluster-capacity tracker (sum of last-seen lake
    /// slots per worker, plus a counter of slots currently committed
    /// to paid `conjecture_jobs`). Drives the explorer-floor check in
    /// `POST /api/jobs/claim`.
    pub capacity: Arc<crate::jobs::capacity::CapacityTracker>,
    /// Per-job SSE broadcast channels for paid Researcher progress.
    /// Lazily inserted on first subscribe / first emit.
    pub job_events: Arc<
        dashmap::DashMap<
            uuid::Uuid,
            tokio::sync::broadcast::Sender<crate::jobs::JobEvent>,
        >,
    >,
    /// 60-second cache backing `GET /api/stats/landing`.
    pub landing_stats: Arc<crate::handlers::stats::LandingStatsCache>,
    /// Firebase project id (e.g. `"nasrudin"`). When `None`,
    /// `/api/auth/firebase-session` returns 503 and email/Google sign-in
    /// is unavailable. Other endpoints work normally.
    pub firebase_project_id: Option<String>,
    /// Lazily-fetched Google JWKs, used to verify Firebase ID tokens.
    pub firebase_jwks: Arc<crate::firebase_auth::JwksCache>,

    // ── Admin panel + trust bypass ────────────────────────────────────
    /// Trust-decision cache keyed by `api_keys.id`. 30 s TTL, 4096
    /// capacity. Populated lazily by the ingest path; invalidated
    /// surgically via `trust_invalidation_tx` when admin endpoints
    /// mutate trust state.
    pub trust_cache: crate::trust::TrustCache,
    /// Broadcast channel for cache invalidation. Admin handlers post
    /// `CacheInvalidation::{ApiKey,User,All}` after committing a trust
    /// mutation; a single tokio task subscribes and purges.
    pub trust_invalidation_tx:
        tokio::sync::broadcast::Sender<crate::trust::CacheInvalidation>,
    /// Default spot-check rate (`TRUSTED_SPOT_CHECK_RATE` env var).
    /// Used when neither the api_key nor the user has an override set.
    pub trusted_spot_check_rate: u32,
    /// Reusable HTTP client for direct Stripe REST calls (refund flow).
    /// Distinct from `BillingClient.stripe` (which is `stripe::Client`)
    /// because the refund + reconciler use raw REST for explicit
    /// idempotency-key control.
    pub stripe_http: reqwest::Client,
    /// Base URL for direct Stripe REST calls. `https://api.stripe.com`
    /// in production; tests override to a wiremock server.
    pub stripe_base_url: String,
    /// `STRIPE_SECRET_KEY` env var, or empty string when unset (in
    /// which case the refund handler returns 503).
    pub stripe_secret: String,
    /// HMAC signing key for impersonation tokens. Hex-decoded from
    /// `IMPERSONATION_SIGNING_KEY`. `None` disables impersonation —
    /// the start handler returns 503.
    pub impersonation_signing_key: Option<Vec<u8>>,
    /// Per-run progress channel for bulk admin operations. Senders:
    /// the bulk runner task. Receivers: SSE handlers filtered by run_id.
    pub bulk_run_progress_tx: tokio::sync::broadcast::Sender<(
        uuid::Uuid,
        crate::admin::bulk_runner::BulkProgress,
    )>,
}

/// Cache key for the `/api/seed` JSON response cache. Distinct
/// `(domain, top)` requests produce distinct response bodies, so each
/// gets its own cached entry. `None` domain == "no domain filter".
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SeedCacheKey {
    pub domain: Option<String>,
    pub top: u64,
}

/// Hot-swappable steerer snapshot stored in `AppState.steering`.
///
/// `etag` is a `u64` (xxhash64 of the serialised config) that the
/// `/api/steering` and `/api/seed` handlers expose to clients so they
/// can do conditional-GET. `started_at` is the cycle's start time and
/// gets surfaced to the worker for debugging.
pub struct SteeringSnapshot {
    pub config: serde_json::Value,
    pub etag: u64,
    pub started_at: chrono::DateTime<chrono::Utc>,
}

/// UCB1 bandit's chosen K per island. Workers read this from
/// `/api/seed` and run k-means with the assigned K each chunk.
/// Decoupled from `SteeringSnapshot` because the bandit picks K
/// independently of the LLM emission (different update cadences,
/// different invariants).
#[derive(Debug, Clone, Default)]
pub struct ClusterConfigSnapshot {
    /// island_domain → K
    pub k_per_island: std::collections::HashMap<String, u32>,
    pub etag: u64,
}

impl AppState {
    /// Drop every cached `/api/seed` response. Called by the steerer
    /// after it rotates a new config so workers don't see a stale
    /// pairing of axioms+steering for up to the cache TTL.
    pub fn invalidate_seed_cache(&self) {
        if let Ok(mut g) = self.seed_cache.lock() {
            g.clear();
        }
    }
}
