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
}

/// Cache key for the `/api/seed` JSON response cache. Distinct
/// `(domain, top)` requests produce distinct response bodies, so each
/// gets its own cached entry. `None` domain == "no domain filter".
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SeedCacheKey {
    pub domain: Option<String>,
    pub top: u64,
}
