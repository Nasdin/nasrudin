//! Shared application state.

use std::sync::{Arc, Mutex};

use nasrudin_derive::AxiomStore;
use nasrudin_ga::{DiscoveryEvent, GaStatusSnapshot};
use nasrudin_rocks::TheoremDb;

pub struct AppState {
    pub db: Arc<TheoremDb>,
    pub pg: Option<nasrudin_pg::sea_orm::DatabaseConnection>,
    pub axiom_store: Arc<AxiomStore>,
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
}
