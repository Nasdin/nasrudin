//! Public landing-page stats. 60-second in-process cache, no auth.
//!
//! Drives the sign-in page sidebar. Returns three numbers — total verified
//! theorems (RocksDB stats), workers heartbeating in the last 5 minutes
//! (PG), and distinct contributors (PG). On any source error we return the
//! stale cached value if we have one, else zeros.

use std::sync::Arc;
use std::time::{Duration, Instant};

use axum::{Json, extract::State};
use serde::Serialize;
use tokio::sync::RwLock;

use crate::state::AppState;

const CACHE_TTL: Duration = Duration::from_secs(60);
const ACTIVE_WINDOW_MIN: i64 = 5;

/// Public landing/workers-page network pulse.
///
/// All counts come from the `theorems` mirror table; the cache TTL means the
/// lifetime totals + 24h windows are at most 60 s stale. The `last_verified_*`
/// fields drive the "last verification Ks ago" ticker — clients render the
/// elapsed time client-side from `last_verified_at`, so even the cached value
/// stays fresh-feeling between recomputes.
#[derive(Clone, Debug, Serialize)]
pub struct LandingStats {
    pub verified_theorems: u64,
    pub active_workers: u64,
    pub contributors: u64,
    /// `Verified` theorems with `verified_at` in the last 24 hours.
    pub verified_24h: u64,
    /// `Verified` theorems with `verified_at` in the last hour.
    pub verified_1h: u64,
    /// ISO-8601 timestamp of the most recent `Verified` theorem, or `None`
    /// when the corpus is empty. Clients format "Ks ago" off the wall clock.
    pub last_verified_at: Option<String>,
    /// Domain of that most-recent verification (e.g. `"special_relativity"`).
    pub last_verified_domain: Option<String>,
    /// Per-domain breakdown of the `verified_24h` count, ordered by count
    /// descending. `(domain, count)` pairs.
    pub by_domain_24h: Vec<DomainCount>,
    /// Discard-funnel for the last 24 hours: how many candidates the
    /// network produced, how many landed in pending verification, how
    /// many Lean accepted, how many it rejected. Honest "1-in-N
    /// survives" view of the pipeline.
    pub funnel_24h: FunnelStats,
}

#[derive(Clone, Debug, Serialize)]
pub struct DomainCount {
    pub domain: String,
    pub count: u64,
}

/// Pipeline funnel — see `LandingStats::funnel_24h`. All four counts
/// live in the `theorems` mirror table; queries are O(log n) via
/// partial indexes added in m20260501_000020.
#[derive(Clone, Debug, Serialize)]
pub struct FunnelStats {
    /// Theorems whose `created_at` falls inside the 24h window —
    /// every worker submission lands here regardless of outcome.
    pub submitted_24h: u64,
    /// Theorems with `status='Verified'` and `verified_at` in window.
    /// Same number as the top-level `verified_24h`; duplicated here so
    /// the funnel is self-contained for the chart component.
    pub verified_24h: u64,
    /// Theorems with `status='Rejected'` and `created_at` in window —
    /// Lean kernel said no.
    pub rejected_24h: u64,
    /// Live pending count — theorems sitting in the lake-build queue
    /// right now. Not bounded to 24h: this is the instantaneous depth.
    pub pending_now: u64,
}

impl FunnelStats {
    pub fn zero() -> Self {
        Self {
            submitted_24h: 0,
            verified_24h: 0,
            rejected_24h: 0,
            pending_now: 0,
        }
    }
}

impl LandingStats {
    pub fn zero() -> Self {
        Self {
            verified_theorems: 0,
            active_workers: 0,
            contributors: 0,
            verified_24h: 0,
            verified_1h: 0,
            last_verified_at: None,
            last_verified_domain: None,
            by_domain_24h: Vec::new(),
            funnel_24h: FunnelStats::zero(),
        }
    }
}

#[derive(Default)]
pub struct LandingStatsCache {
    inner: RwLock<Option<(Instant, LandingStats)>>,
}

impl LandingStatsCache {
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(None),
        }
    }

    /// Returns the cached value if younger than `CACHE_TTL`, else None.
    async fn get_fresh(&self) -> Option<LandingStats> {
        let guard = self.inner.read().await;
        if let Some((ts, ref stats)) = *guard {
            if ts.elapsed() < CACHE_TTL {
                return Some(stats.clone());
            }
        }
        None
    }

    async fn store(&self, stats: LandingStats) {
        *self.inner.write().await = Some((Instant::now(), stats));
    }

    /// Returns the cached value regardless of age (used as a fallback when
    /// recomputation fails).
    async fn get_stale(&self) -> Option<LandingStats> {
        self.inner.read().await.as_ref().map(|(_, s)| s.clone())
    }
}

/// `GET /api/stats/landing` — public, 60s cached.
pub async fn landing(State(state): State<Arc<AppState>>) -> Json<LandingStats> {
    if let Some(fresh) = state.landing_stats.get_fresh().await {
        return Json(fresh);
    }

    let computed = compute(&state).await;
    let to_return = match computed {
        Ok(stats) => stats,
        Err(e) => {
            tracing::warn!(error = %e, "landing stats: compute failed; returning stale or zeros");
            state.landing_stats.get_stale().await.unwrap_or_else(LandingStats::zero)
        }
    };

    state.landing_stats.store(to_return.clone()).await;
    Json(to_return)
}

async fn compute(state: &Arc<AppState>) -> anyhow::Result<LandingStats> {
    let verified_theorems = state
        .db
        .get_stats()
        .map(|s| s.total_theorems)
        .unwrap_or(0);

    let mut stats = LandingStats {
        verified_theorems,
        ..LandingStats::zero()
    };

    if let Some(ref pg) = state.pg {
        stats.active_workers = nasrudin_pg::query::workers::count_active_workers(
            pg,
            chrono::Duration::minutes(ACTIVE_WINDOW_MIN),
        )
        .await?;
        stats.contributors =
            nasrudin_pg::query::workers::count_distinct_contributors(pg).await?;

        let now = chrono::Utc::now();
        let since_24h = now - chrono::Duration::hours(24);
        let since_1h = now - chrono::Duration::hours(1);

        stats.verified_24h =
            nasrudin_pg::query::theorems::count_verified_since(pg, since_24h).await?;
        stats.verified_1h =
            nasrudin_pg::query::theorems::count_verified_since(pg, since_1h).await?;

        let by_domain =
            nasrudin_pg::query::theorems::count_verified_by_domain_since(pg, since_24h).await?;
        stats.by_domain_24h = by_domain
            .into_iter()
            .map(|(domain, count)| DomainCount {
                domain,
                count: count.max(0) as u64,
            })
            .collect();

        if let Some((verified_at, domain)) =
            nasrudin_pg::query::theorems::last_verified(pg).await?
        {
            stats.last_verified_at = Some(verified_at.to_rfc3339());
            stats.last_verified_domain = Some(domain);
        }

        // Discard funnel — same 24h window as `verified_24h` so the
        // submitted vs verified ratio reads consistently. `pending_now`
        // is instantaneous (no time window), reflecting current lake
        // queue depth.
        let submitted = nasrudin_pg::query::theorems::count_submitted_since(pg, since_24h).await?;
        let rejected = nasrudin_pg::query::theorems::count_rejected_since(pg, since_24h).await?;
        let pending = nasrudin_pg::query::theorems::count_pending(pg).await?;
        stats.funnel_24h = FunnelStats {
            submitted_24h: submitted,
            verified_24h: stats.verified_24h,
            rejected_24h: rejected,
            pending_now: pending,
        };
    }

    Ok(stats)
}
