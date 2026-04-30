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

#[derive(Clone, Debug, Serialize)]
pub struct LandingStats {
    pub verified_theorems: u64,
    pub active_workers: u64,
    pub contributors: u64,
}

impl LandingStats {
    pub fn zero() -> Self {
        Self {
            verified_theorems: 0,
            active_workers: 0,
            contributors: 0,
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

    let (active_workers, contributors) = if let Some(ref pg) = state.pg {
        let active = nasrudin_pg::query::workers::count_active_workers(
            pg,
            chrono::Duration::minutes(ACTIVE_WINDOW_MIN),
        )
        .await?;
        let contrib = nasrudin_pg::query::workers::count_distinct_contributors(pg).await?;
        (active, contrib)
    } else {
        (0, 0)
    };

    Ok(LandingStats {
        verified_theorems,
        active_workers,
        contributors,
    })
}
