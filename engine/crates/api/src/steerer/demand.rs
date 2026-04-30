//! Aggregate user-demand signals over a sliding window for the steerer
//! prompt.
//!
//! The platform doesn't have a dedicated search-log table (the design
//! spec called for one but Phase 9 ships without it; logging individual
//! `/api/search` hits would be high-volume and isn't needed for any
//! other product surface). Instead we synthesise demand from three
//! durable signals that *do* persist:
//!
//!   1. `saved_searches` — explicit "I care about this LaTeX" bookmarks.
//!      Ground-truth user intent, but coarse (one row per save).
//!   2. `targeted_search_usage` — `conjecture_jobs` created in the
//!      window, surfacing the hunches paying Researchers gave us.
//!   3. `conjecture_jobs.hunch` (claimed/running) — what's currently
//!      being chased; the steerer should bias the explorer fleet
//!      toward prerequisite lemmas in those domains.
//!
//! The output is a `DemandSnapshot` that the prompt builder serialises
//! verbatim into the LLM context.

use chrono::Utc;
use sea_orm::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Duration;

use nasrudin_pg::entity::{conjecture_jobs, saved_searches, targeted_search_usage};

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct DemandSnapshot {
    pub window_seconds: u64,
    /// (latex, count_of_user_saves) — newest unique latex strings,
    /// truncated to top N by frequency.
    pub top_saved_searches: Vec<(String, u32)>,
    /// Number of paid-conjecture submissions inside the window.
    pub targeted_search_count: u64,
    /// (hunch_summary, count) for jobs currently `claimed`/`running`
    /// — surfaces what paying Researchers are actively chasing.
    pub active_hunches: Vec<(String, u32)>,
}

pub async fn aggregate_demand(
    db: &DatabaseConnection,
    window: Duration,
) -> Result<DemandSnapshot, DbErr> {
    let cutoff = Utc::now() - chrono::Duration::from_std(window).unwrap_or_default();
    let cutoff_off = cutoff.fixed_offset();

    // 1. saved_searches — group identical latex strings, take top 10.
    let saved_rows = saved_searches::Entity::find()
        .filter(saved_searches::Column::CreatedAt.gt(cutoff_off))
        .all(db)
        .await?;
    let mut saved_counts: HashMap<String, u32> = HashMap::new();
    for r in saved_rows {
        *saved_counts.entry(r.latex).or_insert(0) += 1;
    }
    let mut saved_vec: Vec<(String, u32)> = saved_counts.into_iter().collect();
    saved_vec.sort_by(|a, b| b.1.cmp(&a.1));
    saved_vec.truncate(10);

    // 2. targeted_search_usage — total count in window.
    let targeted_search_count = targeted_search_usage::Entity::find()
        .filter(targeted_search_usage::Column::CreatedAt.gt(cutoff_off))
        .count(db)
        .await?;

    // 3. conjecture_jobs currently active — top by their hunch's
    //    first ~100 chars (deduped because a Researcher can claim
    //    duplicate hunches from the queue).
    let active_rows = conjecture_jobs::Entity::find()
        .filter(conjecture_jobs::Column::State.is_in(["claimed", "running", "Running"]))
        .filter(conjecture_jobs::Column::LeaseExpiresAt.gt(Utc::now().fixed_offset()))
        .all(db)
        .await?;
    let mut active_counts: HashMap<String, u32> = HashMap::new();
    for r in active_rows {
        let summary: String = r.hunch.chars().take(100).collect();
        *active_counts.entry(summary).or_insert(0) += 1;
    }
    let mut active_vec: Vec<(String, u32)> = active_counts.into_iter().collect();
    active_vec.sort_by(|a, b| b.1.cmp(&a.1));
    active_vec.truncate(10);

    Ok(DemandSnapshot {
        window_seconds: window.as_secs(),
        top_saved_searches: saved_vec,
        targeted_search_count,
        active_hunches: active_vec,
    })
}
