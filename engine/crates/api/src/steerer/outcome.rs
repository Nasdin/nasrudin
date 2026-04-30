//! Compute the outcome JSON that closes a cycle.
//!
//! Each cycle's outcome is the LLM's feedback signal for the next
//! cycle: what actually happened during this window? We measure:
//!
//!   * Theorems verified during the window — the headline output.
//!   * Domain distribution actual vs. requested (the LLM bias the
//!     domain_weights toward thermo, did the explorer fleet actually
//!     verify thermo theorems? if not, the model knows its next
//!     domain_weights need a stronger push).
//!   * Cascade rejections — bad theorems fanning out.
//!   * Lake failure rate.
//!   * User engagement — manual verifies + downloads (placeholder
//!     wired in 7.1).
//!
//! All counts are bounded windows so the LLM context stays small.

use chrono::{DateTime, Utc};
use sea_orm::{DatabaseConnection, DbErr};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct OutcomeJson {
    pub theorems_verified_in_window: u64,
    pub domain_distribution_actual: HashMap<String, f32>,
    /// Filled-in when GA reports back via heartbeat (Phase 6); 0.0
    /// until then. Kept here so the schema is stable for the model.
    pub target_hit_rate: f32,
    /// Same — 0.0 until Phase 6 wiring.
    pub population_diversity_delta: f32,
    pub cascade_rejects: u64,
    pub lake_failure_rate: f32,
    pub user_engagement: UserEngagement,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct UserEngagement {
    pub views: u64,
    pub downloads: u64,
    pub manual_verifies: u64,
    pub median_dwell_ms: u64,
}

/// Compute outcome for the window `[window_start, window_end]`.
///
/// All counts gracefully fall back to 0 on PG errors — outcome is a
/// best-effort hint for the next prompt, not an authoritative record.
pub async fn compute_outcome(
    db: &DatabaseConnection,
    window_start: DateTime<Utc>,
    window_end: DateTime<Utc>,
) -> Result<OutcomeJson, DbErr> {
    use nasrudin_pg::entity::theorems;
    use sea_orm::*;

    // Theorems with verified_at in window.
    let in_window = theorems::Entity::find()
        .filter(theorems::Column::VerifiedAt.gte(window_start.fixed_offset()))
        .filter(theorems::Column::VerifiedAt.lte(window_end.fixed_offset()))
        .all(db)
        .await
        .unwrap_or_default();

    let theorems_verified_in_window = in_window.len() as u64;

    let mut by_domain: HashMap<String, u64> = HashMap::new();
    for t in &in_window {
        *by_domain.entry(t.domain.clone()).or_insert(0) += 1;
    }
    let total: u64 = by_domain.values().sum();
    let domain_distribution_actual = if total > 0 {
        by_domain
            .into_iter()
            .map(|(k, v)| (k, v as f32 / total as f32))
            .collect()
    } else {
        HashMap::new()
    };

    // Cascade rejects: theorems with status="Rejected" + reason
    // beginning "ancestor_rejected:" (the cascade marker emitted by
    // P-Task 3 cascade_reject).
    let cascades = theorems::Entity::find()
        .filter(theorems::Column::VerifiedAt.gte(window_start.fixed_offset()))
        .filter(theorems::Column::VerifiedAt.lte(window_end.fixed_offset()))
        .filter(theorems::Column::Status.eq("Rejected"))
        .all(db)
        .await
        .unwrap_or_default();
    let cascade_rejects = cascades
        .iter()
        .filter(|t: &&theorems::Model| {
            t.rejected_reason
                .as_deref()
                .is_some_and(|r| r.starts_with("ancestor_rejected:"))
        })
        .count() as u64;

    // Lake-failure rate over the window: rejected / (verified + rejected).
    let denom = (in_window.len() + cascades.len()) as f32;
    let lake_failure_rate = if denom > 0.0 {
        cascades.len() as f32 / denom
    } else {
        0.0
    };

    Ok(OutcomeJson {
        theorems_verified_in_window,
        domain_distribution_actual,
        target_hit_rate: 0.0,
        population_diversity_delta: 0.0,
        cascade_rejects,
        lake_failure_rate,
        user_engagement: UserEngagement::default(),
    })
}
