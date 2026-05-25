//! `GET /api/discoveries/novel` — M3 novel-discovery surface.
//!
//! Returns GA-verified theorems whose canonical statement does NOT
//! appear in the PhysLean catalog. The acceptance criterion (M3):
//!
//!   * `verification_tactic != 'imported'`  (excludes catalog mirrors)
//!   * `generation > 0`                     (excludes seed axioms)
//!   * `canonical_hash ∉ catalog_hashes`    (the novelty bit)
//!
//! The catalog hash set is pre-built at API boot from
//! `physlean-extract/output/catalog.json` via
//! [`nasrudin_derive::axiom_store::AxiomStore::collect_catalog_eq_canonicals`]
//! and lives in [`crate::state::AppState::catalog_hashes`]. When the
//! catalog file isn't on disk at boot the set is empty and this
//! endpoint degrades to "every non-imported GA theorem is novel" — a
//! permissive fallback (operators see the behavior in the response's
//! `catalog_hashes_loaded` field).
//!
//! Pagination: cursor-less, single-page newest-first; capped at 500
//! rows per request. Callers that need more should slice by `domain`.

use axum::{
    Json,
    extract::{Query, State},
    http::StatusCode,
    response::IntoResponse,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::state::AppState;

/// Query parameters for `/api/discoveries/novel`.
#[derive(Debug, Deserialize, Default)]
pub struct NovelQuery {
    /// Max rows to return. Default 50, hard-capped at 500.
    pub limit: Option<u64>,
    /// Optional domain filter (e.g. `"Special relativity"`).
    pub domain: Option<String>,
    /// How many DB rows to inspect before the catalog-novelty filter.
    /// Default 1000, hard-capped at 5000. The handler scans newest-first
    /// and stops once it has `limit` novel matches or exhausts the
    /// scanned window. Increase when expecting a low novel-hit rate.
    pub scan: Option<u64>,
}

/// One novel-discovery row in the response.
#[derive(Debug, Clone, Serialize)]
pub struct NovelDiscovery {
    /// Hex-encoded 8-byte id (== canonical_hash in Phase 9).
    pub id: String,
    /// Hex-encoded canonical_hash. Equal to `id` today; kept distinct
    /// in the schema for forward-compat with a future split.
    pub canonical_hash: String,
    pub canonical_statement: String,
    pub latex: Option<String>,
    pub domain: String,
    pub generation: Option<i64>,
    pub verification_tactic: Option<String>,
    pub verified_at: Option<chrono::DateTime<chrono::Utc>>,
    pub axioms_used: Vec<String>,
    pub contributor_id: String,
}

/// Response envelope. The flags help operators distinguish "no
/// discoveries yet" from "catalog set wasn't loaded so everything
/// looks novel".
#[derive(Debug, Clone, Serialize)]
pub struct NovelResponse {
    pub discoveries: Vec<NovelDiscovery>,
    /// Count of rows in the catalog hash set. `0` means the boot-time
    /// load found no file or the catalog has no Eq-rooted entries —
    /// the endpoint then doesn't reject anything.
    pub catalog_hashes_loaded: usize,
    /// How many rows we scanned before applying the catalog filter.
    /// Useful for telling "we hit the scan cap" from "we ran out of
    /// candidate rows".
    pub scanned: usize,
    /// How many of the scanned rows survived the catalog filter and
    /// landed in `discoveries` (after `limit` truncation). Note this
    /// can be less than `scanned` even before truncation — it's the
    /// post-filter count, not the post-limit count.
    pub returned: usize,
}

/// `GET /api/discoveries/novel` — M3 novel-discovery feed.
pub async fn novel(
    State(state): State<Arc<AppState>>,
    Query(q): Query<NovelQuery>,
) -> impl IntoResponse {
    use nasrudin_pg::sea_orm::{
        ColumnTrait, Condition, EntityTrait, QueryFilter, QueryOrder, QuerySelect,
    };

    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({ "error": "pg_unavailable" })),
            )
                .into_response();
        }
    };

    let limit = q.limit.unwrap_or(50).min(500) as usize;
    let scan = q.scan.unwrap_or(1000).min(5000);

    // SQL pre-filter: status + non-imported tactic + gen > 0. The
    // catalog-novelty check is a Rust-side HashSet lookup since
    // catalog_hashes lives in memory, not Postgres. We over-scan
    // (`scan`) because at steady state most GA-verified rows
    // rediscover catalog formulas; the post-filter survival rate is
    // expected to be low.
    let mut query = nasrudin_pg::entity::theorems::Entity::find()
        .filter(nasrudin_pg::entity::theorems::Column::Status.eq("Verified"))
        // verification_tactic IS NULL OR != 'imported'. In-process GA
        // discoveries leave the column NULL; PhysLean imports stamp it
        // as 'imported'. Either branch is "not imported" for M3's
        // purposes — only the explicit 'imported' stamp is excluded.
        .filter(
            Condition::any()
                .add(
                    nasrudin_pg::entity::theorems::Column::VerificationTactic.is_null(),
                )
                .add(
                    nasrudin_pg::entity::theorems::Column::VerificationTactic
                        .ne("imported"),
                ),
        )
        // generation > 0: seed axioms (gen 0) aren't discoveries even
        // when they happen to carry a non-imported tactic.
        .filter(nasrudin_pg::entity::theorems::Column::Generation.gt(0i64));
    if let Some(d) = q.domain.as_ref() {
        query = query.filter(nasrudin_pg::entity::theorems::Column::Domain.eq(d.clone()));
    }

    let rows = match query
        .order_by_desc(nasrudin_pg::entity::theorems::Column::VerifiedAt)
        .order_by_desc(nasrudin_pg::entity::theorems::Column::Id)
        .limit(scan)
        .all(pg)
        .await
    {
        Ok(r) => r,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };

    let scanned = rows.len();
    let catalog = &state.catalog_hashes;

    // Post-filter: drop anything whose canonical_hash hits the catalog
    // set. When the catalog set is empty (missing file at boot) this
    // is a no-op — every row passes through.
    let mut discoveries: Vec<NovelDiscovery> = Vec::with_capacity(limit.min(scanned));
    for thm in rows {
        if !catalog.is_empty() && catalog.contains(&thm.canonical_hash) {
            continue;
        }
        discoveries.push(NovelDiscovery {
            id: hex::encode(&thm.id),
            canonical_hash: hex::encode(&thm.canonical_hash),
            canonical_statement: thm.canonical_statement,
            latex: thm.latex,
            domain: thm.domain,
            generation: thm.generation,
            verification_tactic: thm.verification_tactic,
            verified_at: thm.verified_at.map(|d| d.with_timezone(&chrono::Utc)),
            axioms_used: thm.axioms_used,
            contributor_id: thm.contributor_id,
        });
        if discoveries.len() >= limit {
            break;
        }
    }

    let returned = discoveries.len();
    (
        StatusCode::OK,
        Json(NovelResponse {
            discoveries,
            catalog_hashes_loaded: catalog.len(),
            scanned,
            returned,
        }),
    )
        .into_response()
}
