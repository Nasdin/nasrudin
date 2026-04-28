//! Query helpers backing `/api/search`.
//!
//! Three lookup shapes:
//!   * [`find_by_ac_hash`] — Tier 1 exact match.
//!   * [`candidates`] — Tier 2 narrowing for Rust-side unification + Tier 3
//!     near-miss ranking. Filters by domain, dimension, required-axiom
//!     containment, and max derivation depth; only returns `Verified` rows.
//!   * [`find_by_axiom_set`] — convenience wrapper for the
//!     "show me everything derivable from these axioms" browse mode.

use anyhow::{Context, Result};
use sea_orm::{
    ColumnTrait, ConnectionTrait, EntityTrait, QueryFilter, QueryOrder, QuerySelect, sea_query::Expr,
};

use crate::entity::theorems;

/// Look up a single verified theorem by its 8-byte AC-canonical hash.
///
/// Returns `None` for missing rows or rows that haven't been backfilled
/// yet (i.e. `canonical_ac_hash IS NULL`).
pub async fn find_by_ac_hash(
    db: &impl ConnectionTrait,
    hash: &[u8],
) -> Result<Option<theorems::Model>> {
    theorems::Entity::find()
        .filter(theorems::Column::CanonicalAcHash.eq(hash.to_vec()))
        .filter(theorems::Column::Status.eq("Verified"))
        .one(db)
        .await
        .context("find_by_ac_hash")
}

/// Filter set for candidate narrowing.
///
/// Any field set to `None`/empty is dropped from the WHERE clause. An empty
/// `CandidateFilter` returns the most-recent `Verified` rows up to `limit`.
#[derive(Default, Clone, Debug)]
pub struct CandidateFilter {
    pub domain: Option<String>,
    pub dimension: Option<Vec<i32>>,
    pub axioms_required: Vec<String>,
    pub max_depth: Option<i32>,
}

/// Return up to `limit` verified candidates matching `filter`. Ordering is
/// shallowest-first (`depth ASC`, NULLs last) so unification finds the
/// most-fundamental match first.
///
/// `axioms_required` uses PostgreSQL array containment (`axioms_used @>
/// $1::text[]`) — the GIN index on `axioms_used` keeps this fast even at
/// corpus scale. `dimension` is an exact-match check against the seven-vector
/// signature.
pub async fn candidates(
    db: &impl ConnectionTrait,
    filter: &CandidateFilter,
    limit: u64,
) -> Result<Vec<theorems::Model>> {
    let mut q = theorems::Entity::find().filter(theorems::Column::Status.eq("Verified"));

    if let Some(domain) = filter.domain.as_ref() {
        q = q.filter(theorems::Column::Domain.eq(domain.clone()));
    }
    if let Some(max_depth) = filter.max_depth {
        q = q.filter(theorems::Column::Depth.lte(max_depth));
    }
    if let Some(dim) = filter.dimension.as_ref() {
        // Exact array equality. `dim @> X AND dim <@ X` would match the GIN
        // index but `=` is just as fast given the tiny array length and lets
        // SeaORM bind the array natively.
        q = q.filter(Expr::cust_with_values(
            "dimension = $1::integer[]",
            [dim.clone()],
        ));
    }
    if !filter.axioms_required.is_empty() {
        q = q.filter(Expr::cust_with_values(
            "axioms_used @> $1::text[]",
            [filter.axioms_required.clone()],
        ));
    }

    q.order_by_asc(theorems::Column::Depth)
        .order_by_desc(theorems::Column::VerifiedAt)
        .limit(limit)
        .all(db)
        .await
        .context("search::candidates")
}

/// "Show me everything derivable from this axiom set." Convenience wrapper
/// over [`candidates`] for the browse-by-axiom mode.
pub async fn find_by_axiom_set(
    db: &impl ConnectionTrait,
    axioms: Vec<String>,
    limit: u64,
) -> Result<Vec<theorems::Model>> {
    candidates(
        db,
        &CandidateFilter {
            axioms_required: axioms,
            ..Default::default()
        },
        limit,
    )
    .await
}
