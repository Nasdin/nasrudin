//! `GET /api/resolve/{qualifier}` — resolve a Lean qualifier into either an
//! in-corpus theorem, a known axiom, or "unknown".
//!
//! The theorem detail page renders a "Built from" panel listing every
//! upstream constant the canonical statement references. For each one we
//! call this endpoint to find out where the user should land when they
//! click the row:
//!
//! - `Lorentz.Vector.timelike_time_dominates_space` is an imported PhysLean
//!   theorem — resolves to `kind: theorem` with its hex id, and the
//!   frontend renders an in-app `<Link to="/theorem/$id">`.
//! - `Lorentz.Vector.spatialPart` is a Lean *definition* (not a theorem);
//!   the importer registered it in the `AxiomStore` but it never got
//!   promoted to a `theorems` row. Resolves to `kind: axiom` with name +
//!   domain + description, and the frontend links to `/axiom/$name`.
//! - `Real`, some hygenic generated name, etc. — resolves to `kind: none`
//!   and the frontend renders plain text.
//!
//! Lookup order: theorem first, then axiom. We try the full qualifier as
//! the axiom name; if that misses we also try the last `.`-segment, since
//! the AxiomStore is keyed by short names for some legacy entries.

use axum::{
    Json,
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
};
use serde::Serialize;
use std::sync::Arc;

use crate::state::AppState;
use nasrudin_pg::query::theorems;

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ResolveResponse {
    Theorem {
        /// 8-byte hex id — same format `/theorem/$id` accepts.
        id: String,
        /// Domain enum string (`SpecialRelativity`, `Electromagnetism`, …).
        domain: String,
        /// The full Lean qualifier we matched on (echoed for the client).
        source: String,
        /// Verification tactic — useful for the detail page so it can show
        /// "imported" vs "GA-discovered" without re-fetching the row.
        verification_tactic: Option<String>,
    },
    Axiom {
        name: String,
        domain: String,
        description: String,
    },
    None,
}

/// Strip the last `.`-segment. `Foo.Bar.baz` → `baz`; bare names pass
/// through unchanged.
fn last_segment(s: &str) -> &str {
    s.rsplit('.').next().unwrap_or(s)
}

pub async fn resolve(
    State(state): State<Arc<AppState>>,
    Path(qualifier): Path<String>,
) -> impl IntoResponse {
    // Empty or unreasonably long qualifiers — reject early. A Lean
    // qualifier is at most a few hundred chars in practice; cap higher
    // than that with comfortable headroom to keep abuse paths cheap.
    if qualifier.is_empty() || qualifier.len() > 512 {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "bad_qualifier" })),
        )
            .into_response();
    }

    // 1. Theorem-by-imported-source lookup. This is the hot path because
    //    the seeded corpus is dominated by PhysLean imports.
    if let Some(pg) = state.pg.as_ref() {
        match theorems::find_by_imported_source(pg, &qualifier).await {
            Ok(Some(t)) => {
                let id_hex = hex::encode(&t.id);
                let source = t
                    .origin_payload
                    .as_ref()
                    .and_then(|p| p.get("Imported"))
                    .and_then(|i| i.get("source"))
                    .and_then(|s| s.as_str())
                    .unwrap_or(&qualifier)
                    .to_string();
                return (
                    StatusCode::OK,
                    Json(ResolveResponse::Theorem {
                        id: id_hex,
                        domain: t.domain.clone(),
                        source,
                        verification_tactic: t.verification_tactic.clone(),
                    }),
                )
                    .into_response();
            }
            Ok(None) => {}
            Err(e) => {
                // Log + fall through — a transient PG error here shouldn't
                // make every "Built from" row look broken; the axiom
                // fallback below still has a chance.
                tracing::warn!(
                    qualifier = %qualifier,
                    error = %e,
                    "resolve: pg lookup failed, falling back to axiom",
                );
            }
        }
    }

    // 2. AxiomStore lookup. Try the full qualifier first (PhysLean's
    //    importer registers the canonical full path), then the last
    //    segment as a defensive fallback for legacy short-keyed entries.
    let store = state.axiom_store.load();
    let hit = store
        .get(&qualifier)
        .or_else(|| store.get(last_segment(&qualifier)));
    if let Some(a) = hit {
        return (
            StatusCode::OK,
            Json(ResolveResponse::Axiom {
                name: a.name,
                domain: a.domain.to_string(),
                description: a.description,
            }),
        )
            .into_response();
    }

    // 3. Nothing matched. Return 200 + `kind: none` rather than 404 — the
    //    frontend renders a different element shape for "unknown" and
    //    using a status code as the type discriminator would force the
    //    client into try/catch on every dep row, which is awkward.
    (StatusCode::OK, Json(ResolveResponse::None)).into_response()
}
