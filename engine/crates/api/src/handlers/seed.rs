//! `GET /api/seed` — remote-worker bootstrap endpoint (Phase 9 Task 5.3).
//!
//! Returns the in-memory axiom catalog plus the top-N highest-fitness
//! `Verified` theorems for the given domain. A Phase-10 remote worker calls
//! this once at cold start to seed its local GA population without having to
//! page the full theorem mirror.
//!
//! Shape:
//! ```json
//! {
//!   "axioms":         [{"name": "...", "statement": "...", "domain": "..."}, ...],
//!   "seed_theorems":  [<Theorem>, ...]
//! }
//! ```
//!
//! `top` is clamped to 500 to keep the response bounded.
//! When PostgreSQL is not configured, the endpoint returns `503` with
//! `error = "pg_unavailable"` for symmetry with the rest of the read API.

use axum::{
    Json,
    extract::{Query, State},
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
};
use serde::Deserialize;
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::state::{AppState, ComputeArmsSnapshot, DirectiveArmsSnapshot, SeedCacheKey};

/// Compact the compute-arm snapshot into per-(island, strength_bucket)
/// slots with the 5 multiplier_choice arms inlined. ~30 slots × 120 B
/// ≈ 4 KB plain, ~1 KB gzipped.
fn compute_arms_compact(snap: &ComputeArmsSnapshot) -> Vec<serde_json::Value> {
    use std::collections::BTreeMap;
    type SlotKey = (String, i16);
    let mut by_slot: BTreeMap<SlotKey, Vec<serde_json::Value>> = BTreeMap::new();
    for r in &snap.arms {
        let key = (r.island_domain.clone(), r.strength_bucket);
        let mean = if r.pulls > 0 {
            r.total_reward / r.pulls as f64
        } else {
            0.0
        };
        by_slot.entry(key).or_default().push(serde_json::json!({
            "multiplier_choice": r.multiplier_choice,
            "pulls": r.pulls,
            "mean_reward": mean,
            "linucb_score": r.linucb_score,
        }));
    }
    by_slot
        .into_iter()
        .map(|((domain, bucket), arms)| {
            serde_json::json!({
                "island_domain": domain,
                "strength_bucket": bucket,
                "arms": arms,
            })
        })
        .collect()
}

/// Convert the flat per-arm snapshot into a per-slot rollup with the
/// 5 multiplier_choice arms inlined. Cuts JSON size from
/// O(rows × ~40 B) to O(slots × ~120 B) — ~120 slots × 120 B ≈ 14 KB
/// plain, ~5 KB after the existing CompressionLayer.
fn directive_arms_compact(snap: &DirectiveArmsSnapshot) -> Vec<serde_json::Value> {
    use std::collections::BTreeMap;
    type SlotKey = (String, String, i16);
    let mut by_slot: BTreeMap<SlotKey, Vec<serde_json::Value>> = BTreeMap::new();
    for r in &snap.arms {
        let key = (r.island_domain.clone(), r.action.clone(), r.strength_bucket);
        let mean = if r.pulls > 0 {
            r.total_reward / r.pulls as f64
        } else {
            0.0
        };
        by_slot.entry(key).or_default().push(serde_json::json!({
            "multiplier_choice": r.multiplier_choice,
            "pulls": r.pulls,
            "mean_reward": mean,
            "linucb_score": r.linucb_score,
        }));
    }
    by_slot
        .into_iter()
        .map(|((domain, action, bucket), arms)| {
            serde_json::json!({
                "island_domain": domain,
                "action": action,
                "strength_bucket": bucket,
                "arms": arms,
            })
        })
        .collect()
}

/// How long a serialised /api/seed response stays valid in cache. The
/// AxiomStore only changes via /api/admin/reload_corpus (which busts
/// the cache) and the verified-recent index ticks roughly every chunk
/// (60s). 30s is a safe middle ground: workers polling at 60s cadence
/// hit fresh data on alternating polls.
const SEED_CACHE_TTL: Duration = Duration::from_secs(30);

#[derive(Deserialize)]
pub struct SeedQuery {
    pub domain: Option<String>,
    pub top: Option<u64>,
}

/// `GET /api/seed?domain=X&top=N` — bootstrap payload for a remote worker.
///
/// Honors `If-None-Match` / `ETag` for 304 conditional requests so
/// 1000-worker polling doesn't transfer 13MB JSON every chunk
/// boundary — most polls hit 304 with empty body. The ETag is the
/// xxhash64 of the cached body, so any change to the AxiomStore or
/// the LakeVerified set busts it.
pub async fn seed(
    State(state): State<Arc<AppState>>,
    Query(q): Query<SeedQuery>,
    headers: HeaderMap,
) -> impl IntoResponse {
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
    let top = q.top.unwrap_or(50).min(500);

    // ── Cache hit fast path ───────────────────────────────────────────
    // Most workers re-poll /api/seed at chunk boundaries with the same
    // (domain, top). Skip the entire axiom-store iteration + verified-
    // recent fetch + JSON serialise if we have a fresh cached body.
    // Cache invalidation: /api/admin/reload_corpus clears the map after
    // hot-reloading the AxiomStore.
    let cache_key = SeedCacheKey {
        domain: q.domain.clone(),
        top,
    };
    if let Ok(map) = state.seed_cache.lock() {
        if let Some((generated_at, body)) = map.get(&cache_key) {
            if generated_at.elapsed() < SEED_CACHE_TTL {
                let etag = format!("\"{:016x}\"", xxhash_rust::xxh64::xxh64(body.as_bytes(), 0));
                // Conditional request fast path: client sent
                // If-None-Match matching our ETag → 304 + empty body.
                if let Some(client_etag) = headers
                    .get(axum::http::header::IF_NONE_MATCH)
                    .and_then(|v| v.to_str().ok())
                {
                    if client_etag == etag {
                        return (
                            StatusCode::NOT_MODIFIED,
                            [
                                (axum::http::header::ETAG, etag.clone()),
                                (
                                    axum::http::header::CACHE_CONTROL,
                                    "public, max-age=30, stale-while-revalidate=300".to_string(),
                                ),
                            ],
                        )
                            .into_response();
                    }
                }
                return (
                    StatusCode::OK,
                    [
                        (axum::http::header::CONTENT_TYPE, "application/json".to_string()),
                        (axum::http::header::ETAG, etag),
                        (
                            axum::http::header::CACHE_CONTROL,
                            "public, max-age=30, stale-while-revalidate=300".to_string(),
                        ),
                    ],
                    body.as_bytes().to_vec(),
                )
                    .into_response();
            }
        }
    }

    // Axioms from the in-memory AxiomStore. Domain filter accepts either the
    // Display form ("special_relativity") or the Rust enum name
    // ("SpecialRelativity") so callers can use whichever convention their
    // local DSL prefers.
    let domain_filter = q.domain.clone();
    let store = state.axiom_store.load();
    let axioms: Vec<serde_json::Value> = store
        .iter()
        .filter(|a| {
            domain_filter.as_ref().is_none_or(|d| {
                let dom_dbg = format!("{:?}", a.domain);
                let dom_disp = format!("{}", a.domain);
                dom_dbg == *d || dom_disp == *d
            })
        })
        .map(|a| {
            // Expr has no Display impl; serialise to JSON so a worker can
            // round-trip it back into an Expr tree. Falls back to the Rust
            // Debug form on the (unreachable) serde failure.
            let statement = serde_json::to_string(&a.statement)
                .unwrap_or_else(|_| format!("{:?}", a.statement));
            serde_json::json!({
                "name": a.name,
                "statement": statement,
                "domain": format!("{}", a.domain),
                "description": a.description,
            })
        })
        .collect();

    // Seed theorems: top-N Verified, newest-first. RocksDB-primary
    // (Task 4): the verified-at index is populated by `flip_verified`
    // every time a theorem flips to Verified, so this returns the same
    // data PG would but ~10× faster (RocksDB indexed scan vs. PG row
    // fetch). Falls back to PG when the RocksDB index is empty so
    // legacy data still surfaces during the rollout window.
    let _ = pg; // PG kept for the legacy fallback below.
    let mut seed_theorems: Vec<serde_json::Value> = Vec::new();
    // P-Task 12 propagation policy:
    //   - "lake_build"   → server kernel-confirmed (gold standard).
    //   - "worker_claim" → worker locally lake-built before submitting
    //                      AND chain replay regenerated the canonical.
    //                      99.9999%-true under the trust-but-verify
    //                      model: server still queues a redundant lake
    //                      build (P-Task 2 drain), but propagation does
    //                      not block on it.
    //   - "chain_replay" → unverified at the kernel level; absent from
    //                      seed. The pollution risk for these is real
    //                      (chain replay is sound only over the audited
    //                      AxiomStore + rule library), so we still gate
    //                      them behind lake promotion before allowing
    //                      peer-axiom composition.
    //
    // Pull a wider window than `top` from the recency index so we can
    // afford to skip chain_replay-only rows without thinning the
    // response.
    let scan_window = (top as usize).saturating_mul(8).max(top as usize);
    if let Ok(ids) = state.db.list_verified_recent_ids(scan_window) {
        for id in ids {
            if seed_theorems.len() >= top as usize {
                break;
            }
            if let Ok(Some(theorem)) = state.db.get_theorem(&id) {
                // Accept lake_build (gold) and worker_claim (worker lake
                // build + chain replay agreed). Reject chain_replay-only.
                let propagatable = matches!(
                    &theorem.verified,
                    nasrudin_core::VerificationStatus::Verified { tactic_used, .. }
                        if tactic_used == "lake_build" || tactic_used == "worker_claim"
                );
                if !propagatable {
                    // Side effect: enqueue this chain_replay theorem
                    // for lake promotion at priority 1 (seed-inclusion
                    // demand). The /api/seed endpoint heating up the
                    // promotion queue means workers polling create
                    // pressure to graduate the freshest theorems first.
                    if let nasrudin_core::VerificationStatus::Verified { tactic_used, .. }
                        = &theorem.verified
                    {
                        if tactic_used == "chain_replay" {
                            let _ = state.db.enqueue_lake_promotion(&id, 1);
                        }
                    }
                    continue;
                }
                if let Some(ref d) = q.domain {
                    let dom_disp = format!("{}", theorem.domain);
                    let dom_dbg = format!("{:?}", theorem.domain);
                    if dom_disp != *d && dom_dbg != *d {
                        continue;
                    }
                }
                seed_theorems.push(
                    serde_json::to_value(&theorem)
                        .unwrap_or_else(|_| serde_json::Value::Null),
                );
            }
        }
    }
    if seed_theorems.is_empty() {
        match nasrudin_pg::query::theorems::list_verified(
            pg,
            None,
            top,
            q.domain.clone(),
        )
        .await
        {
            Ok(page) => {
                seed_theorems = page
                    .items
                    .into_iter()
                    .map(|m| {
                        serde_json::to_value(&m).unwrap_or_else(|_| serde_json::Value::Null)
                    })
                    .collect();
            }
            Err(e) => {
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(serde_json::json!({
                        "error": format!("seed_query_failed: {e}")
                    })),
                )
                    .into_response();
            }
        }
    }

    // Fold in the live cluster steering snapshot so workers hot-reload
    // the LLM's mutation knobs + domain weights without a separate
    // poll. cluster_config is a sibling field — it ships the bandit's
    // chosen K per island so workers know how many clusters to k-means
    // each chunk. Both are versioned via independent etags.
    let steering_snap = state.steering.load();
    let cc_snap = state.cluster_config.load();
    let arms_snap = state.directive_arms.load();
    let compute_snap = state.compute_arms.load();
    let body = serde_json::json!({
        "axioms": axioms,
        "seed_theorems": seed_theorems,
        "steering": {
            "config": steering_snap.config,
            "etag": format!("{:016x}", steering_snap.etag),
            "started_at": steering_snap.started_at.to_rfc3339(),
        },
        "cluster_config": {
            "k_per_island": cc_snap.k_per_island,
            "etag": format!("{:016x}", cc_snap.etag),
        },
        "directive_arms": {
            "snapshot": directive_arms_compact(&arms_snap),
            "etag": format!("{:016x}", arms_snap.etag),
        },
        "compute_arms": {
            "snapshot": compute_arms_compact(&compute_snap),
            "etag": format!("{:016x}", compute_snap.etag),
        },
    });
    let body_str = serde_json::to_string(&body)
        .unwrap_or_else(|_| r#"{"error":"serialise_failed"}"#.to_string());
    let body_arc = Arc::new(body_str);
    if let Ok(mut map) = state.seed_cache.lock() {
        map.insert(cache_key, (Instant::now(), Arc::clone(&body_arc)));
    }
    let etag = format!("\"{:016x}\"", xxhash_rust::xxh64::xxh64(body_arc.as_bytes(), 0));
    (
        StatusCode::OK,
        [
            (axum::http::header::CONTENT_TYPE, "application/json".to_string()),
            (axum::http::header::ETAG, etag),
            (
                axum::http::header::CACHE_CONTROL,
                "public, max-age=30, stale-while-revalidate=300".to_string(),
            ),
        ],
        body_arc.as_bytes().to_vec(),
    )
        .into_response()
}
