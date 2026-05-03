//! `GET /api/theorems`, `…/recent`, `…/{id}`, `…/{hash}/lean`.
//!
//! Phase 9 / Task 5.1. All four read endpoints serve directly out of the
//! PostgreSQL `theorems` mirror (see `nasrudin_pg::query::theorems`) so the
//! frontend always sees the canonical "verified + persisted" view rather than
//! the in-flight RocksDB row, which can include `Pending` and `Rejected`
//! statuses.
//!
//! When PostgreSQL is not configured the daemon still boots, but every
//! endpoint here returns `503 Service Unavailable` with `error =
//! "pg_unavailable"` — making it a soft failure mode that the frontend can
//! detect and degrade gracefully.

use axum::{
    Json,
    extract::{Path, Query, State},
    http::{StatusCode, header},
    response::IntoResponse,
};
use serde::Deserialize;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

use crate::state::AppState;
use nasrudin_pg::query::theorems;

/// 30-second TTL cache for `GET /api/theorems/recent`. Keyed on
/// `(limit, domain)`; cursor is always None on this endpoint. The
/// frontend's React Query staleTime + polling cadence is already 60 s,
/// so the user-visible freshness is unchanged while we collapse hot
/// traffic into one PG round-trip per (limit, domain) pair.
const RECENT_TTL: Duration = Duration::from_secs(30);
/// Hard cap on cache entries — cache_key is `(limit_bucket, Option<domain>)`
/// and a small handful of (limit, domain) combos covers >99 % of traffic.
const RECENT_MAX_ENTRIES: usize = 64;

/// Cache key for the `/api/theorems/recent` response. The trailing two
/// bools track the `include_rejected` and `include_internal` query flags
/// so admin- and toggle-driven variants of the response don't share cache
/// entries with the public default.
type RecentKey = (u64, Option<String>, bool, bool);

/// Per-(limit, domain) cached response body. `Arc<String>` so cache hits
/// avoid both PG and re-serialisation.
#[derive(Default)]
pub struct TheoremsRecentCache {
    inner: RwLock<HashMap<RecentKey, (Instant, Arc<String>)>>,
}

impl TheoremsRecentCache {
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(HashMap::new()),
        }
    }

    async fn get_fresh(&self, key: &RecentKey) -> Option<Arc<String>> {
        let g = self.inner.read().await;
        g.get(key).and_then(|(ts, body)| {
            (ts.elapsed() < RECENT_TTL).then(|| body.clone())
        })
    }

    async fn store(&self, key: RecentKey, body: Arc<String>) {
        let mut g = self.inner.write().await;
        // Bound entries; on overflow drop expired or arbitrary entries.
        if g.len() >= RECENT_MAX_ENTRIES {
            g.retain(|_, (ts, _)| ts.elapsed() < RECENT_TTL);
            if g.len() >= RECENT_MAX_ENTRIES {
                if let Some(k) = g.keys().next().cloned() {
                    g.remove(&k);
                }
            }
        }
        g.insert(key, (Instant::now(), body));
    }
}

/// Query params shared by `list` and `recent`. `recent` ignores `cursor`.
///
/// `include_rejected` surfaces `status = 'Rejected'` rows (off by default —
/// most viewers don't want failed candidates in their feed). `include_internal`
/// surfaces `verification_tactic = 'chain_replay'` rows (no Lean kernel has
/// touched them yet) and is honored only when the request authenticates as
/// admin via `RequireAdmin`; otherwise silently ignored.
#[derive(Deserialize)]
pub struct ListQuery {
    pub limit: Option<u64>,
    pub cursor: Option<String>,
    pub domain: Option<String>,
    #[serde(default)]
    pub include_rejected: bool,
    #[serde(default)]
    pub include_internal: bool,
}

/// `GET /api/theorems` — cursor-paginated `Verified` list, newest-first.
///
/// Returns `{ theorems, next_cursor, total, total_capped }`. `total` is
/// COUNT(*) capped at 10 000; when the true count exceeds that, `total_capped`
/// is `true` so the UI can render "10,000+" without lying.
pub async fn list(
    State(state): State<Arc<AppState>>,
    admin: Option<crate::admin::require_admin::RequireAdmin>,
    Query(q): Query<ListQuery>,
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
    let limit = q.limit.unwrap_or(50).min(500);
    let opts = nasrudin_pg::query::theorems::ListOptions {
        include_rejected: q.include_rejected,
        // Honored only for admins so a crafted query string can't leak
        // chain_replay (no-Lean-kernel) rows to the public.
        include_internal: q.include_internal && admin.is_some(),
    };
    match theorems::list_verified(pg, q.cursor, limit, q.domain, opts).await {
        Ok(page) => (
            StatusCode::OK,
            Json(serde_json::json!({
                "theorems": page.items,
                "next_cursor": page.next_cursor,
                "total": page.total,
                "total_capped": page.total_capped,
            })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

/// `GET /api/theorems/recent` — same query shape as `list` but the cursor
/// param is dropped before the DB call so it always returns the newest page.
/// 30 s TTL cache keyed on `(limit, domain, include_rejected, include_internal)`.
pub async fn recent(
    State(state): State<Arc<AppState>>,
    admin: Option<crate::admin::require_admin::RequireAdmin>,
    Query(q): Query<ListQuery>,
) -> impl IntoResponse {
    let limit = q.limit.unwrap_or(50).min(500);
    let include_rejected = q.include_rejected;
    let include_internal = q.include_internal && admin.is_some();
    let cache_key: RecentKey = (limit, q.domain.clone(), include_rejected, include_internal);

    if let Some(body) = state.theorems_recent_cache.get_fresh(&cache_key).await {
        return (
            StatusCode::OK,
            [(header::CONTENT_TYPE, "application/json")],
            body.as_bytes().to_vec(),
        )
            .into_response();
    }

    let Some(pg) = &state.pg else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "pg_unavailable" })),
        )
            .into_response();
    };

    let opts = nasrudin_pg::query::theorems::ListOptions {
        include_rejected,
        include_internal,
    };
    match theorems::list_verified(pg, None, limit, q.domain, opts).await {
        Ok(page) => {
            let payload = serde_json::json!({
                "theorems": page.items,
                "next_cursor": page.next_cursor,
                "total": page.total,
                "total_capped": page.total_capped,
            });
            let body = serde_json::to_string(&payload).unwrap_or_else(|_| "{}".to_string());
            let body_arc = Arc::new(body);
            state
                .theorems_recent_cache
                .store(cache_key, body_arc.clone())
                .await;
            (
                StatusCode::OK,
                [(header::CONTENT_TYPE, "application/json")],
                body_arc.as_bytes().to_vec(),
            )
                .into_response()
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

/// `GET /api/theorems/{id}` — fetch one theorem by its 8-byte hex id.
///
/// `id` must be 16 hex chars. Anything malformed → 400; not found → 404.
pub async fn by_id(
    State(state): State<Arc<AppState>>,
    Path(id): Path<String>,
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
    let id_bytes = match hex::decode(&id) {
        Ok(b) => b,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": "bad_id" })),
            )
                .into_response();
        }
    };
    match theorems::get_by_id(pg, &id_bytes).await {
        Ok(Some(t)) => (StatusCode::OK, Json(t)).into_response(),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not_found" })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

/// `GET /api/theorems/{hash}/lean` — download the Lean source for a verified
/// theorem as `text/plain` with a `Content-Disposition: attachment` filename.
///
/// `hash` is the 8-byte canonical hash hex-encoded — the same identity the
/// frontend uses to dedupe rows, distinct from the primary-key `id` used by
/// `by_id` even though in Phase 9 they happen to be the same value.
pub async fn lean_download(
    State(state): State<Arc<AppState>>,
    Path(hash): Path<String>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    let hash_bytes = match hex::decode(&hash) {
        Ok(b) => b,
        Err(_) => return (StatusCode::BAD_REQUEST, "bad_hash").into_response(),
    };

    // P-Task 1+2+12: download is a "consumption" trigger that demands
    // the server's own kernel guarantee. Anything not yet flipped to
    // `lake_build` (chain_replay or worker_claim) gets a synchronous
    // priority-0 lake-promotion. worker_claim still needs server-side
    // confirmation here because the .lean is the artifact the caller
    // will cite — a malicious worker that lied about local lake-build
    // would be caught at this gate before any external citation
    // touches the source.
    //
    // - If lake_build: serve immediately.
    // - If chain_replay or worker_claim: enqueue at priority 0, park
    //   up to 60s on the per-id Notify. On lake success, serve. On
    //   lake failure, the drain has already run cascade-reject; return
    //   410 Gone.
    // - On wait timeout (lake genuinely takes >60s): 202 Accepted with
    //   Retry-After header.
    let mut id_arr = [0u8; 8];
    if hash_bytes.len() == 8 {
        id_arr.copy_from_slice(&hash_bytes);
    }
    let needs_promotion = matches!(
        state.db.get_theorem(&id_arr).ok().flatten().map(|t| t.verified),
        Some(nasrudin_core::VerificationStatus::Verified { tactic_used, .. })
            if tactic_used == "chain_replay" || tactic_used == "worker_claim"
    );
    if needs_promotion {
        if let Some(promotion) = state.lake_promotion.as_ref() {
            match promotion
                .await_promotion(id_arr, std::time::Duration::from_secs(60))
                .await
            {
                Ok(Some(nasrudin_core::VerificationStatus::Verified { tactic_used, .. }))
                    if tactic_used == "lake_build" =>
                {
                    // Continue to PG fetch + serve below.
                }
                Ok(Some(nasrudin_core::VerificationStatus::Rejected { reason })) => {
                    return (
                        StatusCode::GONE,
                        format!("rejected: {reason}"),
                    )
                        .into_response();
                }
                _ => {
                    return (
                        StatusCode::ACCEPTED,
                        [(header::RETRY_AFTER, "60".to_string())],
                        "lake_promotion_in_flight",
                    )
                        .into_response();
                }
            }
        }
    }

    match theorems::get_by_canonical_hash(pg, &hash_bytes).await {
        Ok(Some(t)) => {
            let filename = format!("theorem_{}.lean", hex::encode(&t.canonical_hash));
            let cd = format!("attachment; filename=\"{filename}\"");
            (
                StatusCode::OK,
                [
                    (header::CONTENT_TYPE, "text/plain; charset=utf-8".to_string()),
                    (header::CONTENT_DISPOSITION, cd),
                ],
                t.lean_source,
            )
                .into_response()
        }
        Ok(None) => (StatusCode::NOT_FOUND, "not_found").into_response(),
        Err(_) => (StatusCode::INTERNAL_SERVER_ERROR, "db_error").into_response(),
    }
}


/// `GET /api/rejected_hashes` — list of canonical_hash bytes for every
/// theorem in the `Rejected` state. Workers pull this at startup (and
/// periodically) so they can skip any chain whose final canonical
/// matches a known-rejected hash, instead of handing it to lake-build
/// just to fail again.
///
/// Response: `{ hashes: [[<8 bytes>], …], count: N }`. Hashes are
/// serialized as JSON arrays of byte numbers (matches SeaORM's default
/// Vec<u8> serde, same convention as Theorem.id and canonical_hash).
pub async fn rejected_hashes(
    State(state): State<Arc<AppState>>,
) -> impl IntoResponse {
    // RocksDB-primary (Task 4): scan CF_THEOREMS for `Rejected` /
    // `Timeout` rows. Cap at 100k. Each hash is 8 bytes, so the wire
    // response stays under 1 MB even at the cap. PG is no longer
    // queried — the RocksDB Theorem rows are the source of truth for
    // negative-result memory now that ingest is RocksDB-primary.
    match state.db.list_rejected_canonical_hashes(100_000) {
        Ok(ids) => {
            // Wire shape: list of 8-byte arrays. Each TheoremId already
            // == canonical_hash in Phase 9 (theorem_id_from_canonical),
            // so the bytes ARE the canonical hash.
            let hashes: Vec<Vec<u8>> = ids.into_iter().map(|id| id.to_vec()).collect();
            let count = hashes.len();
            (
                StatusCode::OK,
                Json(serde_json::json!({ "hashes": hashes, "count": count })),
            )
                .into_response()
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        )
            .into_response(),
    }
}
