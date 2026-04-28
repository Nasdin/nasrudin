//! `POST /api/ingest` — public worker submission endpoint.
//!
//! Phase 9 / Task 4.2.
//!
//! # Request flow
//!
//! 1. **Bearer auth.** The `WorkerAuth` extractor (Task 4.3) parses the
//!    `Authorization: Bearer nsk_worker_…` header, looks up the api-key in
//!    PostgreSQL, verifies the Argon2 hash, and rejects any non-worker key
//!    kinds. After extraction we additionally enforce that
//!    `auth.worker_handle == batch.worker_id` — a worker cannot submit on
//!    behalf of another worker.
//! 2. **Per-worker rate limit.** Consumes `theorems.len()` tokens from the
//!    keyed `WorkerRateLimiter` (default 60/min). Failure → 429 for the entire
//!    batch.
//! 3. **Global queue-depth throttle.** If `reverify_queue_depth > 200` we
//!    refuse the whole batch with 503; the worker should retry after the
//!    backlog drains.
//! 4. **Per-theorem pipeline.** For each item:
//!    a. Size guards: `lean_source` ≤ 256 KiB, `chain` ≤ 64 steps.
//!    b. Pre-flight axiom/sorry firewall (rejects fake-via-axiom proofs).
//!    c. Dedup against Postgres by `canonical_hash`. If found → `Duplicate`.
//!    d. INSERT `Pending` row, then best-effort `enqueue_reverify` +
//!       `theorem_pending` SSE broadcast.
//!
//! Per-theorem response is one of `Pending`, `Duplicate`, or `Rejected`. The
//! whole call returns `202 Accepted` so a partial-failure batch still drains
//! the successful items into the queue.
//!
//! # Race window (acceptable for Phase 9)
//!
//! The dedup SELECT and the INSERT are not atomic — two concurrent requests
//! for the same `canonical_hash` could both pass the SELECT and both attempt
//! the INSERT. The PostgreSQL `UNIQUE(canonical_hash)` constraint is the
//! backstop: the second INSERT fails, we return `Rejected{insert_db_error}`
//! and the worker can retry → second time the dedup branch will pick up the
//! existing row and return `Duplicate`. Documented here rather than fixed
//! because the cost is one extra round trip on a rare race; a real fix would
//! either advisory-lock per hash or use `INSERT … ON CONFLICT DO NOTHING
//! RETURNING …`.

use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::{auth::WorkerAuth, lake_builder::preflight_axiom_or_sorry, state::AppState};
use nasrudin_pg::query::theorems;
use nasrudin_rocks::ReverifyJob;

/// Reject batches when the reverify queue holds more than this many jobs.
/// Workers see 503 and back off until the drain catches up.
const QUEUE_DEPTH_THROTTLE: usize = 200;
/// Hard upper bound on a submitted Lean source body (256 KiB). Anything
/// larger almost certainly indicates a runaway emitter or worker bug.
const MAX_LEAN_SOURCE_BYTES: usize = 256 * 1024;
/// Hard upper bound on chain length (number of derivation steps).
const MAX_CHAIN_STEPS: usize = 64;

/// Top-level batch payload posted by a worker.
#[derive(Deserialize)]
pub struct IngestBatch {
    pub worker_id: String,
    pub engine_git_sha: String,
    pub lean_version: String,
    pub theorems: Vec<IngestTheorem>,
}

/// One theorem inside an ingest batch. Required: `canonical_statement`,
/// `domain`, `lean_source`, `chain`, `axioms_used`. Everything else is
/// `Option<...>`.
#[derive(Deserialize, Clone)]
pub struct IngestTheorem {
    pub canonical_statement: String,
    pub latex: Option<String>,
    pub domain: String,
    pub lean_source: String,
    pub chain: serde_json::Value,
    pub axioms_used: Vec<String>,
    pub parents: Option<Vec<String>>,
    pub origin: Option<serde_json::Value>,
    pub depth: Option<u32>,
    pub complexity: Option<u32>,
    pub generation: Option<u64>,
    pub fitness: Option<serde_json::Value>,
    pub verification_tactic: Option<String>,
    pub verification_duration_ms: Option<u32>,
    pub dimension: Option<[i32; 7]>,
}

/// Per-theorem outcome variants. Tagged `kind` on the wire.
#[derive(Serialize)]
#[serde(tag = "kind")]
pub enum IngestStatus {
    /// Inserted as Pending; queued for reverification.
    Pending,
    /// `canonical_hash` already exists; the existing row's status is reported.
    Duplicate { existing_status: String },
    /// Pre-flight, schema, or DB error blocked insertion.
    Rejected { reason: String },
}

/// One element of the per-theorem result array.
#[derive(Serialize)]
pub struct IngestResultItem {
    pub theorem_id: String,
    pub canonical_hash: String,
    pub status: IngestStatus,
}

/// Top-level response body returned with `202 Accepted`.
#[derive(Serialize)]
pub struct IngestResponse {
    pub results: Vec<IngestResultItem>,
}

/// `POST /api/ingest` handler.
///
/// See module-level docs for the full request flow + race-window discussion.
pub async fn ingest(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Json(batch): Json<IngestBatch>,
) -> axum::response::Response {
    // === Bearer auth (WorkerAuth extractor — Task 4.3) ===
    // The extractor already enforced: header present, `nsk_worker_` prefix,
    // row exists in `api_keys`, kind == "worker", Argon2 hash verified.
    // Additionally enforce that the worker can only ingest as itself.
    if auth.0.worker_handle != batch.worker_id {
        return (
            StatusCode::FORBIDDEN,
            Json(serde_json::json!({ "error": "worker_id_mismatch" })),
        )
            .into_response();
    }

    // === Per-worker rate limit ===
    let n = batch.theorems.len() as u32;
    if state
        .worker_rate_limiter
        .check_and_consume(&batch.worker_id, n)
        .is_err()
    {
        return (
            StatusCode::TOO_MANY_REQUESTS,
            Json(serde_json::json!({ "error": "rate_limited" })),
        )
            .into_response();
    }

    // === Global queue depth throttle ===
    if state.db.reverify_queue_depth().unwrap_or(0) > QUEUE_DEPTH_THROTTLE {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "queue_full" })),
        )
            .into_response();
    }

    // === PostgreSQL required ===
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

    let mut results = Vec::with_capacity(batch.theorems.len());
    for t in &batch.theorems {
        // ── Per-theorem size guards ───────────────────────────────────────
        if t.lean_source.len() > MAX_LEAN_SOURCE_BYTES {
            results.push(reject_item("", "", "too_large"));
            continue;
        }
        if let Some(arr) = t.chain.as_array() {
            if arr.len() > MAX_CHAIN_STEPS {
                results.push(reject_item("", "", "too_complex"));
                continue;
            }
        }

        // ── Pre-flight axiom/sorry firewall ───────────────────────────────
        if let Err(reason) = preflight_axiom_or_sorry(&t.lean_source) {
            results.push(reject_item("", "", reason));
            continue;
        }

        let canonical_hash = nasrudin_core::canonical_hash(&t.canonical_statement);
        // theorem_id == canonical_hash in Phase 9 (see core::theorem_id_from_canonical).
        let theorem_id = canonical_hash.clone();
        let id_hex = hex::encode(&theorem_id);
        let hash_hex = hex::encode(&canonical_hash);

        // ── Dedup against Postgres ────────────────────────────────────────
        match theorems::get_by_canonical_hash(pg, &canonical_hash).await {
            Ok(Some(existing)) => {
                results.push(IngestResultItem {
                    theorem_id: hex::encode(&existing.id),
                    canonical_hash: hex::encode(&existing.canonical_hash),
                    status: IngestStatus::Duplicate {
                        existing_status: existing.status,
                    },
                });
                continue;
            }
            Ok(None) => {}
            Err(e) => {
                results.push(IngestResultItem {
                    theorem_id: id_hex.clone(),
                    canonical_hash: hash_hex.clone(),
                    status: IngestStatus::Rejected {
                        reason: format!("dedup_db_error: {e}"),
                    },
                });
                continue;
            }
        }

        // ── Build NewTheorem ──────────────────────────────────────────────
        let parents_bytes: Option<Vec<Vec<u8>>> = t.parents.as_ref().map(|ps| {
            ps.iter()
                .filter_map(|p| hex::decode(p).ok())
                .collect()
        });
        let origin_kind = t
            .origin
            .as_ref()
            .and_then(|v| v.get("type").and_then(|x| x.as_str()).map(String::from))
            .unwrap_or_else(|| "Axiom".to_string());

        let new_row = theorems::NewTheorem {
            id: theorem_id.clone(),
            canonical_hash: canonical_hash.clone(),
            canonical_statement: t.canonical_statement.clone(),
            latex: t.latex.clone(),
            lean_source: t.lean_source.clone(),
            domain: t.domain.clone(),
            axioms_used: t.axioms_used.clone(),
            chain_json: t.chain.clone(),
            parents: parents_bytes,
            origin_kind,
            origin_payload: t.origin.clone(),
            depth: t.depth.map(|x| x as i32),
            complexity: t.complexity.map(|x| x as i32),
            generation: t.generation.map(|x| x as i64),
            fitness_novelty: extract_fitness(&t.fitness, "novelty"),
            fitness_compactness: extract_fitness(&t.fitness, "compactness"),
            fitness_dimensional_correctness: extract_fitness(
                &t.fitness,
                "dimensional_correctness",
            ),
            fitness_domain_coverage: extract_fitness(&t.fitness, "domain_coverage"),
            fitness_axiom_efficiency: extract_fitness(&t.fitness, "axiom_efficiency"),
            fitness_nasrudin_relevance: extract_fitness(&t.fitness, "nasrudin_relevance"),
            fitness_depth_score: extract_fitness(&t.fitness, "depth"),
            dimension: t.dimension.map(|d| d.to_vec()),
            engine_git_sha: batch.engine_git_sha.clone(),
            lean_version: batch.lean_version.clone(),
            contributor_id: batch.worker_id.clone(),
        };

        // ── INSERT(Pending) + best-effort enqueue + SSE broadcast ─────────
        match theorems::insert_pending(pg, new_row).await {
            Ok(id_bytes) => {
                let mut id_arr = [0u8; 8];
                if id_bytes.len() == 8 {
                    id_arr.copy_from_slice(&id_bytes);
                }
                // Best-effort: enqueue failure shouldn't fail the whole result.
                // The drain loop won't pick it up but the row is still in PG;
                // an operator can re-enqueue manually.
                let _ = state.db.enqueue_reverify(&ReverifyJob {
                    theorem_id: id_arr,
                    attempts: 0,
                    enqueued_at_micros: chrono::Utc::now().timestamp_micros(),
                });
                let _ = state
                    .reverify_event_tx
                    .send(crate::reverify::DiscoveryEvent::TheoremPending {
                        theorem_id: id_hex.clone(),
                        canonical: t.canonical_statement.clone(),
                        contributor_id: batch.worker_id.clone(),
                    });
                results.push(IngestResultItem {
                    theorem_id: id_hex,
                    canonical_hash: hash_hex,
                    status: IngestStatus::Pending,
                });
            }
            Err(e) => {
                results.push(IngestResultItem {
                    theorem_id: id_hex,
                    canonical_hash: hash_hex,
                    status: IngestStatus::Rejected {
                        reason: format!("insert_db_error: {e}"),
                    },
                });
            }
        }
    }

    (StatusCode::ACCEPTED, Json(IngestResponse { results })).into_response()
}

/// Build a `Rejected` result item with empty IDs, used for theorems that
/// failed validation before we hashed their canonical statement.
fn reject_item(theorem_id: &str, canonical_hash: &str, reason: &str) -> IngestResultItem {
    IngestResultItem {
        theorem_id: theorem_id.to_string(),
        canonical_hash: canonical_hash.to_string(),
        status: IngestStatus::Rejected {
            reason: reason.to_string(),
        },
    }
}

/// Pull a single fitness component out of the optional JSON object the worker
/// sent (or `None` if the key is missing / wrong type).
fn extract_fitness(fitness: &Option<serde_json::Value>, key: &str) -> Option<f32> {
    fitness
        .as_ref()
        .and_then(|f| f.get(key))
        .and_then(|v| v.as_f64())
        .map(|x| x as f32)
}
