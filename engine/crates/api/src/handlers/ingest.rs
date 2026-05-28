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

use axum::{
    Extension, Json,
    extract::State,
    http::StatusCode,
    response::IntoResponse,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::{
    auth::WorkerAuth,
    lake_builder::preflight_axiom_or_sorry,
    state::AppState,
    trust::{LocalSocket, TrustDecision},
};
use nasrudin_pg::query::theorems;
use nasrudin_rocks::ReverifyJob;

/// Reject batches when the reverify queue holds more than this many jobs.
/// Workers see 503 and back off until the drain catches up.
///
/// **Tuned for the discovery-rate target.** The user-set goal is
/// ≥1 verified theorem per 6h. At a default `submit_unverified_top_k = 4`
/// across N workers, the unverified-submission stream can briefly burst
/// to a few hundred jobs. Bound was 200; raised to 1000 so a moderate
/// fleet of workers doesn't trip 503s while the chain-replay drain is
/// catching up. Override via `NASRUDIN_INGEST_QUEUE_THROTTLE` — if the
/// drain is genuinely stuck the operator should investigate, not just
/// raise the bound further.
fn queue_depth_throttle() -> usize {
    std::env::var("NASRUDIN_INGEST_QUEUE_THROTTLE")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(1000)
}
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
    /// **P-Task 12:** the worker locally lake-built this Lean source
    /// before submitting and confirmed it kernel-verifies. When set,
    /// the server's reverify drain treats chain-replay success as
    /// sufficient to flip the row directly to LakeVerified — the
    /// theorem is immediately available as a peer-axiom in /api/seed
    /// without waiting for a separate lake-promotion step.
    ///
    /// The lazy lake-build on `/api/theorems/{id}/lean` (download)
    /// remains as defense-in-depth: it re-runs lake against the
    /// stored source, and on disagreement triggers cascade-reject +
    /// reputation-tank for the submitter.
    ///
    /// Honest workers running a stock binary set this to true.
    /// A bad actor who lies about it gets caught the moment any user
    /// downloads the .lean file (the lazy lake catches forged claims).
    #[serde(default)]
    pub worker_verified: bool,
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
    local_socket: Option<Extension<LocalSocket>>,
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
    if state.db.reverify_queue_depth().unwrap_or(0) > queue_depth_throttle() {
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

    // === Trust resolution ===
    // Cache hit: skip the DB lookup. Cache miss: load the api_key row,
    // call trust::resolve, store the decision. The cache invalidation
    // listener (main.rs) drops entries when admins change trust state.
    let via_unix_socket = local_socket.is_some();
    let key_id = auth.0.api_key_id;
    let decision = if let Some(d) = state.trust_cache.get(&key_id) {
        d
    } else {
        use sea_orm::EntityTrait;
        let key_row = nasrudin_pg::entity::api_keys::Entity::find_by_id(key_id)
            .one(pg)
            .await
            .ok()
            .flatten();
        let d = crate::trust::resolve(
            pg,
            key_row.as_ref(),
            via_unix_socket,
            state.trusted_spot_check_rate,
        )
        .await
        .unwrap_or_else(|_| crate::trust::TrustDecision {
            trusted: false,
            spot_check_rate: state.trusted_spot_check_rate,
            source: crate::trust::TrustSource::Default,
        });
        state.trust_cache.put(key_id, d.clone());
        d
    };

    let mut results = Vec::with_capacity(batch.theorems.len());
    for t in &batch.theorems {
        let item = ingest_one_theorem(
            &state,
            &batch.worker_id,
            &batch.engine_git_sha,
            &batch.lean_version,
            t,
            &decision,
        )
        .await;
        results.push(item);
    }

    // PG handle is unused on the hot path — write-behind via pg_drain.
    let _ = pg;

    (StatusCode::ACCEPTED, Json(IngestResponse { results })).into_response()
}

/// Per-theorem pipeline shared by `POST /api/ingest` (batch) and
/// `POST /api/conjecture/{id}/submit` (one). Runs size guards →
/// axiom/sorry firewall → RocksDB dedup → primary-write + write-behind
/// PG enqueue → SSE broadcast → reverify enqueue. Returns the per-item
/// outcome (Pending / Duplicate / Rejected).
pub async fn ingest_one_theorem(
    state: &Arc<AppState>,
    worker_id: &str,
    engine_git_sha: &str,
    lean_version: &str,
    t: &IngestTheorem,
    decision: &TrustDecision,
) -> IngestResultItem {
    if t.lean_source.len() > MAX_LEAN_SOURCE_BYTES {
        return reject_item("", "", "too_large");
    }
    if let Some(arr) = t.chain.as_array() {
        if arr.len() > MAX_CHAIN_STEPS {
            return reject_item("", "", "too_complex");
        }
    }

    if let Err(reason) = preflight_axiom_or_sorry(&t.lean_source) {
        return reject_item("", "", reason);
    }

    let canonical_hash = nasrudin_core::canonical_hash(&t.canonical_statement);
    let theorem_id = canonical_hash.clone();
    let id_hex = hex::encode(&theorem_id);
    let hash_hex = hex::encode(&canonical_hash);

    let canonical_ac_hash = nasrudin_core::parse::parse_sexpr(&t.canonical_statement)
        .ok()
        .map(|e| nasrudin_core::canonical_ac_hash(&e).to_vec());

    let id_bytes_arr: [u8; 8] = {
        let mut a = [0u8; 8];
        if theorem_id.len() == 8 {
            a.copy_from_slice(&theorem_id);
        }
        a
    };
    match state.db.theorem_exists(&id_bytes_arr) {
        Ok(true) => {
            let existing_status = match state.db.get_theorem(&id_bytes_arr) {
                Ok(Some(t)) => match t.verified {
                    nasrudin_core::VerificationStatus::Verified { .. } => "Verified",
                    nasrudin_core::VerificationStatus::Pending => "Pending",
                    nasrudin_core::VerificationStatus::Rejected { .. } => "Rejected",
                    nasrudin_core::VerificationStatus::Timeout => "Rejected",
                }
                .to_string(),
                _ => "Unknown".to_string(),
            };
            return IngestResultItem {
                theorem_id: id_hex,
                canonical_hash: hash_hex,
                status: IngestStatus::Duplicate { existing_status },
            };
        }
        Ok(false) => {}
        Err(e) => {
            return IngestResultItem {
                theorem_id: id_hex,
                canonical_hash: hash_hex,
                status: IngestStatus::Rejected {
                    reason: format!("dedup_rocks_error: {e}"),
                },
            };
        }
    }

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

    // Look up the user's email from the worker's API key. One user
    // can own multiple workers; persisting the email on every theorem
    // row lets the contributor leaderboard aggregate at the user level
    // (rather than the worker level).
    let user_email: Option<String> = if let Some(pg) = &state.pg {
        use nasrudin_pg::sea_orm::{ColumnTrait, EntityTrait, QueryFilter};
        match nasrudin_pg::entity::api_keys::Entity::find()
            .filter(nasrudin_pg::entity::api_keys::Column::Name.eq(worker_id))
            .filter(nasrudin_pg::entity::api_keys::Column::Kind.eq("worker"))
            .filter(nasrudin_pg::entity::api_keys::Column::RevokedAt.is_null())
            .one(pg)
            .await
        {
            Ok(Some(key)) => match key.user_id {
                Some(uid) => nasrudin_pg::entity::users::Entity::find_by_id(uid)
                    .one(pg)
                    .await
                    .ok()
                    .flatten()
                    .map(|u| u.email),
                None => None,
            },
            _ => None,
        }
    } else {
        None
    };

    let new_row = theorems::NewTheorem {
        id: theorem_id.clone(),
        canonical_hash: canonical_hash.clone(),
        canonical_ac_hash: canonical_ac_hash.clone(),
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
        fitness_dimensional_correctness: extract_fitness(&t.fitness, "dimensional_correctness"),
        fitness_domain_coverage: extract_fitness(&t.fitness, "domain_coverage"),
        fitness_axiom_efficiency: extract_fitness(&t.fitness, "axiom_efficiency"),
        fitness_nasrudin_relevance: extract_fitness(&t.fitness, "nasrudin_relevance"),
        fitness_depth_score: extract_fitness(&t.fitness, "depth"),
        dimension: t.dimension.map(|d| d.to_vec()),
        engine_git_sha: engine_git_sha.to_string(),
        lean_version: lean_version.to_string(),
        contributor_id: worker_id.to_string(),
        worker_verified: t.worker_verified,
        worker_trusted: decision.trusted,
        worker_spot_check_rate: Some(decision.spot_check_rate as i32),
        user_email,
        pre_verified: false,
    };

    let id_arr = id_bytes_arr;
    let parsed_statement = nasrudin_core::parse::parse_sexpr(&t.canonical_statement)
        .unwrap_or_else(|_| nasrudin_core::Expr::Var("placeholder".into()));
    let theorem_for_rocks = nasrudin_core::Theorem {
        id: id_arr,
        statement: parsed_statement,
        canonical: t.canonical_statement.clone(),
        latex: t.latex.clone().unwrap_or_default(),
        proof: nasrudin_core::ProofTree::Axiom(id_arr),
        depth: t.depth.unwrap_or(0) as u32,
        complexity: t.complexity.unwrap_or(0) as u32,
        domain: parse_domain_or_default(&t.domain),
        dimension: None,
        parents: vec![],
        children: vec![],
        verified: nasrudin_core::VerificationStatus::Pending,
        fitness: nasrudin_core::FitnessScore::default(),
        generation: t.generation.unwrap_or(0) as u64,
        created_at: chrono::Utc::now().timestamp() as u64,
        origin: nasrudin_core::TheoremOrigin::Axiom,
    };

    if let Err(e) = state.db.put_theorem(&theorem_for_rocks) {
        return IngestResultItem {
            theorem_id: id_hex,
            canonical_hash: hash_hex,
            status: IngestStatus::Rejected {
                reason: format!("rocks_put_error: {e}"),
            },
        };
    }

    match serde_json::to_vec(&new_row) {
        Ok(payload) => {
            let _ = state.db.enqueue_pg_insert(&id_arr, &payload);
        }
        Err(e) => {
            tracing::warn!(
                theorem_id = %id_hex,
                "ingest: NewTheorem serialise failed; row in RocksDB but not queued for PG: {e}"
            );
        }
    }

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
            contributor_id: worker_id.to_string(),
        });
    IngestResultItem {
        theorem_id: id_hex,
        canonical_hash: hash_hex,
        status: IngestStatus::Pending,
    }
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

/// Convert the worker-supplied domain string to a `nasrudin_core::Domain`,
/// defaulting to `PureMath` for any unknown / empty value. Mirrors the
/// permissive parsing in `axiom_store::load_from_catalog`.
fn parse_domain_or_default(s: &str) -> nasrudin_core::Domain {
    use nasrudin_core::Domain;
    match s.to_lowercase().replace('-', "_").as_str() {
        "classical_mechanics" | "classicalmechanics" => Domain::ClassicalMechanics,
        "electromagnetism" => Domain::Electromagnetism,
        "special_relativity" | "specialrelativity" => Domain::SpecialRelativity,
        "general_relativity" | "generalrelativity" => Domain::GeneralRelativity,
        "quantum_mechanics" | "quantummechanics" => Domain::QuantumMechanics,
        "quantum_field_theory" | "quantumfieldtheory" => Domain::QuantumFieldTheory,
        "statistical_mechanics" | "statisticalmechanics" => Domain::StatisticalMechanics,
        "thermodynamics" => Domain::Thermodynamics,
        "optics" => Domain::Optics,
        "fluid_dynamics" | "fluiddynamics" => Domain::FluidDynamics,
        _ => Domain::PureMath,
    }
}
