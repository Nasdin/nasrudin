//! CRUD + listing operations for the `theorems` mirror table.
//!
//! The PostgreSQL theorems table mirrors the canonical RocksDB store. This
//! module is the single insertion / lookup / pagination surface used by
//! - the API ingest pipeline (Phase 4.2): insert pending → verify → flip,
//! - the read endpoints (Phase 5.1): get-by-id, get-by-hash, list-verified
//!   with stable cursor pagination.
//!
//! All write functions accept `&impl ConnectionTrait` so they can be called
//! either directly on a `DatabaseConnection` or inside a `DatabaseTransaction`
//! for atomic multi-step ingest.

use anyhow::{Context, Result};
use base64::{Engine as _, engine::general_purpose::URL_SAFE_NO_PAD};
use sea_orm::{
    ActiveModelTrait, ColumnTrait, ConnectionTrait, EntityTrait, ExprTrait, NotSet, QueryFilter,
    QueryOrder, QuerySelect, Set,
};

use crate::entity::theorems;

/// Builder for an unverified theorem submission.
///
/// `id` and `canonical_hash` MUST be set by the caller — they default to
/// `Vec::new()` for the `..Default::default()` shorthand, but the database
/// schema requires `binary_len(8) NOT NULL` for both. Use
/// `nasrudin_core::canonical_hash(canonical_statement)` to populate them.
///
/// All `Option<...>` fields default to `None`. `chain_json` defaults to an
/// empty JSON array. `origin_kind` defaults to `"Axiom"` because the column
/// is `NOT NULL TEXT` in PostgreSQL — callers should set it to a meaningful
/// value (`"Axiom"`, `"Derived"`, `"Imported"`, etc.) before insert.
#[derive(Clone, Debug)]
pub struct NewTheorem {
    pub id: Vec<u8>,
    pub canonical_hash: Vec<u8>,
    pub canonical_statement: String,
    pub latex: Option<String>,
    pub lean_source: String,
    pub domain: String,
    pub axioms_used: Vec<String>,
    pub chain_json: serde_json::Value,
    pub parents: Option<Vec<Vec<u8>>>,
    pub origin_kind: String,
    pub origin_payload: Option<serde_json::Value>,
    pub depth: Option<i32>,
    pub complexity: Option<i32>,
    pub generation: Option<i64>,
    pub fitness_novelty: Option<f32>,
    pub fitness_compactness: Option<f32>,
    pub fitness_dimensional_correctness: Option<f32>,
    pub fitness_domain_coverage: Option<f32>,
    pub fitness_axiom_efficiency: Option<f32>,
    pub fitness_nasrudin_relevance: Option<f32>,
    pub fitness_depth_score: Option<f32>,
    pub dimension: Option<Vec<i32>>,
    pub engine_git_sha: String,
    pub lean_version: String,
    pub contributor_id: String,
}

impl Default for NewTheorem {
    fn default() -> Self {
        Self {
            id: Vec::new(),
            canonical_hash: Vec::new(),
            canonical_statement: String::new(),
            latex: None,
            lean_source: String::new(),
            domain: String::new(),
            axioms_used: Vec::new(),
            chain_json: serde_json::json!([]),
            parents: None,
            origin_kind: "Axiom".into(),
            origin_payload: None,
            depth: None,
            complexity: None,
            generation: None,
            fitness_novelty: None,
            fitness_compactness: None,
            fitness_dimensional_correctness: None,
            fitness_domain_coverage: None,
            fitness_axiom_efficiency: None,
            fitness_nasrudin_relevance: None,
            fitness_depth_score: None,
            dimension: None,
            engine_git_sha: String::new(),
            lean_version: String::new(),
            contributor_id: String::new(),
        }
    }
}

/// A paged result set with optional next-cursor and a capped total.
///
/// `total` is `COUNT(*)` capped at `TOTAL_CAP` (10_000); `total_capped` is set
/// when the underlying row count exceeded the cap so callers can render
/// "10,000+" instead of an inaccurate exact number.
#[derive(Debug, Clone)]
pub struct Page<T> {
    pub items: Vec<T>,
    pub next_cursor: Option<String>,
    pub total_capped: bool,
    pub total: u64,
}

/// Maximum count we report from `list_verified` — anything beyond is just
/// flagged as `total_capped = true`.
const TOTAL_CAP: u64 = 10_000;

/// Insert a new pending theorem. Returns the inserted `id`.
///
/// Sets `status = "Pending"`, `created_at = NOW()` (DB default), and leaves
/// all `verification_*` / `verified_at` columns NULL. A unique-violation on
/// `canonical_hash` propagates as the underlying SeaORM error so callers can
/// implement deduplication on top.
pub async fn insert_pending(db: &impl ConnectionTrait, n: NewTheorem) -> Result<Vec<u8>> {
    let id = n.id.clone();

    let active = theorems::ActiveModel {
        id: Set(n.id),
        canonical_hash: Set(n.canonical_hash),
        canonical_statement: Set(n.canonical_statement),
        latex: Set(n.latex),
        lean_source: Set(n.lean_source),
        domain: Set(n.domain),
        axioms_used: Set(n.axioms_used),
        chain_json: Set(n.chain_json),
        parents: Set(n.parents),
        origin_kind: Set(n.origin_kind),
        origin_payload: Set(n.origin_payload),
        depth: Set(n.depth),
        complexity: Set(n.complexity),
        generation: Set(n.generation),
        fitness_novelty: Set(n.fitness_novelty),
        fitness_compactness: Set(n.fitness_compactness),
        fitness_dimensional_correctness: Set(n.fitness_dimensional_correctness),
        fitness_domain_coverage: Set(n.fitness_domain_coverage),
        fitness_axiom_efficiency: Set(n.fitness_axiom_efficiency),
        fitness_nasrudin_relevance: Set(n.fitness_nasrudin_relevance),
        fitness_depth_score: Set(n.fitness_depth_score),
        dimension: Set(n.dimension),
        engine_git_sha: Set(n.engine_git_sha),
        lean_version: Set(n.lean_version),
        verification_tactic: Set(None),
        verification_duration_ms: Set(None),
        verification_path: Set(None),
        status: Set("Pending".into()),
        rejected_reason: Set(None),
        contributor_id: Set(n.contributor_id),
        // Let the DB default (NOW()) populate created_at — saves a clock RTT.
        created_at: NotSet,
        verified_at: Set(None),
    };

    active
        .insert(db)
        .await
        .context("insert pending theorem")?;
    Ok(id)
}

/// Look up a single theorem by its 8-byte primary key.
pub async fn get_by_id(
    db: &impl ConnectionTrait,
    id: &[u8],
) -> Result<Option<theorems::Model>> {
    theorems::Entity::find_by_id(id.to_vec())
        .one(db)
        .await
        .context("get_by_id theorem")
}

/// Look up a single theorem by its canonical hash (also 8 bytes, unique).
pub async fn get_by_canonical_hash(
    db: &impl ConnectionTrait,
    hash: &[u8],
) -> Result<Option<theorems::Model>> {
    theorems::Entity::find()
        .filter(theorems::Column::CanonicalHash.eq(hash.to_vec()))
        .one(db)
        .await
        .context("get_by_canonical_hash theorem")
}

/// Flip a pending theorem to `Verified`, recording the verification path
/// (e.g. `"A"`, `"B"`, `"C"`), the tactic that closed the goal, and the
/// wall-clock duration in milliseconds.
pub async fn mark_verified(
    db: &impl ConnectionTrait,
    id: &[u8],
    path: &str,
    tactic: &str,
    duration_ms: i32,
) -> Result<()> {
    let now: chrono::DateTime<chrono::Utc> = chrono::Utc::now();
    let active = theorems::ActiveModel {
        id: Set(id.to_vec()),
        status: Set("Verified".into()),
        verification_path: Set(Some(path.into())),
        verification_tactic: Set(Some(tactic.into())),
        verification_duration_ms: Set(Some(duration_ms)),
        verified_at: Set(Some(now.into())),
        ..Default::default()
    };
    active.update(db).await.context("mark_verified theorem")?;
    Ok(())
}

/// Flip a pending theorem to `Rejected`, recording a free-form reason.
pub async fn mark_rejected(
    db: &impl ConnectionTrait,
    id: &[u8],
    reason: &str,
) -> Result<()> {
    let active = theorems::ActiveModel {
        id: Set(id.to_vec()),
        status: Set("Rejected".into()),
        rejected_reason: Set(Some(reason.into())),
        ..Default::default()
    };
    active.update(db).await.context("mark_rejected theorem")?;
    Ok(())
}

/// Encode a `(verified_at, id)` cursor as 16-byte URL-safe base64 (no pad).
fn encode_cursor(verified_at: chrono::DateTime<chrono::FixedOffset>, id: &[u8]) -> String {
    let micros: i64 = verified_at.timestamp_micros();
    let mut buf = micros.to_le_bytes().to_vec();
    buf.extend_from_slice(id);
    URL_SAFE_NO_PAD.encode(buf)
}

/// Decode a cursor produced by [`encode_cursor`]. The cursor encodes the
/// `verified_at` of the last row on the previous page plus that row's 8-byte
/// id, so the next page can filter strictly past it.
fn decode_cursor(c: &str) -> Result<(chrono::DateTime<chrono::FixedOffset>, Vec<u8>)> {
    let bytes = URL_SAFE_NO_PAD
        .decode(c)
        .context("cursor: invalid base64url")?;
    if bytes.len() != 16 {
        anyhow::bail!("cursor: expected 16 bytes, got {}", bytes.len());
    }
    let micros = i64::from_le_bytes(bytes[0..8].try_into().unwrap());
    let id = bytes[8..16].to_vec();
    let dt_utc = chrono::DateTime::from_timestamp_micros(micros)
        .ok_or_else(|| anyhow::anyhow!("cursor: bad timestamp"))?;
    Ok((dt_utc.fixed_offset(), id))
}

/// List `Verified` theorems newest-first with cursor pagination.
///
/// Ordering is `(verified_at DESC, id DESC)` — both terms matter so rows that
/// happen to share a microsecond timestamp still have a deterministic order
/// for the cursor's `<` filter.
///
/// `total` is COUNT(*) over the same WHERE clause, capped at [`TOTAL_CAP`];
/// when the true count exceeds the cap, `total_capped = true`.
pub async fn list_verified(
    db: &impl ConnectionTrait,
    cursor: Option<String>,
    limit: u64,
    domain: Option<String>,
) -> Result<Page<theorems::Model>> {
    let mut q = theorems::Entity::find().filter(theorems::Column::Status.eq("Verified"));
    if let Some(d) = domain.as_ref() {
        q = q.filter(theorems::Column::Domain.eq(d.clone()));
    }
    if let Some(c) = cursor.as_ref() {
        let (dt, id) = decode_cursor(c)?;
        // verified_at < dt OR (verified_at = dt AND id < $id)
        q = q.filter(
            theorems::Column::VerifiedAt
                .lt(dt)
                .or(theorems::Column::VerifiedAt
                    .eq(dt)
                    .and(theorems::Column::Id.lt(id))),
        );
    }

    // Peek one extra row so we can tell whether more pages exist.
    let rows = q
        .order_by_desc(theorems::Column::VerifiedAt)
        .order_by_desc(theorems::Column::Id)
        .limit(limit + 1)
        .all(db)
        .await
        .context("list_verified")?;

    let has_more = rows.len() as u64 > limit;
    let mut items: Vec<theorems::Model> = rows.into_iter().take(limit as usize).collect();

    let next_cursor = if has_more {
        items
            .last()
            .and_then(|m| m.verified_at.map(|v| encode_cursor(v, &m.id)))
    } else {
        None
    };

    // Capped count over the same filter (status + optional domain). Cheap
    // because of idx_theorems_status; PostgreSQL won't actually scan more
    // than TOTAL_CAP+1 rows thanks to the inner LIMIT.
    let total = count_capped(db, domain.as_deref()).await?;
    let total_capped = total > TOTAL_CAP;
    let total = Ord::min(total, TOTAL_CAP);

    // We over-allocated capacity if there were more rows; trim to fit.
    items.shrink_to_fit();

    Ok(Page {
        items,
        next_cursor,
        total_capped,
        total,
    })
}

/// COUNT(*)-equivalent of verified rows (optionally filtered by domain),
/// capped at `TOTAL_CAP + 1`. Implemented as a SELECT-IDs probe with
/// `LIMIT TOTAL_CAP + 1`: cheap because the index covers `(status)` and we
/// never scan past the cap. Returns the row count seen by the probe; the
/// caller compares to `TOTAL_CAP` to decide whether to flag `total_capped`.
async fn count_capped(db: &impl ConnectionTrait, domain: Option<&str>) -> Result<u64> {
    let mut q = theorems::Entity::find().filter(theorems::Column::Status.eq("Verified"));
    if let Some(d) = domain {
        q = q.filter(theorems::Column::Domain.eq(d));
    }
    // Project to id only and cap the scan; we just need the row count, the
    // bytes are discarded.
    let ids: Vec<Vec<u8>> = q
        .select_only()
        .column(theorems::Column::Id)
        .limit(TOTAL_CAP + 1)
        .into_tuple::<Vec<u8>>()
        .all(db)
        .await
        .context("count_capped probe")?;
    Ok(ids.len() as u64)
}
