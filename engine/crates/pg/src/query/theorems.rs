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
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct NewTheorem {
    pub id: Vec<u8>,
    pub canonical_hash: Vec<u8>,
    /// AC-canonical hash of the statement. Optional for legacy ingest paths
    /// during the rollout window; new ingest writes this to enable
    /// commutativity-aware exact-match search.
    pub canonical_ac_hash: Option<Vec<u8>>,
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
    /// P-Task 12: worker locally lake-built before submitting.
    pub worker_verified: bool,
    /// Trust decision at ingest time (admin-panel trust-bypass).
    pub worker_trusted: bool,
    /// 1-in-N sampling rate at ingest; None means env default.
    pub worker_spot_check_rate: Option<i32>,
    /// Email of the user who owns the worker's API key. `None` for
    /// anonymous workers. Powers the user-level contributor leaderboard
    /// — aggregations group by `user_email` so one user's many workers
    /// roll up into a single row.
    pub user_email: Option<String>,
    /// Bypass the Pending → Lake-build → Verified state machine and
    /// land the row directly as `Verified` with `verified_at = NOW()`.
    /// Used by the PhysLean catalog mirror at boot — those theorems
    /// arrive pre-proven from upstream, so re-verifying via the lake
    /// would be wasted compute. `#[serde(default)]` keeps payloads
    /// already sitting in the RocksDB pg_insert_queue from before this
    /// field existed deserialisable (default = false → status="Pending"
    /// as before).
    #[serde(default)]
    pub pre_verified: bool,
}

impl Default for NewTheorem {
    fn default() -> Self {
        Self {
            id: Vec::new(),
            canonical_hash: Vec::new(),
            canonical_ac_hash: None,
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
            worker_verified: false,
            worker_trusted: false,
            worker_spot_check_rate: None,
            user_email: None,
            pre_verified: false,
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

/// Insert a new theorem. Returns the inserted `id`.
///
/// By default sets `status = "Pending"`, `created_at = NOW()` (DB default),
/// and leaves all `verification_*` / `verified_at` columns NULL. When the
/// payload's `pre_verified` flag is set, lands the row directly as
/// `Verified` with `verified_at = NOW()` and `verification_tactic =
/// "imported"` — the PhysLean catalog mirror uses this so pre-proven
/// upstream theorems skip the Pending → Lake-build → Verified cycle.
///
/// A unique-violation on `canonical_hash` propagates as the underlying
/// SeaORM error so callers can implement deduplication on top.
pub async fn insert_pending(db: &impl ConnectionTrait, n: NewTheorem) -> Result<Vec<u8>> {
    let id = n.id.clone();
    let pre_verified = n.pre_verified;
    let now = chrono::Utc::now().fixed_offset();

    let active = theorems::ActiveModel {
        id: Set(n.id),
        canonical_hash: Set(n.canonical_hash),
        canonical_ac_hash: Set(n.canonical_ac_hash),
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
        verification_tactic: Set(if pre_verified { Some("imported".into()) } else { None }),
        verification_duration_ms: Set(None),
        verification_path: Set(None),
        status: Set(if pre_verified { "Verified".into() } else { "Pending".into() }),
        rejected_reason: Set(None),
        contributor_id: Set(n.contributor_id),
        // Let the DB default (NOW()) populate created_at — saves a clock RTT.
        created_at: NotSet,
        verified_at: Set(if pre_verified { Some(now) } else { None }),
        worker_verified: Set(n.worker_verified),
        worker_trusted: Set(n.worker_trusted),
        worker_spot_check_rate: Set(n.worker_spot_check_rate),
        user_email: Set(n.user_email),
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

/// Batch lookup of theorems by 8-byte primary key. One PG round-trip
/// instead of N — used by hot paths like concept-search that resolve a
/// page of nearest-neighbour hits to full rows. Order of the returned
/// `Vec` is whatever PG decides; callers should index by `model.id` if
/// they care about input order.
///
/// Empty input is a no-op that returns `Vec::new()` without touching PG.
pub async fn list_by_ids(
    db: &impl ConnectionTrait,
    ids: &[Vec<u8>],
) -> Result<Vec<theorems::Model>> {
    if ids.is_empty() {
        return Ok(Vec::new());
    }
    theorems::Entity::find()
        .filter(theorems::Column::Id.is_in(ids.iter().cloned()))
        .all(db)
        .await
        .context("list_by_ids theorems")
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

/// Mark a batch of theorems Rejected with the same reason in one
/// PG round-trip. Used by the lake-promotion drain after a
/// `cascade_reject` walk produces a large set of invalidated
/// descendants — issuing N individual UPDATEs for a 10k-descendant
/// cascade is unacceptable, this is one statement.
///
/// `ids` must be 8-byte canonical hashes. Empty input is a no-op.
pub async fn mark_rejected_batch(
    db: &impl ConnectionTrait,
    ids: &[Vec<u8>],
    reason: &str,
) -> Result<u64> {
    use sea_orm::Statement;
    if ids.is_empty() {
        return Ok(0);
    }
    // Construct a parameterised IN-list statement. SeaORM accepts
    // Vec<Vec<u8>> directly through the Value type's bytea variant.
    let mut placeholders: Vec<String> = Vec::with_capacity(ids.len());
    let mut values: Vec<sea_orm::Value> = Vec::with_capacity(ids.len() + 1);
    values.push(reason.into());
    for (i, id) in ids.iter().enumerate() {
        // $1 is reason, $2..N+1 are the ids.
        placeholders.push(format!("${}", i + 2));
        values.push(id.clone().into());
    }
    let sql = format!(
        "UPDATE theorems SET status = 'Rejected', rejected_reason = $1 \
         WHERE id IN ({})",
        placeholders.join(",")
    );
    let stmt = Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        &sql,
        values,
    );
    let rows = db
        .execute_raw(stmt)
        .await
        .context("mark_rejected_batch UPDATE")?;
    Ok(rows.rows_affected())
}

/// Return the canonical-hash bytes of every theorem currently in the
/// `Rejected` state. Workers pull this list at startup to build a
/// negative-result Bloom filter — if a chain produces a canonical
/// already known to be rejected, no point handing it to lake-build.
///
/// The list grows monotonically; workers can re-pull periodically to
/// stay current. The page size is intentionally large (the column is
/// 8 bytes per row, so even 1M rejected theorems is ~8 MB on the wire).
pub async fn list_rejected_canonical_hashes(
    db: &impl ConnectionTrait,
    limit: u64,
) -> Result<Vec<Vec<u8>>> {
    use sea_orm::QuerySelect;
    let rows: Vec<(Vec<u8>,)> = theorems::Entity::find()
        .filter(theorems::Column::Status.eq("Rejected"))
        .select_only()
        .column(theorems::Column::CanonicalHash)
        .limit(limit)
        .into_tuple()
        .all(db)
        .await
        .context("list_rejected_canonical_hashes")?;
    Ok(rows.into_iter().map(|(h,)| h).collect())
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

/// Listing filters applied by [`list_verified`]. Defaults are conservative
/// for public endpoints: hide `chain_replay` rows (no Lean kernel has touched
/// them) and `Rejected` rows. Callers that want to surface those (admin
/// views, internal exporters) flip the relevant flag explicitly.
#[derive(Debug, Clone, Copy, Default)]
pub struct ListOptions {
    /// Include rows where `verification_tactic = 'chain_replay'`. Default false.
    pub include_internal: bool,
    /// Include rows where `status = 'Rejected'` alongside `Verified`. Default false.
    pub include_rejected: bool,
}

/// List `Verified` theorems newest-first with cursor pagination.
///
/// Ordering is `(verified_at DESC, id DESC)` — both terms matter so rows that
/// happen to share a microsecond timestamp still have a deterministic order
/// for the cursor's `<` filter.
///
/// `total` is COUNT(*) over the public-default predicate (Verified, not
/// chain_replay), capped at [`TOTAL_CAP`]; when the true count exceeds the
/// cap, `total_capped = true`. The total intentionally does NOT track
/// `opts.include_rejected` — the headline number on `/browse` should reflect
/// the corpus, not the audit-mode toggle state.
pub async fn list_verified(
    db: &impl ConnectionTrait,
    cursor: Option<String>,
    limit: u64,
    domain: Option<String>,
    opts: ListOptions,
) -> Result<Page<theorems::Model>> {
    let mut q = theorems::Entity::find();
    if opts.include_rejected {
        q = q.filter(
            theorems::Column::Status
                .eq("Verified")
                .or(theorems::Column::Status.eq("Rejected")),
        );
    } else {
        q = q.filter(theorems::Column::Status.eq("Verified"));
    }
    if !opts.include_internal {
        q = q.filter(
            theorems::Column::VerificationTactic
                .ne("chain_replay")
                .or(theorems::Column::VerificationTactic.is_null()),
        );
    }
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

/// Count `Verified` theorems attributed to a single contributor.
///
/// Used by the per-user `/api/me/stats` endpoint (Phase 9 Task 6.2). Returns
/// the raw `COUNT(*)` over `(status = 'Verified', contributor_id = $1)` —
/// no cap, since per-user totals are bounded by realistic contribution rates
/// rather than the global theorem volume.
pub async fn count_by_contributor(
    db: &impl ConnectionTrait,
    contributor_id: &str,
) -> Result<u64> {
    use sea_orm::PaginatorTrait;
    let count = theorems::Entity::find()
        .filter(theorems::Column::Status.eq("Verified"))
        .filter(theorems::Column::ContributorId.eq(contributor_id))
        .count(db)
        .await
        .context("count_by_contributor")?;
    Ok(count)
}

/// List the most-recent `Verified` theorems for a contributor, newest-first.
///
/// `limit` is forwarded straight to SQL `LIMIT`. Ordering is by `verified_at
/// DESC, id DESC` to break ties deterministically.
pub async fn list_by_contributor(
    db: &impl ConnectionTrait,
    contributor_id: &str,
    limit: u64,
) -> Result<Vec<theorems::Model>> {
    theorems::Entity::find()
        .filter(theorems::Column::Status.eq("Verified"))
        .filter(theorems::Column::ContributorId.eq(contributor_id))
        .order_by_desc(theorems::Column::VerifiedAt)
        .order_by_desc(theorems::Column::Id)
        .limit(limit)
        .all(db)
        .await
        .context("list_by_contributor")
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

/// Lifetime count of `Verified` rows. Backs the landing/footer
/// "X theorems" badge — must match what `/browse` actually returns
/// (which lists `status = 'Verified'`), so don't conflate with the
/// RocksDB `total_theorems` stat which also counts pending/imported
/// rows that haven't reached PG yet.
pub async fn count_verified(db: &impl ConnectionTrait) -> Result<u64> {
    use sea_orm::PaginatorTrait;
    theorems::Entity::find()
        .filter(theorems::Column::Status.eq("Verified"))
        .count(db)
        .await
        .context("count_verified")
}

/// Count `Verified` theorems with `verified_at >= since`. Backs the
/// landing-page "verified in last N hours" pulse counter — small windows
/// (1h, 24h) hit the `(status, verified_at)` index range scan and stay
/// well under a millisecond even on a 7-figure theorems table.
pub async fn count_verified_since(
    db: &impl ConnectionTrait,
    since: chrono::DateTime<chrono::Utc>,
) -> Result<u64> {
    use sea_orm::PaginatorTrait;
    theorems::Entity::find()
        .filter(theorems::Column::Status.eq("Verified"))
        .filter(theorems::Column::VerifiedAt.gte(since.fixed_offset()))
        .count(db)
        .await
        .context("count_verified_since")
}

/// Per-domain breakdown of `Verified` theorems with `verified_at >= since`,
/// ordered by count desc. Backs the workers-page network breakdown chart.
/// `(domain, count)` pairs; domains with zero in-window count are omitted.
pub async fn count_verified_by_domain_since(
    db: &impl ConnectionTrait,
    since: chrono::DateTime<chrono::Utc>,
) -> Result<Vec<(String, i64)>> {
    use sea_orm::{DatabaseBackend, FromQueryResult, Statement};

    #[derive(FromQueryResult)]
    struct Row {
        domain: String,
        cnt: i64,
    }

    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        SELECT domain, COUNT(*)::BIGINT AS cnt
          FROM theorems
         WHERE status = 'Verified'
           AND verified_at >= $1
         GROUP BY domain
         ORDER BY cnt DESC
        "#,
        [since.fixed_offset().into()],
    );
    let rows = Row::find_by_statement(stmt)
        .all(db)
        .await
        .context("count_verified_by_domain_since")?;
    Ok(rows.into_iter().map(|r| (r.domain, r.cnt)).collect())
}

/// COUNT(*) of theorems submitted in the window `created_at >= since`.
/// Backs the "submitted" stage of the landing-page funnel ticker.
/// O(log n) via `idx_theorems_created_at`.
pub async fn count_submitted_since(
    db: &impl ConnectionTrait,
    since: chrono::DateTime<chrono::Utc>,
) -> Result<u64> {
    use sea_orm::PaginatorTrait;
    theorems::Entity::find()
        .filter(theorems::Column::CreatedAt.gte(since.fixed_offset()))
        .count(db)
        .await
        .context("count_submitted_since")
}

/// COUNT(*) of `Rejected` theorems with `created_at >= since`. Backs the
/// "rejected" stage of the discard-funnel. The partial index
/// `idx_theorems_rejected_created_at` covers this query exactly so it
/// stays sub-millisecond even as the rejected pile grows.
pub async fn count_rejected_since(
    db: &impl ConnectionTrait,
    since: chrono::DateTime<chrono::Utc>,
) -> Result<u64> {
    use sea_orm::PaginatorTrait;
    theorems::Entity::find()
        .filter(theorems::Column::Status.eq("Rejected"))
        .filter(theorems::Column::CreatedAt.gte(since.fixed_offset()))
        .count(db)
        .await
        .context("count_rejected_since")
}

/// Current-pending count: COUNT(*) WHERE status='Pending'. Backs the
/// "pending now" stage (lake-queue depth). Partial index keeps this
/// O(1)-ish — the live pending slice is typically <0.1% of the table.
pub async fn count_pending(db: &impl ConnectionTrait) -> Result<u64> {
    use sea_orm::PaginatorTrait;
    theorems::Entity::find()
        .filter(theorems::Column::Status.eq("Pending"))
        .count(db)
        .await
        .context("count_pending")
}

/// Most-recent `Verified` theorem's metadata for the "last verification Ks
/// ago in [domain]" pulse line. Returns `None` when no theorems have been
/// verified yet.
pub async fn last_verified(
    db: &impl ConnectionTrait,
) -> Result<Option<(chrono::DateTime<chrono::FixedOffset>, String)>> {
    use sea_orm::QuerySelect;
    let row: Option<(Option<chrono::DateTime<chrono::FixedOffset>>, String)> =
        theorems::Entity::find()
            .filter(theorems::Column::Status.eq("Verified"))
            .order_by_desc(theorems::Column::VerifiedAt)
            .order_by_desc(theorems::Column::Id)
            .select_only()
            .column(theorems::Column::VerifiedAt)
            .column(theorems::Column::Domain)
            .limit(1)
            .into_tuple()
            .one(db)
            .await
            .context("last_verified")?;
    Ok(row.and_then(|(va, d)| va.map(|v| (v, d))))
}
