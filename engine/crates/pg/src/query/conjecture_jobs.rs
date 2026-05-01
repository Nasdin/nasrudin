//! CRUD + event-log helpers for `conjecture_jobs` and `conjecture_events`.
//!
//! All state-machine transitions live here; handlers express intent
//! (`set_suggestions`, `set_chosen_seed`, `mark_failed`) and never construct
//! raw `ActiveModel` literals.

use sea_orm::*;
use uuid::Uuid;

use crate::entity::{conjecture_events, conjecture_jobs};

#[derive(Debug, Clone)]
pub struct CreateInput {
    pub owner_id: Uuid,
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub provider: String,
    pub model: String,
    pub budget: serde_json::Value,
}

pub async fn create(db: &DatabaseConnection, input: CreateInput) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    let am = conjecture_jobs::ActiveModel {
        id: Set(id),
        owner_id: Set(input.owner_id),
        state: Set("Created".to_string()),
        outcome: Set(None),
        hunch: Set(input.hunch),
        domain_hint: Set(input.domain_hint),
        provider: Set(input.provider),
        model: Set(input.model),
        suggestions: Set(None),
        chosen_index: Set(None),
        seed: Set(None),
        budget: Set(input.budget),
        claimed_by: Set(None),
        claimed_at: Set(None),
        lease_expires_at: Set(None),
        last_heartbeat_at: Set(None),
        candidates_attempted: Set(0),
        candidates_verified: Set(0),
        verified_theorem_ids: Set(None),
        created_at: Set(chrono::Utc::now().into()),
        completed_at: Set(None),
        paper_draft: Set(None),
        lake_slot_hours_quota: Set(96),
        lake_slot_hours_consumed: Set(0.0),
        slice_priority: Set(5),
        tier: Set("researcher".into()),
        // Default 4 — `atomic_claim_paid` overwrites this with the
        // worker's reported `available_lake_slots` at claim time.
        allocated_slots: Set(4),
    };
    am.insert(db).await?;
    Ok(id)
}

pub async fn get_by_id(
    db: &DatabaseConnection,
    id: Uuid,
) -> Result<Option<conjecture_jobs::Model>, DbErr> {
    conjecture_jobs::Entity::find_by_id(id).one(db).await
}

pub async fn list_for_user(
    db: &DatabaseConnection,
    owner_id: Uuid,
    limit: u64,
) -> Result<Vec<conjecture_jobs::Model>, DbErr> {
    conjecture_jobs::Entity::find()
        .filter(conjecture_jobs::Column::OwnerId.eq(owner_id))
        .order_by_desc(conjecture_jobs::Column::CreatedAt)
        .limit(limit)
        .all(db)
        .await
}

pub async fn set_suggestions(
    db: &DatabaseConnection,
    id: Uuid,
    suggestions: serde_json::Value,
) -> Result<(), DbErr> {
    let model = conjecture_jobs::Entity::find_by_id(id)
        .one(db)
        .await?
        .ok_or_else(|| DbErr::RecordNotFound("conjecture_jobs".into()))?;
    let mut active: conjecture_jobs::ActiveModel = model.into();
    active.suggestions = Set(Some(suggestions));
    active.state = Set("LlmComplete".to_string());
    active.update(db).await?;
    Ok(())
}

pub async fn set_chosen_seed(
    db: &DatabaseConnection,
    id: Uuid,
    chosen_index: i32,
    seed: serde_json::Value,
) -> Result<(), DbErr> {
    let model = conjecture_jobs::Entity::find_by_id(id)
        .one(db)
        .await?
        .ok_or_else(|| DbErr::RecordNotFound("conjecture_jobs".into()))?;
    let mut active: conjecture_jobs::ActiveModel = model.into();
    active.chosen_index = Set(Some(chosen_index));
    active.seed = Set(Some(seed));
    active.state = Set("QueuedForWorker".to_string());
    active.update(db).await?;
    Ok(())
}

pub async fn mark_failed(
    db: &DatabaseConnection,
    id: Uuid,
    reason: &str,
) -> Result<(), DbErr> {
    let model = conjecture_jobs::Entity::find_by_id(id)
        .one(db)
        .await?
        .ok_or_else(|| DbErr::RecordNotFound("conjecture_jobs".into()))?;
    let mut active: conjecture_jobs::ActiveModel = model.into();
    active.state = Set("Complete".to_string());
    active.outcome = Set(Some(format!("Failed:{reason}")));
    active.completed_at = Set(Some(chrono::Utc::now().into()));
    active.update(db).await?;
    Ok(())
}

pub async fn insert_event(
    db: &DatabaseConnection,
    job_id: Uuid,
    kind: &str,
    payload: serde_json::Value,
) -> Result<i64, DbErr> {
    let am = conjecture_events::ActiveModel {
        id: NotSet,
        job_id: Set(job_id),
        kind: Set(kind.to_string()),
        payload: Set(payload),
        at: Set(chrono::Utc::now().into()),
    };
    let inserted = am.insert(db).await?;
    Ok(inserted.id)
}

pub async fn events_after(
    db: &DatabaseConnection,
    job_id: Uuid,
    after_id: i64,
    limit: u64,
) -> Result<Vec<conjecture_events::Model>, DbErr> {
    conjecture_events::Entity::find()
        .filter(conjecture_events::Column::JobId.eq(job_id))
        .filter(conjecture_events::Column::Id.gt(after_id))
        .order_by_asc(conjecture_events::Column::Id)
        .limit(limit)
        .all(db)
        .await
}

// ---------------------------------------------------------------------------
// Phase E: dequeue + lease lifecycle
// ---------------------------------------------------------------------------

/// One claimed conjecture, returned to the worker.
#[derive(Debug, Clone)]
pub struct ClaimedJob {
    pub id: Uuid,
    pub seed: serde_json::Value,
    pub budget: serde_json::Value,
    pub hunch: String,
    pub provider: String,
    pub model: String,
}

/// Atomic dequeue. Marks the row state='Running', sets a 5-minute lease,
/// stamps `claimed_by` + `claimed_at`, returns the row's seed + budget.
/// Returns `Ok(None)` when nothing is queued.
///
/// Uses `FOR UPDATE SKIP LOCKED` so concurrent workers never block each
/// other and never see the same row twice.
pub async fn claim_next(
    db: &DatabaseConnection,
    worker_id: &str,
) -> Result<Option<ClaimedJob>, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET claimed_by = $1,
            claimed_at = NOW(),
            lease_expires_at = NOW() + INTERVAL '5 minutes',
            last_heartbeat_at = NOW(),
            state = 'Running'
        WHERE id = (
            SELECT id FROM conjecture_jobs
            WHERE state = 'QueuedForWorker' AND claimed_by IS NULL
            ORDER BY created_at
            LIMIT 1
            FOR UPDATE SKIP LOCKED
        )
        RETURNING id, seed, budget, hunch, provider, model
        "#,
        [worker_id.into()],
    );
    let Some(row) = db.query_one_raw(stmt).await? else {
        return Ok(None);
    };
    let id: Uuid = row.try_get_by_index(0)?;
    let seed: serde_json::Value = row.try_get_by_index(1)?;
    let budget: serde_json::Value = row.try_get_by_index(2)?;
    let hunch: String = row.try_get_by_index(3)?;
    let provider: String = row.try_get_by_index(4)?;
    let model: String = row.try_get_by_index(5)?;
    Ok(Some(ClaimedJob {
        id,
        seed,
        budget,
        hunch,
        provider,
        model,
    }))
}

/// Heartbeat: extends the lease by 5 minutes and sets progress counters.
/// Returns rows_affected so the caller can detect lease/ownership
/// violations (0 = wrong worker or not Running).
pub async fn update_heartbeat_progress(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: &str,
    candidates_attempted: i32,
    candidates_verified: i32,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET last_heartbeat_at = NOW(),
            lease_expires_at = NOW() + INTERVAL '5 minutes',
            candidates_attempted = $3,
            candidates_verified = $4
        WHERE id = $1 AND claimed_by = $2 AND state = 'Running'
        "#,
        [
            id.into(),
            worker_id.into(),
            candidates_attempted.into(),
            candidates_verified.into(),
        ],
    );
    let res = db.execute_raw(stmt).await?;
    Ok(res.rows_affected())
}

/// Append a theorem id to verified_theorem_ids and bump candidates_verified.
/// Caller has already re-verified the theorem (we delegate to the same
/// ingest pipeline used by `/api/ingest`).
pub async fn append_verified_theorem(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: &str,
    theorem_id: Vec<u8>,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET verified_theorem_ids = COALESCE(verified_theorem_ids, ARRAY[]::BYTEA[]) || ARRAY[$3::BYTEA],
            candidates_verified = candidates_verified + 1,
            last_heartbeat_at = NOW(),
            lease_expires_at = NOW() + INTERVAL '5 minutes'
        WHERE id = $1 AND claimed_by = $2 AND state = 'Running'
        "#,
        [id.into(), worker_id.into(), theorem_id.into()],
    );
    let res = db.execute_raw(stmt).await?;
    Ok(res.rows_affected())
}

/// Final transition. `outcome` ∈ {"Verified", "NoResult", "TimedOut", "Cancelled"}.
pub async fn complete(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: &str,
    outcome: &str,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET state = 'Complete',
            outcome = $3,
            completed_at = NOW()
        WHERE id = $1 AND claimed_by = $2 AND state = 'Running'
        "#,
        [id.into(), worker_id.into(), outcome.into()],
    );
    let res = db.execute_raw(stmt).await?;
    Ok(res.rows_affected())
}

/// Phase F: append a chunk to the streaming paper draft. Concurrent-safe
/// (single writer per job; the trigger handler holds the row implicitly
/// while it streams from the LLM). Initialises the column from NULL.
pub async fn append_paper_chunk(
    db: &DatabaseConnection,
    id: Uuid,
    chunk: &str,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE conjecture_jobs SET paper_draft = COALESCE(paper_draft, '') || $2 WHERE id = $1",
        [id.into(), chunk.into()],
    );
    let res = db.execute_raw(stmt).await?;
    Ok(res.rows_affected())
}

/// Phase F: read the persisted paper draft for a job. `Ok(None)` when
/// the row exists but no draft has been generated yet.
pub async fn get_paper_draft(
    db: &DatabaseConnection,
    id: Uuid,
) -> Result<Option<String>, DbErr> {
    let model = conjecture_jobs::Entity::find_by_id(id).one(db).await?;
    Ok(model.and_then(|m| m.paper_draft))
}

/// Phase F: clear (NULL) the paper draft. Called at the start of a
/// fresh generation request so the SSE stream doesn't show stale
/// chunks merged with new ones.
pub async fn clear_paper_draft(db: &DatabaseConnection, id: Uuid) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE conjecture_jobs SET paper_draft = NULL WHERE id = $1",
        [id.into()],
    );
    let res = db.execute_raw(stmt).await?;
    Ok(res.rows_affected())
}

/// Lease reaper backbone. Returns the IDs that were requeued so the
/// caller can emit one `progress {worker_lost: true}` event per row.
pub async fn requeue_expired_leases(db: &DatabaseConnection) -> Result<Vec<Uuid>, DbErr> {
    let stmt = Statement::from_string(
        DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET claimed_by = NULL,
            claimed_at = NULL,
            lease_expires_at = NULL,
            state = 'QueuedForWorker'
        WHERE state = 'Running' AND lease_expires_at < NOW()
        RETURNING id
        "#
        .to_string(),
    );
    let rows = db.query_all_raw(stmt).await?;
    let mut ids = Vec::with_capacity(rows.len());
    for row in rows {
        ids.push(row.try_get_by_index::<Uuid>(0)?);
    }
    Ok(ids)
}

// ---------------------------------------------------------------------------
// Paid Researcher tier — atomic claim against the new state values
// (`queued` / `claimed` / `running`), distinct from the legacy
// `QueuedForWorker` flow above. Uses FOR UPDATE SKIP LOCKED + the
// (state, slice_priority DESC, created_at ASC) compound index.
// ---------------------------------------------------------------------------

/// Atomically claim the highest-priority queued paid conjecture for a
/// worker. Sets state='claimed', stamps lease 5min ahead, records
/// `claimed_by`. Returns the full Model row for the worker to act on.
pub async fn atomic_claim_paid(
    db: &DatabaseConnection,
    worker_id: &str,
    available_lake_slots: i32,
) -> Result<Option<conjecture_jobs::Model>, DbErr> {
    // Stamp `allocated_slots` from the worker's reported capacity at
    // claim time. Floor 1 so a worker reporting 0 still has a valid
    // sanity-cap denominator on heartbeat, and ceiling 64 to defeat
    // a worker that lies about huge slot counts to inflate the cap.
    let allocated = available_lake_slots.clamp(1, 64);
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs SET
            claimed_by = $1,
            claimed_at = NOW(),
            lease_expires_at = NOW() + INTERVAL '5 minutes',
            last_heartbeat_at = NOW(),
            state = 'claimed',
            allocated_slots = $2
        WHERE id = (
            SELECT id FROM conjecture_jobs
            WHERE state = 'queued'
              AND (lake_slot_hours_quota::float - lake_slot_hours_consumed) > 0
            ORDER BY slice_priority DESC, created_at ASC
            FOR UPDATE SKIP LOCKED
            LIMIT 1
        )
        RETURNING *
        "#,
        [worker_id.into(), allocated.into()],
    );
    let model = conjecture_jobs::Entity::find()
        .from_raw_sql(stmt)
        .one(db)
        .await?;
    Ok(model)
}

/// Heartbeat: extend the lease by 5 minutes, accumulate progress
/// counters, debit lake-slot-hours. Returns `(new_consumed, exhausted)`
/// — when `exhausted` the caller must release_paid_claim with state
/// `budget_exhausted`. Sanity-cap on the consumed delta is applied
/// here using the row's last_heartbeat_at so a lying worker can't
/// burn the quota by reporting a huge delta.
pub async fn heartbeat_paid(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: &str,
    cand_attempted_delta: i32,
    cand_verified_delta: i32,
    consumed_delta_requested: f32,
) -> Result<Option<(f32, bool)>, DbErr> {
    let job = match get_by_id(db, id).await? {
        Some(j) => j,
        None => return Ok(None),
    };
    if job.claimed_by.as_deref() != Some(worker_id) {
        return Ok(None);
    }
    // Heartbeats are only valid while the row is in the active band.
    // Cancellation, budget exhaustion, and `proved` transitions all
    // terminalise the row — a late heartbeat must not flip state back
    // to `running` or eat more quota. The cancel transaction's race-
    // safety argument depends on this guard.
    if !matches!(job.state.as_str(), "claimed" | "running") {
        return Ok(None);
    }
    // Sanity cap: max 2× the wallclock since last heartbeat × slot
    // count. The slot count is the per-job `allocated_slots` stamped
    // at claim time, so the cap follows the actual capacity committed
    // to this conjecture instead of a cluster-wide fixed constant.
    // Defeats workers that report a huge fake delta.
    let wallclock_s = job
        .last_heartbeat_at
        .map(|t| (chrono::Utc::now() - t.with_timezone(&chrono::Utc)).num_seconds() as f32)
        .unwrap_or(60.0);
    // Ord::max disambiguated — sea_orm::ExprTrait::max is also in scope
    // via the wildcard `use sea_orm::*;` at the top of this file.
    let slots_held = std::cmp::max(job.allocated_slots, 1) as f32;
    let max_delta = 2.0 * (wallclock_s / 3600.0) * slots_held;
    let consumed_delta = consumed_delta_requested.clamp(0.0, max_delta);
    let new_consumed = job.lake_slot_hours_consumed + consumed_delta;
    let exhausted = new_consumed >= job.lake_slot_hours_quota as f32;
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"UPDATE conjecture_jobs SET
            last_heartbeat_at = NOW(),
            lease_expires_at = NOW() + INTERVAL '5 minutes',
            state = 'running',
            candidates_attempted = candidates_attempted + $2,
            candidates_verified = candidates_verified + $3,
            lake_slot_hours_consumed = lake_slot_hours_consumed + $4
           WHERE id = $1
             AND claimed_by = $5
             AND state IN ('claimed', 'running')"#,
        [
            id.into(),
            cand_attempted_delta.into(),
            cand_verified_delta.into(),
            consumed_delta.into(),
            worker_id.into(),
        ],
    );
    db.execute_raw(stmt).await?;
    Ok(Some((new_consumed, exhausted)))
}

/// Release a paid claim, transitioning to a terminal or back-to-queue
/// state. Valid `new_state` values: `"queued"` (release & requeue),
/// `"budget_exhausted"`, `"cancelled"`, `"proved"`. Clears
/// claim/lease columns. No-op if the worker doesn't own the lease.
pub async fn release_paid_claim(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: Option<&str>,
    new_state: &str,
) -> Result<u64, DbErr> {
    let stmt = if let Some(w) = worker_id {
        Statement::from_sql_and_values(
            DatabaseBackend::Postgres,
            r#"UPDATE conjecture_jobs SET
                state = $3,
                claimed_by = NULL,
                claimed_at = NULL,
                lease_expires_at = NULL
               WHERE id = $1 AND claimed_by = $2"#,
            [id.into(), w.into(), new_state.into()],
        )
    } else {
        Statement::from_sql_and_values(
            DatabaseBackend::Postgres,
            r#"UPDATE conjecture_jobs SET
                state = $2,
                claimed_by = NULL,
                claimed_at = NULL,
                lease_expires_at = NULL
               WHERE id = $1"#,
            [id.into(), new_state.into()],
        )
    };
    let r = db.execute_raw(stmt).await?;
    Ok(r.rows_affected())
}

/// Result of `cancel_paid_with_refund`.
#[derive(Debug, Clone)]
pub struct CancelOutcome {
    /// True iff the conditional UPDATE actually transitioned the row.
    /// Idempotent against double-clicks: the second call sees this as
    /// false and applies no refund.
    pub row_was_cancelled: bool,
    /// Credits returned to the user. 0 if `row_was_cancelled` is false
    /// or if any theorem was verified.
    pub refunded_credits: i32,
    /// True iff the row's prior state was `claimed` or `running`. The
    /// caller uses this to decide whether to release in-memory cluster
    /// capacity — for a `queued` cancel no slots were ever reserved.
    pub was_in_flight: bool,
    /// `allocated_slots` value the row carried at cancel time. Only
    /// meaningful when `was_in_flight == true`.
    pub allocated_slots: i32,
}

/// Atomically cancel a paid Researcher job and refund the user
/// proportionally to the unused budget. Single transaction:
///   1. SELECT … FOR UPDATE locks the row and snapshots its prior
///      state — needed because Postgres's UPDATE … RETURNING shows
///      post-update values, but we need the pre-cancel state to
///      decide `was_in_flight` correctly.
///   2. Bail if the row doesn't exist, the owner mismatches, or the
///      state is already terminal.
///   3. UPDATE state→'cancelled', clear claim columns; RETURNING
///      computes the refund amount inline.
///   4. If the refund > 0, increment users.research_credits.
///
/// `credits_spent` is reconstructed from the row:
///   credits_spent = (lake_slot_hours_quota / 96)
///                 + (slice_priority > 5 ? 1 : 0)
///
/// Refund formula: `floor(credits_spent × max(0, 1 - consumed/quota))`
/// when verified == 0, else 0.
pub async fn cancel_paid_with_refund(
    db: &DatabaseConnection,
    job_id: Uuid,
    owner_id: Uuid,
) -> Result<CancelOutcome, DbErr> {
    let txn = db.begin().await?;

    // Step 1: lock + snapshot prior state. FOR UPDATE serialises
    // concurrent heartbeats and double-cancel attempts behind us.
    let lock_stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"SELECT state, allocated_slots
             FROM conjecture_jobs
            WHERE id = $1 AND owner_id = $2
            FOR UPDATE"#,
        [job_id.into(), owner_id.into()],
    );
    let lock_row = txn.query_one_raw(lock_stmt).await?;
    let Some(lock_row) = lock_row else {
        // Row doesn't exist or owner mismatched.
        txn.rollback().await?;
        return Ok(CancelOutcome {
            row_was_cancelled: false,
            refunded_credits: 0,
            was_in_flight: false,
            allocated_slots: 0,
        });
    };
    let prior_state: String = lock_row.try_get_by_index(0)?;
    let allocated_slots: i32 = lock_row.try_get_by_index(1)?;
    if !matches!(prior_state.as_str(), "queued" | "claimed" | "running") {
        // Already terminal — nothing to do.
        txn.rollback().await?;
        return Ok(CancelOutcome {
            row_was_cancelled: false,
            refunded_credits: 0,
            was_in_flight: false,
            allocated_slots: 0,
        });
    }
    let was_in_flight = matches!(prior_state.as_str(), "claimed" | "running");

    // Step 2: terminal transition + refund-amount calc in one stmt.
    let cancel_stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"UPDATE conjecture_jobs
              SET state = 'cancelled',
                  completed_at = NOW(),
                  claimed_by = NULL,
                  claimed_at = NULL,
                  lease_expires_at = NULL
            WHERE id = $1
            RETURNING
                CASE
                    WHEN candidates_verified = 0 THEN
                      FLOOR(
                        ((lake_slot_hours_quota / 96)
                         + CASE WHEN slice_priority > 5 THEN 1 ELSE 0 END)::float
                        * GREATEST(0.0, 1.0 - (lake_slot_hours_consumed / lake_slot_hours_quota::float))
                      )::int
                    ELSE 0
                END AS refund_credits"#,
        [job_id.into()],
    );
    let row = txn.query_one_raw(cancel_stmt).await?
        .ok_or_else(|| DbErr::Custom(
            "cancel_paid_with_refund: row vanished between FOR UPDATE and UPDATE".into()
        ))?;
    let refund: i32 = row.try_get_by_index(0)?;

    // Step 3: apply refund (no-op when refund == 0).
    if refund > 0 {
        crate::query::users::refund_research_credits_n(&txn, owner_id, refund).await?;
    }

    txn.commit().await?;

    Ok(CancelOutcome {
        row_was_cancelled: true,
        refunded_credits: refund,
        was_in_flight,
        allocated_slots,
    })
}

/// Mark a paid job as `proved` on a verified-theorem hit. Appends the
/// theorem's id (8 bytes, hex-encoded by the caller) to the existing
/// `verified_theorem_ids` array, stamps `completed_at`, clears claim
/// columns. Idempotent — calling twice with the same hex still leaves
/// the row in `proved` state.
pub async fn mark_paid_proved(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: &str,
    theorem_id_hex: &str,
) -> Result<u64, DbErr> {
    let id_bytes = hex::decode(theorem_id_hex).unwrap_or_default();
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"UPDATE conjecture_jobs SET
            state = 'proved',
            outcome = 'Verified',
            verified_theorem_ids = COALESCE(verified_theorem_ids, ARRAY[]::BYTEA[]) || ARRAY[$3::BYTEA],
            completed_at = NOW(),
            claimed_by = NULL,
            claimed_at = NULL,
            lease_expires_at = NULL
           WHERE id = $1 AND claimed_by = $2"#,
        [id.into(), worker_id.into(), id_bytes.into()],
    );
    let r = db.execute_raw(stmt).await?;
    Ok(r.rows_affected())
}

/// Count rows in any of the given states.
pub async fn count_in_states(
    db: &DatabaseConnection,
    states: &[&str],
) -> Result<u64, DbErr> {
    use sea_orm::*;
    let owned: Vec<String> = states.iter().map(|s| (*s).to_owned()).collect();
    conjecture_jobs::Entity::find()
        .filter(conjecture_jobs::Column::State.is_in(owned))
        .count(db)
        .await
}
