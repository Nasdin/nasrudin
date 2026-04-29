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
