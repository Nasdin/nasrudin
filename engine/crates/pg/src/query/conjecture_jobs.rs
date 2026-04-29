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
