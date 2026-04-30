//! Read/upsert helpers for `llm_proposed_targets`.

use crate::entity::llm_proposed_targets::*;
use chrono::Utc;
use sea_orm::*;

/// Insert a target if missing, else leave it alone (the existing
/// row's status / proposed_at are authoritative — re-emitting the
/// same target_id should not reset its lifecycle).
pub async fn upsert_open(
    db: &DatabaseConnection,
    target_id: &str,
    latex: &str,
    domain: &str,
    weight: f64,
) -> Result<(), DbErr> {
    let exists = Entity::find_by_id(target_id.to_string()).one(db).await?;
    if exists.is_some() {
        return Ok(());
    }
    let am = ActiveModel {
        target_id: Set(target_id.into()),
        latex: Set(latex.into()),
        domain: Set(domain.into()),
        weight: Set(weight),
        status: Set("open".into()),
        proposed_at: Set(Utc::now().fixed_offset()),
        updated_at: Set(Utc::now().fixed_offset()),
    };
    Entity::insert(am).exec(db).await?;
    Ok(())
}

/// Update an existing target's status. Caller is responsible for
/// validating the new status against the lifecycle (open → proving
/// → proved | abandoned). Unknown target_ids are silently ignored.
pub async fn set_status(
    db: &DatabaseConnection,
    target_id: &str,
    new_status: &str,
) -> Result<(), DbErr> {
    let arm = Entity::find_by_id(target_id.to_string()).one(db).await?;
    let Some(m) = arm else {
        return Ok(());
    };
    let mut am: ActiveModel = m.into();
    am.status = Set(new_status.into());
    am.updated_at = Set(Utc::now().fixed_offset());
    am.save(db).await?;
    Ok(())
}

/// Most recent `n` targets, newest first. Used by the steerer's
/// prompt builder so the LLM sees its self-curriculum history.
pub async fn recent(db: &DatabaseConnection, n: u64) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .order_by_desc(Column::ProposedAt)
        .limit(n)
        .all(db)
        .await
}

/// Targets currently in the "open" or "proving" state. Used by the
/// prompt to show the LLM what's still in flight.
pub async fn in_flight(db: &DatabaseConnection, n: u64) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .filter(Column::Status.is_in(["open", "proving"]))
        .order_by_desc(Column::ProposedAt)
        .limit(n)
        .all(db)
        .await
}
