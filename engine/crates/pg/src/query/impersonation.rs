//! Lifecycle helpers for `impersonation_sessions`.

use chrono::Utc;
use sea_orm::{
    ActiveModelTrait, ActiveValue::Set, ColumnTrait, ConnectionTrait, DbErr, EntityTrait,
    QueryFilter,
};
use uuid::Uuid;

use crate::entity::impersonation_sessions as ent;

pub async fn start<C: ConnectionTrait>(
    conn: &C,
    admin: Uuid,
    target: Uuid,
    expires_at: chrono::DateTime<Utc>,
    reason: String,
) -> Result<ent::Model, DbErr> {
    let id = Uuid::new_v4();
    let now: chrono::DateTime<chrono::FixedOffset> = Utc::now().into();
    let row = ent::ActiveModel {
        id: Set(id),
        admin_user_id: Set(admin),
        target_user_id: Set(target),
        started_at: Set(now),
        expires_at: Set(expires_at.into()),
        ended_at: Set(None),
        end_reason: Set(None),
        reason: Set(reason),
    };
    row.insert(conn).await
}

pub async fn end<C: ConnectionTrait>(conn: &C, id: Uuid, reason: &str) -> Result<(), DbErr> {
    let row = ent::Entity::find_by_id(id)
        .one(conn)
        .await?
        .ok_or_else(|| DbErr::RecordNotFound("impersonation session not found".into()))?;
    let mut active: ent::ActiveModel = row.into();
    active.ended_at = Set(Some(Utc::now().into()));
    active.end_reason = Set(Some(reason.to_string()));
    active.update(conn).await?;
    Ok(())
}

pub async fn find_active<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
) -> Result<Option<ent::Model>, DbErr> {
    let row = ent::Entity::find_by_id(id).one(conn).await?;
    Ok(row.filter(|r| r.ended_at.is_none() && r.expires_at > Utc::now()))
}

/// Sessions whose `expires_at` is in the past and which haven't been
/// manually ended. Driven by the 60-second expiry tick in the API crate.
pub async fn list_expired<C: ConnectionTrait>(conn: &C) -> Result<Vec<ent::Model>, DbErr> {
    let now: chrono::DateTime<chrono::FixedOffset> = Utc::now().into();
    ent::Entity::find()
        .filter(ent::Column::EndedAt.is_null())
        .filter(ent::Column::ExpiresAt.lt(now))
        .all(conn)
        .await
}
