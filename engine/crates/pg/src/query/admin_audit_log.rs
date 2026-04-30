//! Insert / list helpers for `admin_audit_log`.

use std::net::IpAddr;

use sea_orm::{
    ColumnTrait, ConnectionTrait, DatabaseBackend, DbErr, EntityTrait, QueryFilter, QueryOrder,
    QuerySelect, Statement,
};
use uuid::Uuid;

use crate::entity::admin_audit_log;

#[allow(clippy::too_many_arguments)]
pub async fn insert<C: ConnectionTrait>(
    conn: &C,
    actor_user_id: Uuid,
    target_user_id: Option<Uuid>,
    impersonating_user_id: Option<Uuid>,
    action: &str,
    before_value: Option<serde_json::Value>,
    after_value: Option<serde_json::Value>,
    reason: String,
    request_ip: Option<IpAddr>,
    user_agent: Option<String>,
) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "INSERT INTO admin_audit_log
            (id, actor_user_id, target_user_id, action, before_value, after_value,
             reason, impersonating_user_id, request_ip, user_agent)
         VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)",
        [
            id.into(),
            actor_user_id.into(),
            target_user_id.into(),
            action.to_string().into(),
            before_value.unwrap_or(serde_json::Value::Null).into(),
            after_value.unwrap_or(serde_json::Value::Null).into(),
            reason.into(),
            impersonating_user_id.into(),
            request_ip.map(|ip| ip.to_string()).into(),
            user_agent.into(),
        ],
    );
    conn.execute_raw(stmt).await?;
    Ok(id)
}

pub async fn list_by_target<C: ConnectionTrait>(
    conn: &C,
    target: Uuid,
    limit: u64,
) -> Result<Vec<admin_audit_log::Model>, DbErr> {
    admin_audit_log::Entity::find()
        .filter(admin_audit_log::Column::TargetUserId.eq(target))
        .order_by_desc(admin_audit_log::Column::CreatedAt)
        .limit(limit)
        .all(conn)
        .await
}

pub async fn list_recent<C: ConnectionTrait>(
    conn: &C,
    limit: u64,
) -> Result<Vec<admin_audit_log::Model>, DbErr> {
    admin_audit_log::Entity::find()
        .order_by_desc(admin_audit_log::Column::CreatedAt)
        .limit(limit)
        .all(conn)
        .await
}

pub async fn list_filtered<C: ConnectionTrait>(
    conn: &C,
    actor: Option<Uuid>,
    target: Option<Uuid>,
    action: Option<&str>,
    limit: u64,
    offset: u64,
) -> Result<Vec<admin_audit_log::Model>, DbErr> {
    let mut q = admin_audit_log::Entity::find();
    if let Some(a) = actor {
        q = q.filter(admin_audit_log::Column::ActorUserId.eq(a));
    }
    if let Some(t) = target {
        q = q.filter(admin_audit_log::Column::TargetUserId.eq(t));
    }
    if let Some(act) = action {
        q = q.filter(admin_audit_log::Column::Action.eq(act));
    }
    q.order_by_desc(admin_audit_log::Column::CreatedAt)
        .limit(limit)
        .offset(offset)
        .all(conn)
        .await
}
