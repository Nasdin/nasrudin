//! `bulk_runs` CRUD + JSONB-append failures + restart reaper.

use sea_orm::{
    ActiveModelTrait, ActiveValue::Set, ColumnTrait, ConnectionTrait, DatabaseBackend, DbErr,
    EntityTrait, PaginatorTrait, QueryFilter, QueryOrder, QuerySelect, Statement,
};
use uuid::Uuid;

use crate::entity::bulk_runs as ent;

pub async fn insert<C: ConnectionTrait>(
    conn: &C,
    admin: Uuid,
    action: &str,
    params: serde_json::Value,
    total: i32,
) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    ent::ActiveModel {
        id: Set(id),
        started_by_admin_id: Set(admin),
        action: Set(action.into()),
        params: Set(params),
        total_count: Set(total),
        completed_count: Set(0),
        failed_count: Set(0),
        status: Set("running".into()),
        started_at: Set(chrono::Utc::now().into()),
        completed_at: Set(None),
        failures: Set(None),
    }
    .insert(conn)
    .await?;
    Ok(id)
}

pub async fn increment_completed<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE bulk_runs SET completed_count = completed_count + 1 WHERE id=$1",
        [id.into()],
    ))
    .await?;
    Ok(())
}

pub async fn increment_failed<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    failure_record: serde_json::Value,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE bulk_runs
         SET failed_count = failed_count + 1,
             failures = COALESCE(failures, '[]'::jsonb) || $2::jsonb
         WHERE id=$1",
        [id.into(), failure_record.into()],
    ))
    .await?;
    Ok(())
}

pub async fn complete<C: ConnectionTrait>(conn: &C, id: Uuid, status: &str) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE bulk_runs SET status=$2, completed_at=now() WHERE id=$1",
        [id.into(), status.to_string().into()],
    ))
    .await?;
    Ok(())
}

pub async fn reap_stale<C: ConnectionTrait>(conn: &C) -> Result<u64, DbErr> {
    let res = conn
        .execute_raw(Statement::from_sql_and_values(
            DatabaseBackend::Postgres,
            "UPDATE bulk_runs SET status='aborted', completed_at=now()
             WHERE status='running' AND started_at < now() - INTERVAL '1 hour'",
            [],
        ))
        .await?;
    Ok(res.rows_affected())
}

pub async fn find_by_id<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
) -> Result<Option<ent::Model>, DbErr> {
    ent::Entity::find_by_id(id).one(conn).await
}

pub async fn list_recent<C: ConnectionTrait>(
    conn: &C,
    limit: u64,
) -> Result<Vec<ent::Model>, DbErr> {
    ent::Entity::find()
        .order_by_desc(ent::Column::StartedAt)
        .limit(limit)
        .all(conn)
        .await
}

pub async fn count_active<C: ConnectionTrait>(conn: &C) -> Result<u64, DbErr> {
    ent::Entity::find()
        .filter(ent::Column::Status.eq("running"))
        .count(conn)
        .await
}
