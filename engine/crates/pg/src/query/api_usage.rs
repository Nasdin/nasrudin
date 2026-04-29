//! `api_usage_daily` increment + read helpers.
//!
//! `increment_and_get` does an atomic UPSERT and returns the post-increment
//! count so the rate-limit middleware can decide 429 in one round trip.
//! `count_today` is the read-only path used by `/api/billing/me`.

use chrono::NaiveDate;
use sea_orm::prelude::*;
use sea_orm::{ConnectionTrait, DatabaseBackend, ExprTrait, Statement};
use uuid::Uuid;

use crate::entity::api_usage_daily as aud;

pub async fn increment_and_get(
    db: &DatabaseConnection,
    user_id: Uuid,
    day: NaiveDate,
) -> Result<i64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "INSERT INTO api_usage_daily (user_id, day, request_count) \
         VALUES ($1, $2, 1) \
         ON CONFLICT (user_id, day) DO UPDATE \
         SET request_count = api_usage_daily.request_count + 1 \
         RETURNING request_count",
        [user_id.into(), day.into()],
    );
    let row = db
        .query_one_raw(stmt)
        .await?
        .ok_or(DbErr::RecordNotFound("api_usage_daily upsert".into()))?;
    row.try_get::<i64>("", "request_count")
}

pub async fn count_today(
    db: &DatabaseConnection,
    user_id: Uuid,
    day: NaiveDate,
) -> Result<i64, DbErr> {
    Ok(aud::Entity::find_by_id((user_id, day))
        .one(db)
        .await?
        .map(|m| m.request_count)
        .unwrap_or(0))
}
