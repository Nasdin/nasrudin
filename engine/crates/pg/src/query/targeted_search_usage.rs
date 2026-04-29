//! Per-period count + record helpers for the targeted-search quota.
//!
//! `count_in_period` is called on conjecture-create to gate the request;
//! `record` writes a row immediately after the gate passes so the count
//! reflects the new usage on subsequent requests.

use chrono::{DateTime, Utc};
use sea_orm::ActiveValue::*;
use sea_orm::prelude::*;
use uuid::Uuid;

use crate::entity::targeted_search_usage as tsu;

pub async fn count_in_period(
    db: &DatabaseConnection,
    user_id: Uuid,
    period_start: DateTime<Utc>,
) -> Result<u64, DbErr> {
    tsu::Entity::find()
        .filter(tsu::Column::UserId.eq(user_id))
        .filter(tsu::Column::PeriodStart.gte(period_start.fixed_offset()))
        .count(db)
        .await
}

pub async fn record(
    db: &DatabaseConnection,
    user_id: Uuid,
    conjecture_job_id: Uuid,
    period_start: DateTime<Utc>,
) -> Result<(), DbErr> {
    tsu::ActiveModel {
        id: Set(Uuid::new_v4()),
        user_id: Set(user_id),
        conjecture_job_id: Set(conjecture_job_id),
        period_start: Set(period_start.fixed_offset()),
        created_at: Set(Utc::now().fixed_offset()),
    }
    .insert(db)
    .await
    .map(|_| ())
}
