//! CRUD helpers for the `cluster_steering` history table.
//!
//! The steerer task in `physics-api` opens a row at the start of each
//! cycle (`insert_new_cycle`), populates the outcome JSON when the
//! cycle closes (`close_cycle`), and reads the last N rows newest-first
//! to feed the next cycle's prompt (`list_recent`). `last_validated`
//! returns the most recent successfully-validated config so the loop
//! can fall back when the model returns garbage.

use sea_orm::*;
use uuid::Uuid;

use crate::entity::cluster_steering::{ActiveModel, Column, Entity, Model};

/// Begin a new steering cycle. `outcome_json` and token counts remain
/// NULL until the next cycle's tick runs `close_cycle`.
pub async fn insert_new_cycle(
    db: &DatabaseConnection,
    scope: &str,
    config_json: serde_json::Value,
    model_id: &str,
    validation_failed: bool,
    prompt_tokens: Option<i32>,
    completion_tokens: Option<i32>,
) -> Result<Model, DbErr> {
    let am = ActiveModel {
        id: Set(Uuid::new_v4()),
        started_at: Set(chrono::Utc::now().into()),
        ended_at: Set(None),
        scope: Set(scope.to_owned()),
        config_json: Set(config_json),
        outcome_json: Set(None),
        validation_failed: Set(validation_failed),
        model_id: Set(model_id.to_owned()),
        prompt_tokens: Set(prompt_tokens),
        completion_tokens: Set(completion_tokens),
    };
    am.insert(db).await
}

/// Stamp `ended_at = NOW()` and write the computed outcome JSON.
/// Returns rows affected (0 = the cycle id was not found).
pub async fn close_cycle(
    db: &DatabaseConnection,
    id: Uuid,
    outcome_json: serde_json::Value,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE cluster_steering SET ended_at = NOW(), outcome_json = $2 WHERE id = $1",
        [id.into(), outcome_json.into()],
    );
    let res = db.execute_raw(stmt).await?;
    Ok(res.rows_affected())
}

/// History feed for the steerer prompt and admin UI. Newest first.
pub async fn list_recent(db: &DatabaseConnection, n: u64) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .order_by_desc(Column::StartedAt)
        .limit(n)
        .all(db)
        .await
}

/// Most recent cycle whose `validation_failed = false` — the
/// fallback config used when the latest LLM response is unusable.
pub async fn last_validated(db: &DatabaseConnection) -> Result<Option<Model>, DbErr> {
    Entity::find()
        .filter(Column::ValidationFailed.eq(false))
        .order_by_desc(Column::StartedAt)
        .one(db)
        .await
}

/// Most recent cycle (any status). Used by the outcome-capture path
/// to find the row that needs `close_cycle` called on it.
pub async fn most_recent(db: &DatabaseConnection) -> Result<Option<Model>, DbErr> {
    Entity::find()
        .order_by_desc(Column::StartedAt)
        .limit(1)
        .one(db)
        .await
}

/// Retention sweep: keep the last `keep` rows, delete older ones.
/// Cluster-steering history grows ~144 rows/day at 10-min cadence; we
/// trim aggressively because only the last ~10 are ever read by the
/// prompt and the admin UI paginates.
pub async fn prune_to_last_n(db: &DatabaseConnection, keep: u64) -> Result<u64, DbErr> {
    let cutoff = Entity::find()
        .order_by_desc(Column::StartedAt)
        .offset(keep)
        .limit(1)
        .one(db)
        .await?;
    let Some(cutoff) = cutoff else {
        return Ok(0);
    };
    let res = Entity::delete_many()
        .filter(Column::StartedAt.lt(cutoff.started_at))
        .exec(db)
        .await?;
    Ok(res.rows_affected)
}
