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

/// Atomically claim the right to run one LLM strategy refresh.
///
/// This serializes on `cluster_steering` only long enough to check the
/// last persisted strategy attempt and insert a marker row. The caller
/// performs the expensive LLM request after this transaction commits.
/// Other API processes will see the marker and continue with cached
/// RL-only steering instead of issuing their own LLM call.
pub async fn try_claim_strategy_refresh(
    db: &DatabaseConnection,
    scope: &str,
    config_json: serde_json::Value,
    model_id: &str,
    min_interval_secs: i64,
) -> Result<Option<Model>, DbErr> {
    let txn = db.begin().await?;
    txn.execute_raw(Statement::from_string(
        DatabaseBackend::Postgres,
        "LOCK TABLE cluster_steering IN EXCLUSIVE MODE".to_owned(),
    ))
    .await?;

    let cutoff =
        chrono::Utc::now() - chrono::Duration::seconds(std::cmp::max(min_interval_secs, 0));
    let recent = Entity::find()
        .filter(
            Condition::any()
                .add(Column::PromptTokens.is_not_null())
                .add(Column::CompletionTokens.is_not_null())
                .add(Column::ValidationFailed.eq(true)),
        )
        .filter(Column::StartedAt.gt(cutoff.fixed_offset()))
        .order_by_desc(Column::StartedAt)
        .limit(1)
        .one(&txn)
        .await?;
    if recent.is_some() {
        txn.commit().await?;
        return Ok(None);
    }

    let am = ActiveModel {
        id: Set(Uuid::new_v4()),
        started_at: Set(chrono::Utc::now().into()),
        ended_at: Set(None),
        scope: Set(scope.to_owned()),
        config_json: Set(config_json),
        outcome_json: Set(None),
        validation_failed: Set(true),
        model_id: Set(model_id.to_owned()),
        prompt_tokens: Set(None),
        completion_tokens: Set(None),
    };
    let row = am.insert(&txn).await?;
    txn.commit().await?;
    Ok(Some(row))
}

/// Replace a previously-claimed strategy marker with the final LLM
/// result or fallback config.
pub async fn update_strategy_refresh_result(
    db: &DatabaseConnection,
    id: Uuid,
    config_json: serde_json::Value,
    validation_failed: bool,
    prompt_tokens: Option<i32>,
    completion_tokens: Option<i32>,
) -> Result<Model, DbErr> {
    let row = Entity::find_by_id(id)
        .one(db)
        .await?
        .ok_or_else(|| DbErr::RecordNotFound(format!("cluster_steering id {id}")))?;
    let mut am: ActiveModel = row.into();
    am.config_json = Set(config_json);
    am.validation_failed = Set(validation_failed);
    am.prompt_tokens = Set(prompt_tokens);
    am.completion_tokens = Set(completion_tokens);
    am.update(db).await
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

/// Most recent cycle that attempted a strategy refresh. RL-only cycles
/// reuse cached steering and store NULL token counts with
/// `validation_failed=false`; strategy attempts either report tokens
/// or persist `validation_failed=true` when the call/parse/budget gate
/// failed before usage was available.
pub async fn most_recent_strategy_refresh(db: &DatabaseConnection) -> Result<Option<Model>, DbErr> {
    Entity::find()
        .filter(
            Condition::any()
                .add(Column::PromptTokens.is_not_null())
                .add(Column::CompletionTokens.is_not_null())
                .add(Column::ValidationFailed.eq(true)),
        )
        .order_by_desc(Column::StartedAt)
        .limit(1)
        .one(db)
        .await
}

/// Actual provider-reported steerer token usage since `cutoff`.
///
/// This powers the hard rolling LLM spend guard. RL-only cycles store
/// NULL token counts and therefore contribute 0. Strategy attempts
/// that failed before provider usage was available also contribute 0,
/// which matches reported billable usage.
pub async fn llm_tokens_used_since(
    db: &DatabaseConnection,
    cutoff: chrono::DateTime<chrono::Utc>,
) -> Result<i64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "SELECT COALESCE(SUM(COALESCE(prompt_tokens, 0) + COALESCE(completion_tokens, 0)), 0)::BIGINT AS used_tokens \
         FROM cluster_steering \
         WHERE started_at >= $1",
        [cutoff.fixed_offset().into()],
    );
    let row = db
        .query_one_raw(stmt)
        .await?
        .ok_or_else(|| DbErr::RecordNotFound("cluster_steering token sum".into()))?;
    row.try_get::<i64>("", "used_tokens")
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
