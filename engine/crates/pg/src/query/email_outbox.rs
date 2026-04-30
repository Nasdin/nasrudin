//! Outbox CRUD with exponential-backoff claim semantics.

use sea_orm::{
    ActiveModelTrait, ActiveValue::Set, ColumnTrait, ConnectionTrait, DatabaseBackend, DbErr,
    EntityTrait, FromQueryResult, PaginatorTrait, QueryFilter, QueryOrder, QuerySelect, Statement,
};
use uuid::Uuid;

use crate::entity::email_outbox as ent;

#[allow(clippy::too_many_arguments)]
pub async fn queue<C: ConnectionTrait>(
    conn: &C,
    to_user_id: Option<Uuid>,
    to_address: &str,
    template: &str,
    subject: &str,
    body_text: &str,
    body_html: Option<&str>,
    queued_by_admin_id: Option<Uuid>,
    queued_by_action: Option<&str>,
) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    ent::ActiveModel {
        id: Set(id),
        to_user_id: Set(to_user_id),
        to_address: Set(to_address.into()),
        template: Set(template.into()),
        subject: Set(subject.into()),
        body_text: Set(body_text.into()),
        body_html: Set(body_html.map(str::to_string)),
        status: Set("queued".into()),
        attempts: Set(0),
        last_attempt_at: Set(None),
        last_error: Set(None),
        provider_message_id: Set(None),
        queued_by_admin_id: Set(queued_by_admin_id),
        queued_by_action: Set(queued_by_action.map(str::to_string)),
        created_at: Set(chrono::Utc::now().into()),
        sent_at: Set(None),
    }
    .insert(conn)
    .await?;
    Ok(id)
}

/// Claim up to `limit` rows that are eligible to send right now: status
/// `queued`, or `failed_retrying` with attempts < 5 whose backoff window
/// (5 min × 2^attempts) has elapsed since the last attempt.
pub async fn claim_pending<C: ConnectionTrait>(
    conn: &C,
    limit: u32,
) -> Result<Vec<ent::Model>, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        SELECT id, to_user_id, to_address, template, subject, body_text, body_html, status,
               attempts, last_attempt_at, last_error, provider_message_id, queued_by_admin_id,
               queued_by_action, created_at, sent_at
        FROM email_outbox
        WHERE status = 'queued'
           OR (status = 'failed_retrying' AND attempts < 5
               AND (last_attempt_at IS NULL
                    OR last_attempt_at < now() - (interval '5 minute' * pow(2, attempts))))
        ORDER BY created_at ASC
        LIMIT $1
        "#,
        [(limit as i64).into()],
    );
    ent::Model::find_by_statement(stmt).all(conn).await
}

pub async fn mark_sent<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    provider_message_id: &str,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE email_outbox
         SET status='sent', sent_at=now(), provider_message_id=$2,
             last_attempt_at=now(), attempts=attempts+1
         WHERE id=$1",
        [id.into(), provider_message_id.to_string().into()],
    ))
    .await?;
    Ok(())
}

pub async fn mark_failed_retrying<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    err: &str,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE email_outbox
         SET status='failed_retrying', last_attempt_at=now(),
             attempts=attempts+1, last_error=$2
         WHERE id=$1",
        [id.into(), err.to_string().into()],
    ))
    .await?;
    Ok(())
}

pub async fn mark_failed_terminal<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    err: &str,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE email_outbox
         SET status='failed_terminal', last_attempt_at=now(),
             attempts=attempts+1, last_error=$2
         WHERE id=$1",
        [id.into(), err.to_string().into()],
    ))
    .await?;
    Ok(())
}

pub async fn cancel_dependent<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE email_outbox SET status='cancelled_dependent'
         WHERE id=$1 AND status='queued'",
        [id.into()],
    ))
    .await?;
    Ok(())
}

pub async fn list_recent<C: ConnectionTrait>(
    conn: &C,
    limit: u64,
    offset: u64,
) -> Result<Vec<ent::Model>, DbErr> {
    ent::Entity::find()
        .order_by_desc(ent::Column::CreatedAt)
        .limit(limit)
        .offset(offset)
        .all(conn)
        .await
}

pub async fn find_by_id<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
) -> Result<Option<ent::Model>, DbErr> {
    ent::Entity::find_by_id(id).one(conn).await
}

pub async fn find_by_provider_message_id<C: ConnectionTrait>(
    conn: &C,
    msg_id: &str,
) -> Result<Option<ent::Model>, DbErr> {
    ent::Entity::find()
        .filter(ent::Column::ProviderMessageId.eq(msg_id))
        .one(conn)
        .await
}

pub async fn count_by_status<C: ConnectionTrait>(conn: &C, status: &str) -> Result<u64, DbErr> {
    ent::Entity::find()
        .filter(ent::Column::Status.eq(status))
        .count(conn)
        .await
}
