//! `refund_records` CRUD + reconciler helpers.

use sea_orm::{
    ActiveModelTrait, ActiveValue::Set, ColumnTrait, ConnectionTrait, DatabaseBackend, DbErr,
    EntityTrait, FromQueryResult, QueryFilter, Statement,
};
use uuid::Uuid;

use crate::entity::refund_records as ent;

#[allow(clippy::too_many_arguments)]
pub async fn insert<C: ConnectionTrait>(
    conn: &C,
    user_id: Uuid,
    admin_user_id: Uuid,
    stripe_charge_id: &str,
    amount_cents: i32,
    currency: &str,
    reason: &str,
) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    ent::ActiveModel {
        id: Set(id),
        user_id: Set(user_id),
        admin_user_id: Set(admin_user_id),
        stripe_refund_id: Set(None),
        stripe_charge_id: Set(stripe_charge_id.into()),
        amount_cents: Set(amount_cents),
        currency: Set(currency.into()),
        reason: Set(reason.into()),
        status: Set("pending".into()),
        stripe_failure_reason: Set(None),
        requested_at: Set(chrono::Utc::now().into()),
        completed_at: Set(None),
    }
    .insert(conn)
    .await?;
    Ok(id)
}

pub async fn mark_succeeded<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    stripe_refund_id: &str,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE refund_records
         SET status='succeeded', stripe_refund_id=$2, completed_at=now()
         WHERE id=$1",
        [id.into(), stripe_refund_id.to_string().into()],
    ))
    .await?;
    Ok(())
}

pub async fn mark_failed<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    failure_reason: &str,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE refund_records
         SET status='failed', stripe_failure_reason=$2, completed_at=now()
         WHERE id=$1",
        [id.into(), failure_reason.to_string().into()],
    ))
    .await?;
    Ok(())
}

pub async fn list_pending_older_than<C: ConnectionTrait>(
    conn: &C,
    seconds: i64,
) -> Result<Vec<ent::Model>, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "SELECT id, user_id, admin_user_id, stripe_refund_id, stripe_charge_id, amount_cents,
                currency, reason, status, stripe_failure_reason, requested_at, completed_at
         FROM refund_records
         WHERE status='pending'
           AND requested_at < now() - make_interval(secs => $1)",
        [seconds.into()],
    );
    ent::Model::find_by_statement(stmt).all(conn).await
}

pub async fn find_by_id<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
) -> Result<Option<ent::Model>, DbErr> {
    ent::Entity::find_by_id(id).one(conn).await
}

pub async fn find_by_charge<C: ConnectionTrait>(
    conn: &C,
    charge: &str,
) -> Result<Vec<ent::Model>, DbErr> {
    ent::Entity::find()
        .filter(ent::Column::StripeChargeId.eq(charge))
        .all(conn)
        .await
}
