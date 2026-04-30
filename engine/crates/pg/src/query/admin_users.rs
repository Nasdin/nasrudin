//! Admin-only user queries. Reads + targeted UPDATEs that the admin
//! panel uses, plus a cheap `list_paginated` for the user table view.

use sea_orm::{
    ColumnTrait, ConnectionTrait, Condition, DatabaseBackend, DatabaseConnection, DbErr,
    EntityTrait, FromQueryResult, PaginatorTrait, QueryFilter, QueryOrder, QuerySelect, Statement,
};
use uuid::Uuid;

use crate::entity::users;

#[derive(Clone, Debug, serde::Serialize)]
pub struct UserRow {
    pub id: Uuid,
    pub email: String,
    pub display_name: Option<String>,
    pub plan_tier: String,
    pub research_credits: i32,
    pub is_admin: bool,
    pub is_trusted: bool,
    pub spot_check_rate: Option<i32>,
    pub created_at: chrono::DateTime<chrono::FixedOffset>,
    pub stripe_customer_id: Option<String>,
}

impl From<users::Model> for UserRow {
    fn from(m: users::Model) -> Self {
        Self {
            id: m.id,
            email: m.email,
            display_name: m.display_name,
            plan_tier: m.plan_tier,
            research_credits: m.research_credits,
            is_admin: m.is_admin,
            is_trusted: m.is_trusted,
            spot_check_rate: m.spot_check_rate,
            created_at: m.created_at,
            stripe_customer_id: m.stripe_customer_id,
        }
    }
}

pub async fn list_paginated(
    db: &DatabaseConnection,
    page: u64,
    page_size: u64,
    search: Option<&str>,
    only_paid: bool,
) -> Result<(Vec<UserRow>, u64), DbErr> {
    let mut q = users::Entity::find();
    if let Some(s) = search
        && !s.is_empty()
    {
        let pat = format!("%{}%", s.to_lowercase());
        q = q.filter(
            Condition::any()
                .add(users::Column::Email.contains(&pat))
                .add(users::Column::DisplayName.contains(&pat)),
        );
    }
    if only_paid {
        q = q.filter(users::Column::PlanTier.ne("free"));
    }
    let total = q.clone().count(db).await?;
    let rows = q
        .order_by_desc(users::Column::CreatedAt)
        .paginate(db, page_size.max(1))
        .fetch_page(page.saturating_sub(1))
        .await?;
    Ok((rows.into_iter().map(Into::into).collect(), total))
}

pub async fn find_by_id(db: &DatabaseConnection, id: Uuid) -> Result<Option<users::Model>, DbErr> {
    users::Entity::find_by_id(id).one(db).await
}

pub async fn set_is_admin<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    value: bool,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET is_admin=$2 WHERE id=$1",
        [id.into(), value.into()],
    ))
    .await?;
    Ok(())
}

pub async fn set_is_trusted<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    value: bool,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET is_trusted=$2 WHERE id=$1",
        [id.into(), value.into()],
    ))
    .await?;
    Ok(())
}

pub async fn set_spot_check_rate<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    rate: Option<i32>,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET spot_check_rate=$2 WHERE id=$1",
        [id.into(), rate.into()],
    ))
    .await?;
    Ok(())
}

pub async fn set_plan_tier<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    tier: &str,
) -> Result<(), DbErr> {
    conn.execute_raw(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET plan_tier=$2 WHERE id=$1",
        [id.into(), tier.to_string().into()],
    ))
    .await?;
    Ok(())
}

#[derive(Debug, FromQueryResult)]
struct CreditsRow {
    research_credits: i32,
}

pub async fn adjust_credits<C: ConnectionTrait>(
    conn: &C,
    id: Uuid,
    delta: i32,
) -> Result<i32, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = GREATEST(0, research_credits + $2)
         WHERE id=$1
         RETURNING research_credits",
        [id.into(), delta.into()],
    );
    let row = CreditsRow::find_by_statement(stmt)
        .one(conn)
        .await?
        .ok_or_else(|| DbErr::RecordNotFound("user".into()))?;
    Ok(row.research_credits)
}

pub async fn count_admins<C: ConnectionTrait>(conn: &C) -> Result<u64, DbErr> {
    users::Entity::find()
        .filter(users::Column::IsAdmin.eq(true))
        .count(conn)
        .await
}
