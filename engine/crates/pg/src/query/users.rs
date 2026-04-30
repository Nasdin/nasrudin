use sea_orm::*;
use uuid::Uuid;

use crate::entity::users;

/// Create a new user account. Returns the inserted model.
pub async fn create_user(
    db: &DatabaseConnection,
    email: &str,
    password_hash: &str,
    display_name: Option<&str>,
) -> Result<users::Model, DbErr> {
    let model = users::ActiveModel {
        id: Set(Uuid::new_v4()),
        email: Set(email.to_owned()),
        password_hash: Set(password_hash.to_owned()),
        display_name: Set(display_name.map(|s| s.to_owned())),
        created_at: Set(chrono::Utc::now().into()),
        plan_tier: Set("free".to_owned()),
        stripe_customer_id: Set(None),
        stripe_subscription_id: Set(None),
        current_period_end: Set(None),
        plan_cycle_start: Set(None),
        research_credits: Set(0),
    };
    model.insert(db).await
}

/// Persist a Stripe customer id on the user row. Called the first time we
/// initiate Checkout for a user — subsequent checkouts reuse the customer.
pub async fn set_stripe_customer_id(
    db: &DatabaseConnection,
    user_id: Uuid,
    customer_id: &str,
) -> Result<(), DbErr> {
    users::Entity::update_many()
        .col_expr(
            users::Column::StripeCustomerId,
            sea_orm::sea_query::Expr::value(customer_id),
        )
        .filter(users::Column::Id.eq(user_id))
        .exec(db)
        .await
        .map(|_| ())
}

/// Find a user by their UUID.
pub async fn find_by_id(db: &DatabaseConnection, id: Uuid) -> Result<Option<users::Model>, DbErr> {
    users::Entity::find_by_id(id).one(db).await
}

/// Find a user by email address.
pub async fn find_by_email(
    db: &DatabaseConnection,
    email: &str,
) -> Result<Option<users::Model>, DbErr> {
    users::Entity::find()
        .filter(users::Column::Email.eq(email))
        .one(db)
        .await
}

/// Update a user's display name.
pub async fn update_display_name(
    db: &DatabaseConnection,
    id: Uuid,
    display_name: Option<&str>,
) -> Result<users::Model, DbErr> {
    let model = users::ActiveModel {
        id: Set(id),
        display_name: Set(display_name.map(|s| s.to_owned())),
        ..Default::default()
    };
    model.update(db).await
}

/// Delete a user account. Cascades to sessions, saved_searches, user_preferences.
pub async fn delete_user(db: &DatabaseConnection, id: Uuid) -> Result<DeleteResult, DbErr> {
    users::Entity::delete_by_id(id).exec(db).await
}

/// Atomic credit decrement for the paid Researcher tier. Returns
/// `Ok(true)` when one credit was successfully consumed; `Ok(false)`
/// when the user has zero credits (the UPDATE matches no rows). The
/// `WHERE research_credits > 0` clause makes this safe under
/// concurrent submission attempts — only one wins.
pub async fn try_decrement_research_credits(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<bool, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = research_credits - 1 \
         WHERE id = $1 AND research_credits > 0",
        [user_id.into()],
    );
    let r = db.execute_raw(stmt).await?;
    Ok(r.rows_affected() == 1)
}

/// Refund one research credit. Used by cancel-before-progress and the
/// (rare) atomic create-failure path. No bound check — refunds are
/// privileged operations the caller has already justified.
pub async fn refund_research_credit(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = research_credits + 1 WHERE id = $1",
        [user_id.into()],
    );
    let r = db.execute_raw(stmt).await?;
    Ok(r.rows_affected())
}

/// Grant `credits` research credits to the Stripe customer's user iff
/// the new `cycle_start` advances past the user's recorded
/// `plan_cycle_start` — i.e. it's a fresh billing period, not just a
/// payment-method update or other no-op `subscription.updated`. This
/// makes the webhook idempotent for repeated updates within the same
/// period: Stripe can resend the same subscription event N times and
/// we still grant credits exactly once per period.
///
/// The grant *sets* (not adds) so the user always has exactly `credits`
/// at the start of a fresh period — lose-it-or-use-it semantics
/// matching `targeted_searches_per_period`. Returns rows affected
/// (1 = granted, 0 = same period or no matching customer).
pub async fn grant_research_credits_on_period_advance(
    db: &DatabaseConnection,
    stripe_customer_id: &str,
    new_cycle_start: chrono::DateTime<chrono::Utc>,
    credits: i32,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = $3 \
         WHERE stripe_customer_id = $1 \
           AND (plan_cycle_start IS NULL OR plan_cycle_start < $2)",
        [
            stripe_customer_id.into(),
            new_cycle_start.fixed_offset().into(),
            credits.into(),
        ],
    );
    let r = db.execute_raw(stmt).await?;
    Ok(r.rows_affected())
}
