use sea_orm::*;
use uuid::Uuid;

use crate::entity::users;

/// Create a new user backed by a Firebase identity. The caller has already
/// verified the Firebase ID token; `firebase_uid` is the verified `sub`
/// claim. Returns the inserted model.
pub async fn create_firebase_user(
    db: &DatabaseConnection,
    firebase_uid: &str,
    email: &str,
    display_name: Option<&str>,
) -> Result<users::Model, DbErr> {
    let model = users::ActiveModel {
        id: Set(Uuid::new_v4()),
        email: Set(email.to_owned()),
        display_name: Set(display_name.map(|s| s.to_owned())),
        created_at: Set(chrono::Utc::now().into()),
        plan_tier: Set("free".to_owned()),
        stripe_customer_id: Set(None),
        stripe_subscription_id: Set(None),
        current_period_end: Set(None),
        plan_cycle_start: Set(None),
        research_credits: Set(0),
        firebase_uid: Set(firebase_uid.to_owned()),
        is_admin: Set(false),
        is_trusted: Set(false),
        spot_check_rate: Set(None),
        country_code: Set(None),
    };
    model.insert(db).await
}

/// Find a user by Firebase UID. Used by the session-exchange endpoint
/// to decide insert-vs-return.
pub async fn find_by_firebase_uid(
    db: &DatabaseConnection,
    firebase_uid: &str,
) -> Result<Option<users::Model>, DbErr> {
    users::Entity::find()
        .filter(users::Column::FirebaseUid.eq(firebase_uid))
        .one(db)
        .await
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

/// Find a user by their Stripe customer id. Used by the sponsorship
/// webhook to resolve `event.customer` → `users.id` before recording
/// in `user_sponsorships`.
pub async fn find_by_stripe_customer_id<C: ConnectionTrait>(
    db: &C,
    stripe_customer_id: &str,
) -> Result<Option<users::Model>, DbErr> {
    users::Entity::find()
        .filter(users::Column::StripeCustomerId.eq(stripe_customer_id))
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

/// Update a user's ISO-3166-1 alpha-2 country code (uppercase, 2 chars).
/// `None` clears it. Validation lives at the handler boundary in
/// `crates/api/src/handlers/me.rs` — we trust the value here.
pub async fn update_country_code(
    db: &DatabaseConnection,
    id: Uuid,
    country_code: Option<&str>,
) -> Result<users::Model, DbErr> {
    let model = users::ActiveModel {
        id: Set(id),
        country_code: Set(country_code.map(|s| s.to_owned())),
        ..Default::default()
    };
    model.update(db).await
}

/// Delete a user account. Cascades to sessions, saved_searches, user_preferences.
pub async fn delete_user(db: &DatabaseConnection, id: Uuid) -> Result<DeleteResult, DbErr> {
    users::Entity::delete_by_id(id).exec(db).await
}

/// Atomic multi-credit decrement for the paid Researcher tier. Returns
/// `Some(new_remaining)` when the predicate `research_credits >= n`
/// holds and the row was updated; `None` when the user can't afford
/// `n`. The `WHERE research_credits >= $n` clause makes this safe under
/// concurrent submission attempts — only one wins.
///
/// `n = 0` is allowed: returns the current `research_credits` without
/// modifying the row, so callers can read-without-decrementing inside
/// the same transaction they used for the (failed) atomic decrement.
///
/// Takes `&impl ConnectionTrait` so callers can run this inside a
/// transaction (the API submit path needs decrement + insert atomic).
pub async fn try_decrement_research_credits_n(
    db: &impl ConnectionTrait,
    user_id: Uuid,
    n: i32,
) -> Result<Option<i32>, DbErr> {
    if n == 0 {
        let m = crate::entity::users::Entity::find_by_id(user_id)
            .one(db)
            .await?;
        return Ok(m.map(|u| u.research_credits));
    }
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = research_credits - $2 \
         WHERE id = $1 AND research_credits >= $2 \
         RETURNING research_credits",
        [user_id.into(), n.into()],
    );
    let row = db.query_one_raw(stmt).await?;
    let Some(row) = row else { return Ok(None) };
    Ok(Some(row.try_get_by_index::<i32>(0)?))
}

/// Single-credit wrapper. Kept for backward compatibility with callers
/// that haven't been ported to the multi-credit path; equivalent to
/// `try_decrement_research_credits_n(db, user_id, 1).map(|x| x.is_some())`.
pub async fn try_decrement_research_credits(
    db: &impl ConnectionTrait,
    user_id: Uuid,
) -> Result<bool, DbErr> {
    Ok(try_decrement_research_credits_n(db, user_id, 1)
        .await?
        .is_some())
}

/// Multi-credit refund for the paid Researcher tier. No bound check —
/// refunds are privileged operations the caller has already justified
/// (cancel-with-no-progress, etc.).
///
/// `n <= 0` is a no-op (returns 0 rows affected) so cancel paths can
/// call it unconditionally without branching on whether a refund is
/// actually owed.
///
/// Takes `&impl ConnectionTrait` so callers can run this inside a
/// transaction (the cancel path needs state-flip + refund atomic).
pub async fn refund_research_credits_n(
    db: &impl ConnectionTrait,
    user_id: Uuid,
    n: i32,
) -> Result<u64, DbErr> {
    if n <= 0 {
        return Ok(0);
    }
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = research_credits + $2 WHERE id = $1",
        [user_id.into(), n.into()],
    );
    let r = db.execute_raw(stmt).await?;
    Ok(r.rows_affected())
}

/// Single-credit wrapper. Kept for backward compatibility.
pub async fn refund_research_credit(
    db: &impl ConnectionTrait,
    user_id: Uuid,
) -> Result<u64, DbErr> {
    refund_research_credits_n(db, user_id, 1).await
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
