use sea_orm::*;
use uuid::Uuid;

use crate::entity::users;

/// Create a new user account. Pass `None` for `password_hash` to create an
/// OAuth-only user (sign-in flows that lack a password). Returns the inserted
/// model.
pub async fn create_user(
    db: &DatabaseConnection,
    email: &str,
    password_hash: Option<&str>,
    display_name: Option<&str>,
) -> Result<users::Model, DbErr> {
    let model = users::ActiveModel {
        id: Set(Uuid::new_v4()),
        email: Set(email.to_owned()),
        password_hash: Set(password_hash.map(|s| s.to_owned())),
        display_name: Set(display_name.map(|s| s.to_owned())),
        created_at: Set(chrono::Utc::now().into()),
        plan_tier: Set("free".to_owned()),
        stripe_customer_id: Set(None),
        stripe_subscription_id: Set(None),
        current_period_end: Set(None),
        plan_cycle_start: Set(None),
        research_credits: Set(0),
        github_id: Set(None),
        github_login: Set(None),
    };
    model.insert(db).await
}

/// Find or create a user from a verified GitHub OAuth response.
///
/// Resolution order:
/// 1. Match by `github_id` → return existing row, refresh `github_login` and
///    `display_name` if changed.
/// 2. Match by lowercased email and `github_id IS NULL` → link: set
///    `github_id` and `github_login` on that row, return updated row.
/// 3. Else create a new row with `password_hash = NULL`.
///
/// Caller must already have verified that GitHub flagged this email as
/// `primary == true && verified == true`. We do **not** trust unverified
/// emails to identify pre-existing accounts.
pub async fn find_or_create_from_github(
    db: &DatabaseConnection,
    github_id: i64,
    github_login: &str,
    primary_verified_email: &str,
    display_name: Option<&str>,
) -> Result<users::Model, DbErr> {
    let email_norm = primary_verified_email.to_lowercase();

    // 1. Match by github_id.
    if let Some(existing) = users::Entity::find()
        .filter(users::Column::GithubId.eq(github_id))
        .one(db)
        .await?
    {
        let needs_login_update =
            existing.github_login.as_deref() != Some(github_login);
        let needs_name_update = display_name.is_some()
            && existing.display_name.as_deref() != display_name;
        if needs_login_update || needs_name_update {
            let mut active: users::ActiveModel = existing.clone().into();
            if needs_login_update {
                active.github_login = Set(Some(github_login.to_owned()));
            }
            if needs_name_update {
                active.display_name = Set(display_name.map(|s| s.to_owned()));
            }
            return active.update(db).await;
        }
        return Ok(existing);
    }

    // 2. Match by email.
    if let Some(existing) = users::Entity::find()
        .filter(users::Column::Email.eq(&email_norm))
        .one(db)
        .await?
    {
        // Only auto-link when the row has no GitHub identity yet — never
        // overwrite an existing link (would be a hijack vector).
        if existing.github_id.is_none() {
            let mut active: users::ActiveModel = existing.into();
            active.github_id = Set(Some(github_id));
            active.github_login = Set(Some(github_login.to_owned()));
            return active.update(db).await;
        }
        // Email collision but the row already has a different github_id —
        // treat as conflict so the caller surfaces a clear error.
        return Err(DbErr::Custom(format!(
            "email {} is linked to a different github account",
            email_norm
        )));
    }

    // 3. Create new.
    let model = users::ActiveModel {
        id: Set(Uuid::new_v4()),
        email: Set(email_norm),
        password_hash: Set(None),
        display_name: Set(display_name.map(|s| s.to_owned())),
        created_at: Set(chrono::Utc::now().into()),
        plan_tier: Set("free".to_owned()),
        stripe_customer_id: Set(None),
        stripe_subscription_id: Set(None),
        current_period_end: Set(None),
        plan_cycle_start: Set(None),
        research_credits: Set(0),
        github_id: Set(Some(github_id)),
        github_login: Set(Some(github_login.to_owned())),
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
