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
