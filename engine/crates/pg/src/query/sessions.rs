use sea_orm::*;
use uuid::Uuid;

use crate::entity::sessions;

/// Create a new session for a user.
pub async fn create_session(
    db: &DatabaseConnection,
    user_id: Uuid,
    token: &str,
    expires_at: chrono::DateTime<chrono::Utc>,
) -> Result<sessions::Model, DbErr> {
    let model = sessions::ActiveModel {
        id: Set(Uuid::new_v4()),
        user_id: Set(user_id),
        token: Set(token.to_owned()),
        expires_at: Set(expires_at.into()),
        created_at: Set(chrono::Utc::now().into()),
    };
    model.insert(db).await
}

/// Find a session by its token. Returns None if expired or not found.
pub async fn find_valid_session(
    db: &DatabaseConnection,
    token: &str,
) -> Result<Option<sessions::Model>, DbErr> {
    sessions::Entity::find()
        .filter(sessions::Column::Token.eq(token))
        .filter(sessions::Column::ExpiresAt.gt(chrono::Utc::now()))
        .one(db)
        .await
}

/// Find all active sessions for a user.
pub async fn find_user_sessions(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<Vec<sessions::Model>, DbErr> {
    sessions::Entity::find()
        .filter(sessions::Column::UserId.eq(user_id))
        .filter(sessions::Column::ExpiresAt.gt(chrono::Utc::now()))
        .all(db)
        .await
}

/// Delete a session (logout).
pub async fn delete_session(db: &DatabaseConnection, token: &str) -> Result<DeleteResult, DbErr> {
    sessions::Entity::delete_many()
        .filter(sessions::Column::Token.eq(token))
        .exec(db)
        .await
}

/// Delete all sessions for a user (logout everywhere).
pub async fn delete_user_sessions(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<DeleteResult, DbErr> {
    sessions::Entity::delete_many()
        .filter(sessions::Column::UserId.eq(user_id))
        .exec(db)
        .await
}

/// Purge expired sessions.
pub async fn purge_expired(db: &DatabaseConnection) -> Result<DeleteResult, DbErr> {
    sessions::Entity::delete_many()
        .filter(sessions::Column::ExpiresAt.lt(chrono::Utc::now()))
        .exec(db)
        .await
}
