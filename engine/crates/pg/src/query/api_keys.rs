use sea_orm::*;
use uuid::Uuid;

use crate::entity::api_keys;

/// Insert an api-key row. The caller is responsible for hashing the secret.
#[allow(clippy::too_many_arguments)]
pub async fn create(
    db: &DatabaseConnection,
    user_id: Option<Uuid>,
    kind: &str,
    name: &str,
    prefix: &str,
    key_hash: &str,
    expires_at: Option<chrono::DateTime<chrono::Utc>>,
) -> Result<api_keys::Model, DbErr> {
    let model = api_keys::ActiveModel {
        id: Set(Uuid::new_v4()),
        user_id: Set(user_id),
        kind: Set(kind.to_owned()),
        name: Set(name.to_owned()),
        prefix: Set(prefix.to_owned()),
        key_hash: Set(key_hash.to_owned()),
        last_used_at: Set(None),
        expires_at: Set(expires_at.map(|d| d.into())),
        created_at: Set(chrono::Utc::now().into()),
        revoked_at: Set(None),
        trust_override: Set(None),
        spot_check_rate: Set(None),
    };
    model.insert(db).await
}

/// Find an active (non-revoked) key by its 12-char prefix.
pub async fn find_by_prefix(
    db: &DatabaseConnection,
    prefix: &str,
) -> Result<Option<api_keys::Model>, DbErr> {
    api_keys::Entity::find()
        .filter(api_keys::Column::Prefix.eq(prefix))
        .filter(api_keys::Column::RevokedAt.is_null())
        .one(db)
        .await
}

/// List all non-revoked, non-expired keys for a user.
pub async fn list_by_user(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<Vec<api_keys::Model>, DbErr> {
    let now = chrono::Utc::now();
    api_keys::Entity::find()
        .filter(api_keys::Column::UserId.eq(user_id))
        .filter(api_keys::Column::RevokedAt.is_null())
        .filter(
            api_keys::Column::ExpiresAt
                .is_null()
                .or(api_keys::Column::ExpiresAt.gt(now)),
        )
        .order_by_desc(api_keys::Column::CreatedAt)
        .all(db)
        .await
}

/// Update `last_used_at = now()` on an api-key. Best-effort.
pub async fn mark_used(db: &DatabaseConnection, id: Uuid) -> Result<(), DbErr> {
    let active = api_keys::ActiveModel {
        id: Set(id),
        last_used_at: Set(Some(chrono::Utc::now().into())),
        ..Default::default()
    };
    active.update(db).await?;
    Ok(())
}

/// Revoke an api-key owned by `user_id`. Returns the row if owned, None otherwise.
pub async fn revoke(
    db: &DatabaseConnection,
    id: Uuid,
    user_id: Uuid,
) -> Result<Option<api_keys::Model>, DbErr> {
    let existing = api_keys::Entity::find_by_id(id)
        .filter(api_keys::Column::UserId.eq(user_id))
        .one(db)
        .await?;
    match existing {
        Some(row) => {
            let mut active: api_keys::ActiveModel = row.into();
            active.revoked_at = Set(Some(chrono::Utc::now().into()));
            Ok(Some(active.update(db).await?))
        }
        None => Ok(None),
    }
}
