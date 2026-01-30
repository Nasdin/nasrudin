use sea_orm::*;
use uuid::Uuid;

use crate::entity::user_preferences;

/// Get preferences for a user. Returns default empty JSON object if none set.
pub async fn get(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<serde_json::Value, DbErr> {
    let row = user_preferences::Entity::find_by_id(user_id).one(db).await?;
    Ok(row.map(|r| r.preferences).unwrap_or(serde_json::json!({})))
}

/// Upsert (create or replace) preferences for a user.
pub async fn set(
    db: &DatabaseConnection,
    user_id: Uuid,
    preferences: serde_json::Value,
) -> Result<user_preferences::Model, DbErr> {
    let existing = user_preferences::Entity::find_by_id(user_id)
        .one(db)
        .await?;

    match existing {
        Some(_) => {
            let model = user_preferences::ActiveModel {
                user_id: Set(user_id),
                preferences: Set(preferences),
            };
            model.update(db).await
        }
        None => {
            let model = user_preferences::ActiveModel {
                user_id: Set(user_id),
                preferences: Set(preferences),
            };
            model.insert(db).await
        }
    }
}

/// Merge a partial JSON object into existing preferences.
///
/// Performs a shallow merge: top-level keys in `patch` overwrite those in
/// the existing preferences. Keys not present in `patch` are preserved.
pub async fn merge(
    db: &DatabaseConnection,
    user_id: Uuid,
    patch: serde_json::Value,
) -> Result<user_preferences::Model, DbErr> {
    let current = get(db, user_id).await?;
    let mut merged = current;
    if let (Some(base), Some(update)) = (merged.as_object_mut(), patch.as_object()) {
        for (k, v) in update {
            base.insert(k.clone(), v.clone());
        }
    }
    set(db, user_id, merged).await
}

/// Delete preferences for a user (resets to default).
pub async fn delete(db: &DatabaseConnection, user_id: Uuid) -> Result<DeleteResult, DbErr> {
    user_preferences::Entity::delete_by_id(user_id)
        .exec(db)
        .await
}
