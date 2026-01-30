use sea_orm::*;
use uuid::Uuid;

use crate::entity::saved_searches;

/// Save a LaTeX search for a user.
pub async fn create(
    db: &DatabaseConnection,
    user_id: Uuid,
    latex: &str,
    label: Option<&str>,
) -> Result<saved_searches::Model, DbErr> {
    let model = saved_searches::ActiveModel {
        id: Set(Uuid::new_v4()),
        user_id: Set(user_id),
        latex: Set(latex.to_owned()),
        label: Set(label.map(|s| s.to_owned())),
        created_at: Set(chrono::Utc::now().into()),
    };
    model.insert(db).await
}

/// List all saved searches for a user, newest first.
pub async fn list_by_user(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<Vec<saved_searches::Model>, DbErr> {
    saved_searches::Entity::find()
        .filter(saved_searches::Column::UserId.eq(user_id))
        .order_by_desc(saved_searches::Column::CreatedAt)
        .all(db)
        .await
}

/// Delete a saved search by ID (only if owned by user).
pub async fn delete(
    db: &DatabaseConnection,
    id: Uuid,
    user_id: Uuid,
) -> Result<DeleteResult, DbErr> {
    saved_searches::Entity::delete_many()
        .filter(saved_searches::Column::Id.eq(id))
        .filter(saved_searches::Column::UserId.eq(user_id))
        .exec(db)
        .await
}

/// Update the label on a saved search.
pub async fn update_label(
    db: &DatabaseConnection,
    id: Uuid,
    user_id: Uuid,
    label: Option<&str>,
) -> Result<Option<saved_searches::Model>, DbErr> {
    let existing = saved_searches::Entity::find_by_id(id)
        .filter(saved_searches::Column::UserId.eq(user_id))
        .one(db)
        .await?;

    match existing {
        Some(record) => {
            let mut active: saved_searches::ActiveModel = record.into();
            active.label = Set(label.map(|s| s.to_owned()));
            Ok(Some(active.update(db).await?))
        }
        None => Ok(None),
    }
}
