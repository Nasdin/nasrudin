//! Personal library — saved theorems + folders.
//!
//! All queries are user-scoped: every read/write filters by user_id so
//! rows are invisible to other accounts. The handler layer enforces
//! `PlanTier::quotas().library_max` before calling `save_theorem`.

use sea_orm::prelude::DateTimeWithTimeZone;
use sea_orm::*;
use uuid::Uuid;

use crate::entity::{library_folders, theorems, user_saved_theorems};

// ── folders ────────────────────────────────────────────────────────────

pub async fn list_folders(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<Vec<library_folders::Model>, DbErr> {
    library_folders::Entity::find()
        .filter(library_folders::Column::UserId.eq(user_id))
        .order_by_asc(library_folders::Column::Name)
        .all(db)
        .await
}

pub async fn create_folder(
    db: &DatabaseConnection,
    user_id: Uuid,
    name: &str,
    color: Option<&str>,
) -> Result<library_folders::Model, DbErr> {
    let now = chrono::Utc::now();
    library_folders::ActiveModel {
        id: Set(Uuid::new_v4()),
        user_id: Set(user_id),
        name: Set(name.to_owned()),
        color: Set(color.map(|s| s.to_owned())),
        created_at: Set(now.into()),
        updated_at: Set(now.into()),
    }
    .insert(db)
    .await
}

pub async fn patch_folder(
    db: &DatabaseConnection,
    user_id: Uuid,
    folder_id: Uuid,
    name: Option<&str>,
    color: Option<Option<&str>>,
) -> Result<Option<library_folders::Model>, DbErr> {
    let existing = library_folders::Entity::find_by_id(folder_id)
        .filter(library_folders::Column::UserId.eq(user_id))
        .one(db)
        .await?;
    match existing {
        Some(row) => {
            let mut active: library_folders::ActiveModel = row.into();
            if let Some(n) = name {
                active.name = Set(n.to_owned());
            }
            if let Some(c) = color {
                active.color = Set(c.map(|s| s.to_owned()));
            }
            active.updated_at = Set(chrono::Utc::now().into());
            Ok(Some(active.update(db).await?))
        }
        None => Ok(None),
    }
}

pub async fn delete_folder(
    db: &DatabaseConnection,
    user_id: Uuid,
    folder_id: Uuid,
) -> Result<DeleteResult, DbErr> {
    library_folders::Entity::delete_many()
        .filter(library_folders::Column::Id.eq(folder_id))
        .filter(library_folders::Column::UserId.eq(user_id))
        .exec(db)
        .await
}

// ── saved theorems ────────────────────────────────────────────────────

pub async fn count_saved(db: &DatabaseConnection, user_id: Uuid) -> Result<u64, DbErr> {
    user_saved_theorems::Entity::find()
        .filter(user_saved_theorems::Column::UserId.eq(user_id))
        .count(db)
        .await
}

pub async fn is_saved(
    db: &DatabaseConnection,
    user_id: Uuid,
    theorem_id: &[u8],
) -> Result<bool, DbErr> {
    let exists = user_saved_theorems::Entity::find()
        .filter(user_saved_theorems::Column::UserId.eq(user_id))
        .filter(user_saved_theorems::Column::TheoremId.eq(theorem_id.to_vec()))
        .one(db)
        .await?;
    Ok(exists.is_some())
}

pub async fn save_theorem(
    db: &DatabaseConnection,
    user_id: Uuid,
    theorem_id: &[u8],
    folder_id: Option<Uuid>,
    note: Option<&str>,
    label: Option<&str>,
) -> Result<user_saved_theorems::Model, DbErr> {
    user_saved_theorems::ActiveModel {
        user_id: Set(user_id),
        theorem_id: Set(theorem_id.to_vec()),
        saved_at: Set(chrono::Utc::now().into()),
        folder_id: Set(folder_id),
        note: Set(note.map(|s| s.to_owned())),
        label: Set(label.map(|s| s.to_owned())),
    }
    .insert(db)
    .await
}

pub async fn unsave_theorem(
    db: &DatabaseConnection,
    user_id: Uuid,
    theorem_id: &[u8],
) -> Result<DeleteResult, DbErr> {
    user_saved_theorems::Entity::delete_many()
        .filter(user_saved_theorems::Column::UserId.eq(user_id))
        .filter(user_saved_theorems::Column::TheoremId.eq(theorem_id.to_vec()))
        .exec(db)
        .await
}

pub async fn patch_saved(
    db: &DatabaseConnection,
    user_id: Uuid,
    theorem_id: &[u8],
    folder_id: Option<Option<Uuid>>,
    note: Option<Option<String>>,
    label: Option<Option<String>>,
) -> Result<Option<user_saved_theorems::Model>, DbErr> {
    let existing = user_saved_theorems::Entity::find()
        .filter(user_saved_theorems::Column::UserId.eq(user_id))
        .filter(user_saved_theorems::Column::TheoremId.eq(theorem_id.to_vec()))
        .one(db)
        .await?;
    match existing {
        Some(row) => {
            let mut active: user_saved_theorems::ActiveModel = row.into();
            if let Some(f) = folder_id {
                active.folder_id = Set(f);
            }
            if let Some(n) = note {
                active.note = Set(n);
            }
            if let Some(l) = label {
                active.label = Set(l);
            }
            Ok(Some(active.update(db).await?))
        }
        None => Ok(None),
    }
}

/// Saved theorem joined with the underlying theorem row. Newest-saved first;
/// optionally filtered by folder_id (use `Some(None)` for "ungrouped only",
/// `Some(Some(id))` for a specific folder, `None` for all).
#[derive(Debug, serde::Serialize)]
pub struct SavedTheoremRow {
    pub theorem: theorems::Model,
    pub saved_at: DateTimeWithTimeZone,
    pub folder_id: Option<Uuid>,
    pub note: Option<String>,
    pub label: Option<String>,
}

pub async fn list_saved(
    db: &DatabaseConnection,
    user_id: Uuid,
    folder_filter: FolderFilter,
    limit: u64,
    offset: u64,
) -> Result<Vec<SavedTheoremRow>, DbErr> {
    let mut q = user_saved_theorems::Entity::find()
        .filter(user_saved_theorems::Column::UserId.eq(user_id));
    match folder_filter {
        FolderFilter::All => {}
        FolderFilter::Ungrouped => {
            q = q.filter(user_saved_theorems::Column::FolderId.is_null());
        }
        FolderFilter::Specific(id) => {
            q = q.filter(user_saved_theorems::Column::FolderId.eq(id));
        }
    }
    let saved_rows = q
        .order_by_desc(user_saved_theorems::Column::SavedAt)
        .limit(limit)
        .offset(offset)
        .all(db)
        .await?;

    let ids: Vec<Vec<u8>> = saved_rows.iter().map(|s| s.theorem_id.clone()).collect();
    if ids.is_empty() {
        return Ok(Vec::new());
    }
    let theorems_rows = theorems::Entity::find()
        .filter(theorems::Column::Id.is_in(ids))
        .all(db)
        .await?;

    use std::collections::HashMap;
    let by_id: HashMap<Vec<u8>, theorems::Model> = theorems_rows
        .into_iter()
        .map(|t| (t.id.clone(), t))
        .collect();

    Ok(saved_rows
        .into_iter()
        .filter_map(|s| {
            by_id.get(&s.theorem_id).cloned().map(|t| SavedTheoremRow {
                theorem: t,
                saved_at: s.saved_at,
                folder_id: s.folder_id,
                note: s.note,
                label: s.label,
            })
        })
        .collect())
}

#[derive(Debug, Clone, Copy)]
pub enum FolderFilter {
    All,
    Ungrouped,
    Specific(Uuid),
}
