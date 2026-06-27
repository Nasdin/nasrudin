//! Per-user views over the worker pool.
//!
//! Workers have no direct `user_id` column. The link goes:
//! `workers.id == api_keys.name` (where `api_keys.kind == 'worker'`),
//! and `api_keys.user_id` points at `users.id`.

use anyhow::Result;
use sea_orm::{ColumnTrait, ConnectionTrait, EntityTrait, QueryFilter};
use std::collections::HashMap;
use uuid::Uuid;

use crate::entity::{api_keys, users, workers};

/// All workers owned by a given user, joined via `api_keys`.
///
/// "Owned" means there is at least one non-revoked `api_keys` row of
/// `kind = 'worker'`, `user_id = user_id`, and `name = workers.id`.
pub async fn list_for_user(
    db: &impl ConnectionTrait,
    user_id: Uuid,
) -> Result<Vec<workers::Model>> {
    let keys = api_keys::Entity::find()
        .filter(api_keys::Column::UserId.eq(user_id))
        .filter(api_keys::Column::Kind.eq("worker"))
        .filter(api_keys::Column::RevokedAt.is_null())
        .all(db)
        .await?;
    let names: Vec<String> = keys.into_iter().map(|k| k.name).collect();
    if names.is_empty() {
        return Ok(vec![]);
    }
    Ok(workers::Entity::find()
        .filter(workers::Column::Id.is_in(names))
        .all(db)
        .await?)
}

/// Lookup table from `workers.id` → `users.display_name` (or email fallback)
/// for every worker that has a non-revoked worker-kind api_key linking back
/// to a registered user. Workers registered anonymously via
/// `POST /api/workers/register` (with `user_id = NULL`) are absent.
///
/// Used to enrich the public `GET /api/workers` response with owner info
/// without exposing private fields.
pub async fn owner_map(db: &impl ConnectionTrait) -> Result<HashMap<String, OwnerInfo>> {
    let keys = api_keys::Entity::find()
        .filter(api_keys::Column::Kind.eq("worker"))
        .filter(api_keys::Column::RevokedAt.is_null())
        .filter(api_keys::Column::UserId.is_not_null())
        .all(db)
        .await?;

    let user_ids: Vec<Uuid> = keys.iter().filter_map(|k| k.user_id).collect();
    if user_ids.is_empty() {
        return Ok(HashMap::new());
    }
    let users = users::Entity::find()
        .filter(users::Column::Id.is_in(user_ids))
        .all(db)
        .await?;
    let user_map: HashMap<Uuid, users::Model> = users.into_iter().map(|u| (u.id, u)).collect();

    let mut out = HashMap::new();
    for k in keys {
        let Some(uid) = k.user_id else { continue };
        let Some(u) = user_map.get(&uid) else {
            continue;
        };
        // Last write wins if a worker name appears under multiple keys.
        out.insert(
            k.name,
            OwnerInfo {
                user_id: u.id,
                display_name: u.display_name.clone(),
                // Email is private — we expose a redacted handle (local part).
                email_local: u.email.split('@').next().unwrap_or("").to_owned(),
                country_code: u.country_code.clone(),
            },
        );
    }
    Ok(out)
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct OwnerInfo {
    pub user_id: Uuid,
    pub display_name: Option<String>,
    pub email_local: String,
    /// ISO-3166-1 alpha-2 country code (uppercase) when the user has set one.
    /// Surfaced on the public Workers page as a flag / country pill.
    pub country_code: Option<String>,
}
