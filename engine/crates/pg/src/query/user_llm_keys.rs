//! CRUD on `user_llm_keys`. The encryption layer (`nasrudin_llm::encryption`)
//! is applied at the handler boundary; this module sees only the
//! ciphertext + hint.

use sea_orm::*;
use sea_query::OnConflict;
use uuid::Uuid;

use crate::entity::user_llm_keys;

/// Public-safe summary returned to the UI. Carries the hint, never
/// the ciphertext.
#[derive(Debug, Clone)]
pub struct LlmKeySummary {
    pub provider: String,
    pub key_hint: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub last_used_at: Option<chrono::DateTime<chrono::Utc>>,
}

impl From<user_llm_keys::Model> for LlmKeySummary {
    fn from(m: user_llm_keys::Model) -> Self {
        Self {
            provider: m.provider,
            key_hint: m.key_hint,
            created_at: m.created_at.into(),
            last_used_at: m.last_used_at.map(|d| d.into()),
        }
    }
}

pub async fn list_for_user(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<Vec<LlmKeySummary>, DbErr> {
    let rows = user_llm_keys::Entity::find()
        .filter(user_llm_keys::Column::UserId.eq(user_id))
        .all(db)
        .await?;
    Ok(rows.into_iter().map(LlmKeySummary::from).collect())
}

/// Insert-or-update (the composite PK is `(user_id, provider)`).
pub async fn upsert(
    db: &DatabaseConnection,
    user_id: Uuid,
    provider: String,
    encrypted_key: Vec<u8>,
    key_hint: String,
) -> Result<(), DbErr> {
    let am = user_llm_keys::ActiveModel {
        user_id: Set(user_id),
        provider: Set(provider.clone()),
        encrypted_key: Set(encrypted_key),
        key_hint: Set(key_hint),
        created_at: Set(chrono::Utc::now().into()),
        last_used_at: NotSet,
    };
    user_llm_keys::Entity::insert(am)
        .on_conflict(
            OnConflict::columns([
                user_llm_keys::Column::UserId,
                user_llm_keys::Column::Provider,
            ])
            .update_columns([
                user_llm_keys::Column::EncryptedKey,
                user_llm_keys::Column::KeyHint,
                user_llm_keys::Column::CreatedAt,
            ])
            .to_owned(),
        )
        .exec(db)
        .await?;
    Ok(())
}

/// Returns the ciphertext for the (user_id, provider) row, or None.
/// The caller decrypts with the server's key. Internal API: never
/// expose ciphertext over the wire.
pub async fn get_ciphertext(
    db: &DatabaseConnection,
    user_id: Uuid,
    provider: &str,
) -> Result<Option<Vec<u8>>, DbErr> {
    let row = user_llm_keys::Entity::find_by_id((user_id, provider.to_string()))
        .one(db)
        .await?;
    Ok(row.map(|m| m.encrypted_key))
}

pub async fn delete(
    db: &DatabaseConnection,
    user_id: Uuid,
    provider: &str,
) -> Result<u64, DbErr> {
    let res = user_llm_keys::Entity::delete_by_id((user_id, provider.to_string()))
        .exec(db)
        .await?;
    Ok(res.rows_affected)
}

pub async fn touch_last_used(
    db: &DatabaseConnection,
    user_id: Uuid,
    provider: &str,
) -> Result<(), DbErr> {
    let am = user_llm_keys::ActiveModel {
        user_id: Set(user_id),
        provider: Set(provider.to_string()),
        last_used_at: Set(Some(chrono::Utc::now().into())),
        ..Default::default()
    };
    let _ = user_llm_keys::Entity::update(am).exec(db).await?;
    Ok(())
}
