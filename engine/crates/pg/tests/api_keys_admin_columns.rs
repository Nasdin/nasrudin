//! Verifies the `api_keys` table gains optional `trust_override` and
//! `spot_check_rate` columns. NULL on either column means "inherit from
//! owning user". Skipped when `DATABASE_URL` is unset.

use nasrudin_pg::{PgConfig, connect_and_migrate, entity::api_keys};
use sea_orm::{ActiveModelTrait, ActiveValue::Set, EntityTrait};
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn api_keys_round_trips_trust_override_and_rate() {
    let Some(db) = db().await else { return };

    let id = Uuid::new_v4();
    let unique = Uuid::new_v4();
    let prefix: String = format!("nsk_worker_{}", unique.simple())
        .chars()
        .take(14)
        .collect();
    let model = api_keys::ActiveModel {
        id: Set(id),
        user_id: Set(None),
        kind: Set("worker".into()),
        name: Set(format!("k-{unique}")),
        prefix: Set(prefix),
        key_hash: Set("$argon2id$_".into()),
        last_used_at: Set(None),
        expires_at: Set(None),
        created_at: Set(chrono::Utc::now().into()),
        revoked_at: Set(None),
        trust_override: Set(Some(true)),
        spot_check_rate: Set(Some(10)),
    };
    let row = api_keys::Entity::insert(model)
        .exec_with_returning(&db)
        .await
        .unwrap();
    assert_eq!(row.trust_override, Some(true));
    assert_eq!(row.spot_check_rate, Some(10));

    // NULL coexists fine.
    let id2 = Uuid::new_v4();
    let prefix2: String = format!("nsk_live_{}", Uuid::new_v4().simple())
        .chars()
        .take(12)
        .collect();
    let model2 = api_keys::ActiveModel {
        id: Set(id2),
        user_id: Set(None),
        kind: Set("live".into()),
        name: Set("k-null".into()),
        prefix: Set(prefix2),
        key_hash: Set("$argon2id$_".into()),
        last_used_at: Set(None),
        expires_at: Set(None),
        created_at: Set(chrono::Utc::now().into()),
        revoked_at: Set(None),
        trust_override: Set(None),
        spot_check_rate: Set(None),
    };
    let row2 = api_keys::Entity::insert(model2)
        .exec_with_returning(&db)
        .await
        .unwrap();
    assert_eq!(row2.trust_override, None);
    assert_eq!(row2.spot_check_rate, None);
}
