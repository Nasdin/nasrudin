//! Integration tests for the api_keys query layer.
//! Skipped if DATABASE_URL is not set.

use nasrudin_pg::{connect_and_migrate, query, PgConfig};
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn create_list_revoke_roundtrip() {
    let Some(db) = db().await else { return };

    let email = format!("apikey-test-{}@example.test", Uuid::new_v4());
    let user = query::users::create_user(&db, &email, "stub-hash", None)
        .await
        .unwrap();

    let issued = query::api_keys::create(
        &db,
        Some(user.id),
        "live",
        "my first key",
        "nsk_live_abc1",
        "argon2-hash-of-secret",
        None,
    )
    .await
    .unwrap();
    assert_eq!(issued.kind, "live");
    assert_eq!(issued.user_id, Some(user.id));

    let found = query::api_keys::find_by_prefix(&db, "nsk_live_abc1")
        .await
        .unwrap()
        .expect("must find by prefix");
    assert_eq!(found.id, issued.id);

    query::api_keys::mark_used(&db, issued.id).await.unwrap();
    let after_use = query::api_keys::find_by_prefix(&db, "nsk_live_abc1")
        .await
        .unwrap()
        .unwrap();
    assert!(after_use.last_used_at.is_some());

    let list = query::api_keys::list_by_user(&db, user.id).await.unwrap();
    assert_eq!(list.len(), 1);

    query::api_keys::revoke(&db, issued.id, user.id)
        .await
        .unwrap()
        .expect("revoke must return the row");
    let list_after = query::api_keys::list_by_user(&db, user.id).await.unwrap();
    assert_eq!(list_after.len(), 0);

    query::users::delete_user(&db, user.id).await.unwrap();
}
