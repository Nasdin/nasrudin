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

    let unique_token = Uuid::new_v4();
    let email = format!("apikey-test-{unique_token}@example.test");
    let user = query::users::create_user(&db, &email, "stub-hash", None)
        .await
        .unwrap();

    // The DB cascades user deletion → api_keys, so cleaning up the user is enough
    // to also remove the key — even if assertions below panic. The randomised
    // prefix prevents UNIQUE collisions on retry.
    let result = run_roundtrip(&db, user.id, unique_token).await;

    // Always run cleanup, propagate any panic afterwards.
    let _ = query::users::delete_user(&db, user.id).await;
    result.unwrap();
}

async fn run_roundtrip(
    db: &sea_orm::DatabaseConnection,
    user_id: Uuid,
    unique_token: Uuid,
) -> Result<(), Box<dyn std::error::Error>> {
    let prefix = format!("nsk_live_{}", &unique_token.simple().to_string()[..4]);

    let issued = query::api_keys::create(
        db,
        Some(user_id),
        "live",
        "my first key",
        &prefix,
        "argon2-hash-of-secret",
        None,
    )
    .await?;
    assert_eq!(issued.kind, "live");
    assert_eq!(issued.user_id, Some(user_id));

    let found = query::api_keys::find_by_prefix(db, &prefix)
        .await?
        .ok_or("must find by prefix")?;
    assert_eq!(found.id, issued.id);

    query::api_keys::mark_used(db, issued.id).await?;
    let after_use = query::api_keys::find_by_prefix(db, &prefix)
        .await?
        .ok_or("missing after mark_used")?;
    assert!(after_use.last_used_at.is_some());

    let list = query::api_keys::list_by_user(db, user_id).await?;
    assert_eq!(list.len(), 1);

    query::api_keys::revoke(db, issued.id, user_id)
        .await?
        .ok_or("revoke must return the row")?;
    let list_after = query::api_keys::list_by_user(db, user_id).await?;
    assert_eq!(list_after.len(), 0);

    Ok(())
}
