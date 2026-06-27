//! Lifecycle smoke for the impersonation_sessions table.

use chrono::Utc;
use nasrudin_pg::{PgConfig, connect_and_migrate, query};
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn impersonation_session_lifecycle() {
    let Some(db) = db().await else { return };
    let unique = Uuid::new_v4();
    let admin = query::users::create_firebase_user(
        &db,
        &format!("fb_imp_admin_{}", unique.simple()),
        &format!("imp-admin-{unique}@example.test"),
        None,
    )
    .await
    .unwrap();
    let target = query::users::create_firebase_user(
        &db,
        &format!("fb_imp_target_{}", unique.simple()),
        &format!("imp-target-{unique}@example.test"),
        None,
    )
    .await
    .unwrap();

    let row = query::impersonation::start(
        &db,
        admin.id,
        target.id,
        Utc::now() + chrono::Duration::seconds(900),
        "debugging session for support ticket".into(),
    )
    .await
    .unwrap();
    assert!(
        query::impersonation::find_active(&db, row.id)
            .await
            .unwrap()
            .is_some()
    );

    query::impersonation::end(&db, row.id, "manual_end")
        .await
        .unwrap();
    assert!(
        query::impersonation::find_active(&db, row.id)
            .await
            .unwrap()
            .is_none()
    );

    let expired_row = query::impersonation::start(
        &db,
        admin.id,
        target.id,
        Utc::now() - chrono::Duration::seconds(1),
        "already expired test session".into(),
    )
    .await
    .unwrap();
    let expired = query::impersonation::list_expired(&db).await.unwrap();
    assert!(expired.iter().any(|r| r.id == expired_row.id));
}
