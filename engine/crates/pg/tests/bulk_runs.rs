//! bulk_runs lifecycle + JSONB-append failures.

use nasrudin_pg::{PgConfig, connect_and_migrate, query};
use serde_json::json;
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn bulk_run_lifecycle() {
    let Some(db) = db().await else { return };
    let unique = Uuid::new_v4();
    let admin = query::users::create_firebase_user(
        &db,
        &format!("fb_bulk_{}", unique.simple()),
        &format!("bulk-{unique}@example.test"),
        None,
    )
    .await
    .unwrap();

    let id = query::bulk_runs::insert(&db, admin.id, "set_trust", json!({"to": true}), 5)
        .await
        .unwrap();
    query::bulk_runs::increment_completed(&db, id).await.unwrap();
    query::bulk_runs::increment_failed(&db, id, json!([{"user":"x","err":"e"}]))
        .await
        .unwrap();
    query::bulk_runs::complete(&db, id, "completed").await.unwrap();

    let r = query::bulk_runs::find_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(r.completed_count, 1);
    assert_eq!(r.failed_count, 1);
    assert_eq!(r.status, "completed");
}
