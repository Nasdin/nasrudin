//! refund_records CRUD smoke.

use nasrudin_pg::{PgConfig, connect_and_migrate, query};
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn refund_record_pending_then_succeeded() {
    let Some(db) = db().await else { return };
    let unique = Uuid::new_v4();
    let admin = query::users::create_firebase_user(
        &db,
        &format!("fb_ref_admin_{}", unique.simple()),
        &format!("ref-admin-{unique}@example.test"),
        None,
    )
    .await
    .unwrap();
    let user = query::users::create_firebase_user(
        &db,
        &format!("fb_ref_user_{}", unique.simple()),
        &format!("ref-user-{unique}@example.test"),
        None,
    )
    .await
    .unwrap();

    let id = query::refund_records::insert(
        &db,
        user.id,
        admin.id,
        &format!("ch_test_{}", unique.simple()),
        1900,
        "usd",
        "test refund",
    )
    .await
    .unwrap();

    let pending = query::refund_records::list_pending_older_than(&db, 0)
        .await
        .unwrap();
    assert!(pending.iter().any(|r| r.id == id));

    query::refund_records::mark_succeeded(&db, id, &format!("re_{}", unique.simple()))
        .await
        .unwrap();
    let row = query::refund_records::find_by_id(&db, id)
        .await
        .unwrap()
        .unwrap();
    assert_eq!(row.status, "succeeded");
    assert!(row.stripe_refund_id.is_some());
}
