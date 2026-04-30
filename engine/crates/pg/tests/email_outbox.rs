//! Outbox queue + claim_pending sanity.

use nasrudin_pg::{PgConfig, connect_and_migrate, query};
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn email_outbox_queue_then_claim() {
    let Some(db) = db().await else { return };
    let unique = Uuid::new_v4();
    let user = query::users::create_firebase_user(
        &db,
        &format!("fb_outbox_{}", unique.simple()),
        &format!("outbox-{unique}@example.test"),
        None,
    )
    .await
    .unwrap();

    let id = query::email_outbox::queue(
        &db,
        Some(user.id),
        &user.email,
        "admin_credit_grant",
        "Subject",
        "body text",
        Some("body html"),
        None,
        None,
    )
    .await
    .unwrap();

    let pending = query::email_outbox::claim_pending(&db, 50).await.unwrap();
    assert!(pending.iter().any(|m| m.id == id));

    query::email_outbox::mark_sent(&db, id, "msg_test_123")
        .await
        .unwrap();
    let row = query::email_outbox::find_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(row.status, "sent");
    assert_eq!(row.provider_message_id.as_deref(), Some("msg_test_123"));

    let by_msg = query::email_outbox::find_by_provider_message_id(&db, "msg_test_123")
        .await
        .unwrap();
    assert!(by_msg.is_some());
}
