//! Round-trips an audit log row inside a transaction. Skipped when
//! `DATABASE_URL` is unset.

use nasrudin_pg::{PgConfig, connect_and_migrate, query};
use sea_orm::TransactionTrait;
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn audit_log_insert_and_list_round_trip() {
    let Some(db) = db().await else { return };

    let unique = Uuid::new_v4();
    let actor_uid = format!("fb_actor_{}", unique.simple());
    let target_uid = format!("fb_target_{}", unique.simple());
    let actor_email = format!("auditor-{unique}@example.test");
    let target_email = format!("audited-{unique}@example.test");
    let actor = query::users::create_firebase_user(&db, &actor_uid, &actor_email, None)
        .await
        .unwrap();
    let target = query::users::create_firebase_user(&db, &target_uid, &target_email, None)
        .await
        .unwrap();

    let txn = db.begin().await.unwrap();
    let id = query::admin_audit_log::insert(
        &txn,
        actor.id,
        Some(target.id),
        None,
        "SET_IS_TRUSTED",
        Some(serde_json::json!({"is_trusted": false})),
        Some(serde_json::json!({"is_trusted": true})),
        "promoting test user to trusted contributor".to_string(),
        Some("127.0.0.1".parse().unwrap()),
        Some("test-agent/1.0".to_string()),
    )
    .await
    .unwrap();
    txn.commit().await.unwrap();

    let rows = query::admin_audit_log::list_by_target(&db, target.id, 10)
        .await
        .unwrap();
    assert!(rows.iter().any(|r| r.id == id));
    let row = rows.into_iter().find(|r| r.id == id).unwrap();
    assert_eq!(row.action, "SET_IS_TRUSTED");
    assert_eq!(
        row.before_value.as_ref().and_then(|v| v.get("is_trusted")),
        Some(&serde_json::json!(false))
    );
    assert_eq!(row.user_agent.as_deref(), Some("test-agent/1.0"));
    assert_eq!(row.request_ip.as_deref(), Some("127.0.0.1"));
}
