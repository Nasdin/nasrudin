//! Verifies the prevent_last_admin_demotion trigger.
//!
//! The trigger reads global state (count of OTHER admin rows) when
//! deciding whether to allow `is_admin -> FALSE`. The test cleans up
//! by DELETing fresh admin rows; DELETE does not fire the trigger
//! (it's `BEFORE UPDATE` only), so cleanup is safe.

use nasrudin_pg::{PgConfig, connect_and_migrate, entity::users, query};
use sea_orm::{
    ActiveModelTrait, ActiveValue::Set, ConnectionTrait, DatabaseBackend, EntityTrait, Statement,
};
use tokio::sync::Mutex;
use uuid::Uuid;

/// Tests share global admin-count state. Serialize.
static SERIAL: Mutex<()> = Mutex::const_new(());

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

async fn delete_user(db: &sea_orm::DatabaseConnection, id: Uuid) {
    let _ = users::Entity::delete_by_id(id).exec(db).await;
}

async fn delete_all_admins(db: &sea_orm::DatabaseConnection) {
    db.execute_raw(Statement::from_string(
        DatabaseBackend::Postgres,
        "DELETE FROM users WHERE is_admin = TRUE".to_string(),
    ))
    .await
    .unwrap();
}

#[tokio::test]
async fn cannot_demote_last_admin() {
    let _g = SERIAL.lock().await;
    let Some(db) = db().await else { return };
    delete_all_admins(&db).await;

    let unique = Uuid::new_v4();
    let user = query::users::create_firebase_user(
        &db,
        &format!("fb_lone_{}", unique.simple()),
        &format!("lone-{unique}@example.test"),
        None,
    )
    .await
    .unwrap();
    let mut promote: users::ActiveModel = user.clone().into();
    promote.is_admin = Set(true);
    let admin = promote.update(&db).await.unwrap();

    let mut demote: users::ActiveModel = admin.clone().into();
    demote.is_admin = Set(false);
    let err = demote.update(&db).await.unwrap_err();
    assert!(
        err.to_string().contains("cannot demote last admin") || err.to_string().contains("P0001"),
        "expected last-admin trigger error, got: {err}"
    );

    // Cleanup: DELETE doesn't fire the trigger.
    delete_user(&db, admin.id).await;
}

#[tokio::test]
async fn can_demote_when_other_admins_exist() {
    let _g = SERIAL.lock().await;
    let Some(db) = db().await else { return };
    delete_all_admins(&db).await;

    let unique = Uuid::new_v4();
    let a = query::users::create_firebase_user(
        &db,
        &format!("fb_admin_a_{}", unique.simple()),
        &format!("a-admin-{unique}@example.test"),
        None,
    )
    .await
    .unwrap();
    let b = query::users::create_firebase_user(
        &db,
        &format!("fb_admin_b_{}", unique.simple()),
        &format!("b-admin-{unique}@example.test"),
        None,
    )
    .await
    .unwrap();
    let mut a_act: users::ActiveModel = a.clone().into();
    a_act.is_admin = Set(true);
    a_act.update(&db).await.unwrap();
    let mut b_act: users::ActiveModel = b.clone().into();
    b_act.is_admin = Set(true);
    b_act.update(&db).await.unwrap();

    let mut demote: users::ActiveModel = a.clone().into();
    demote.is_admin = Set(false);
    demote.update(&db).await.unwrap(); // should succeed because b is still admin

    delete_user(&db, a.id).await;
    delete_user(&db, b.id).await;
}
