//! Verifies the `users` table gains `is_admin`, `is_trusted`, and an
//! optional `spot_check_rate` column with sane defaults. Skipped when
//! `DATABASE_URL` is unset — matching the convention in `api_keys.rs`.

use nasrudin_pg::{PgConfig, connect_and_migrate, entity::users, query};
use sea_orm::EntityTrait;
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn user_has_admin_trust_columns_with_defaults() {
    let Some(db) = db().await else { return };
    let unique = Uuid::new_v4();
    let email = format!("trustcols-{unique}@example.test");
    let firebase_uid = format!("fb_{}", unique.simple());
    let u = query::users::create_firebase_user(&db, &firebase_uid, &email, None)
        .await
        .unwrap();
    let m = users::Entity::find_by_id(u.id).one(&db).await.unwrap().unwrap();
    assert!(!m.is_admin);
    assert!(!m.is_trusted);
    assert_eq!(m.spot_check_rate, None);
}
