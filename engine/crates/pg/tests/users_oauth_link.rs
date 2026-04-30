//! Integration tests for `find_or_create_from_github`.
//! Skipped when DATABASE_URL is unset.

use nasrudin_pg::{PgConfig, connect_and_migrate, query};
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

/// Compress a UUID into a positive i64. Used purely so each test gets its
/// own deterministic but unique github_id without colliding with other
/// concurrent or sequential test runs.
fn token_to_gh_id(token: Uuid, salt: i64) -> i64 {
    // Take the low 63 bits of the UUID's 128 bits — strip the sign bit so
    // it always fits in a positive i64. Add salt to differentiate per-test.
    let lo = (token.as_u128() & 0x7fff_ffff_ffff_ffff) as i64;
    lo.wrapping_add(salt)
}

#[tokio::test]
async fn branch_1_match_by_github_id_updates_login_and_name() {
    let Some(db) = db().await else { return };
    let token = Uuid::new_v4();
    let email = format!("gh-link-1-{token}@example.test");
    let github_id = token_to_gh_id(token, 1);

    // Seed.
    let created = query::users::find_or_create_from_github(
        &db, github_id, "octocat", &email, Some("Old Name"),
    )
    .await
    .unwrap();
    assert_eq!(created.github_id, Some(github_id));
    assert_eq!(created.github_login.as_deref(), Some("octocat"));
    assert_eq!(created.display_name.as_deref(), Some("Old Name"));
    assert_eq!(created.password_hash, None);

    // Re-call with renamed login + name.
    let updated = query::users::find_or_create_from_github(
        &db, github_id, "octocat-renamed", &email, Some("New Name"),
    )
    .await
    .unwrap();
    assert_eq!(updated.id, created.id);
    assert_eq!(updated.github_login.as_deref(), Some("octocat-renamed"));
    assert_eq!(updated.display_name.as_deref(), Some("New Name"));

    let _ = query::users::delete_user(&db, created.id).await;
}

#[tokio::test]
async fn branch_2_match_by_email_links_existing_account() {
    let Some(db) = db().await else { return };
    let token = Uuid::new_v4();
    let email = format!("gh-link-2-{token}@example.test");
    let github_id = token_to_gh_id(token, 2);

    // Pre-seed: an email/password user with no GitHub link.
    let pw_user =
        query::users::create_user(&db, &email, Some("argon2-stub-hash"), Some("Anya"))
            .await
            .unwrap();
    assert_eq!(pw_user.github_id, None);

    // Sign in with GitHub using the same primary verified email.
    let linked = query::users::find_or_create_from_github(
        &db, github_id, "anya", &email, Some("Anya K"),
    )
    .await
    .unwrap();

    assert_eq!(linked.id, pw_user.id, "must reuse existing row");
    assert_eq!(linked.github_id, Some(github_id));
    assert_eq!(linked.github_login.as_deref(), Some("anya"));
    assert!(linked.password_hash.is_some(), "password_hash must be preserved");

    let _ = query::users::delete_user(&db, pw_user.id).await;
}

#[tokio::test]
async fn branch_3_creates_new_oauth_only_user() {
    let Some(db) = db().await else { return };
    let token = Uuid::new_v4();
    let email = format!("gh-link-3-{token}@example.test");
    let github_id = token_to_gh_id(token, 3);

    let created = query::users::find_or_create_from_github(
        &db, github_id, "newcomer", &email, Some("Newcomer"),
    )
    .await
    .unwrap();
    assert_eq!(created.github_id, Some(github_id));
    assert_eq!(created.password_hash, None);
    assert_eq!(created.plan_tier, "free");

    let _ = query::users::delete_user(&db, created.id).await;
}

#[tokio::test]
async fn email_collision_with_different_github_id_errors() {
    let Some(db) = db().await else { return };
    let token = Uuid::new_v4();
    let email = format!("gh-link-4-{token}@example.test");
    let gh1 = token_to_gh_id(token, 4);
    let gh2 = token_to_gh_id(token, 5);

    // Existing user already linked to gh1.
    let first = query::users::find_or_create_from_github(
        &db, gh1, "first", &email, None,
    )
    .await
    .unwrap();

    // A different github_id with the same primary email should error.
    let result = query::users::find_or_create_from_github(
        &db, gh2, "second", &email, None,
    )
    .await;
    assert!(result.is_err(), "must refuse to silently re-link");

    let _ = query::users::delete_user(&db, first.id).await;
}
