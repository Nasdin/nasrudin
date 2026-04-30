//! Integration tests for the workers query layer (Phase 9 / Task 1.5).
//!
//! These tests run against a live PostgreSQL test database. They are skipped
//! gracefully if `TEST_DATABASE_URL` is not set and the default connection
//! cannot be established.
//!
//! The default URL points at the dev compose stack:
//! `postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test`.

use nasrudin_pg::{connect_simple, query::workers, run_migrations};
use sea_orm::{ConnectionTrait, DatabaseConnection};
use tokio::sync::{Mutex, MutexGuard};

// Tests in this file share one PostgreSQL test database and each `fresh_db()`
// DROPs and re-creates the schema. Cargo runs `#[tokio::test]` cases
// concurrently by default, so we serialise with a process-wide async mutex
// held for the entire test body to make the suite safe under default
// `cargo test`.
static TEST_LOCK: Mutex<()> = Mutex::const_new(());

async fn fresh_db() -> Option<(DatabaseConnection, MutexGuard<'static, ()>)> {
    let guard = TEST_LOCK.lock().await;
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    });
    let db = connect_simple(&url).await.ok()?;
    db.execute_unprepared(
        "DROP TABLE IF EXISTS user_saved_theorems CASCADE; \
         DROP TABLE IF EXISTS library_folders CASCADE; \
         DROP TABLE IF EXISTS cluster_steering CASCADE; \
         DROP TABLE IF EXISTS conjecture_events CASCADE; \
         DROP TABLE IF EXISTS conjecture_jobs CASCADE; \
         DROP TABLE IF EXISTS manual_verifications CASCADE; \
         DROP TABLE IF EXISTS targeted_search_usage CASCADE; \
         DROP TABLE IF EXISTS api_usage_daily CASCADE; \
         DROP TABLE IF EXISTS billing_events CASCADE; \
         DROP TABLE IF EXISTS user_llm_keys CASCADE; \
         DROP TABLE IF EXISTS theorems CASCADE; \
         DROP TABLE IF EXISTS api_keys CASCADE; \
         DROP TABLE IF EXISTS workers CASCADE; \
         DROP TABLE IF EXISTS sessions CASCADE; \
         DROP TABLE IF EXISTS user_preferences CASCADE; \
         DROP TABLE IF EXISTS saved_searches CASCADE; \
         DROP TABLE IF EXISTS users CASCADE; \
         DROP TABLE IF EXISTS seaql_migrations CASCADE;",
    )
    .await
    .unwrap();
    run_migrations(&db).await.unwrap();
    Some((db, guard))
}

#[tokio::test]
async fn heartbeat_updates_fields_atomically() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    workers::register(&db, "w1", Some("worker-one"), Some("host1"))
        .await
        .unwrap();
    workers::update_heartbeat(&db, "w1", 17, 1234, 99, "deadbee")
        .await
        .unwrap();
    let w = workers::get(&db, "w1").await.unwrap().unwrap();
    assert_eq!(w.current_generation, 17);
    assert_eq!(w.theorems_produced_total, 1234);
    assert_eq!(w.uptime_seconds, 99);
    assert_eq!(w.engine_git_sha.as_deref(), Some("deadbee"));
    assert!(w.last_heartbeat_at.is_some());
}

#[tokio::test]
async fn increment_contribution_is_atomic() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    workers::register(&db, "w2", None, None).await.unwrap();
    workers::increment_contribution(&db, "w2").await.unwrap();
    workers::increment_contribution(&db, "w2").await.unwrap();
    let w = workers::get(&db, "w2").await.unwrap().unwrap();
    assert_eq!(w.theorems_contributed, 2);
    assert!(w.last_contribution_at.is_some());
}

#[tokio::test]
async fn list_all_returns_ordered_by_contribution() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    workers::register(&db, "low", None, None).await.unwrap();
    workers::register(&db, "high", None, None).await.unwrap();
    for _ in 0..5 {
        workers::increment_contribution(&db, "high").await.unwrap();
    }
    workers::increment_contribution(&db, "low").await.unwrap();
    let list = workers::list_all(&db).await.unwrap();
    assert_eq!(list.first().unwrap().id, "high");
    assert_eq!(list.last().unwrap().id, "low");
}

#[tokio::test]
async fn count_active_workers_within_threshold() {
    let Some((db, _g)) = fresh_db().await else { return };

    // Two registered workers, both with last_seen = now (set by register()).
    workers::register(&db, "active-a", None, None).await.unwrap();
    workers::register(&db, "active-b", None, None).await.unwrap();

    let n = workers::count_active_workers(&db, chrono::Duration::minutes(5))
        .await
        .unwrap();
    assert_eq!(n, 2, "both freshly-registered workers must be counted");

    // Tight window — last_seen is up to a few ms old, so a 0-second window
    // should not include them (gt, not gte).
    let n_zero = workers::count_active_workers(&db, chrono::Duration::seconds(0))
        .await
        .unwrap();
    assert_eq!(n_zero, 0, "with a 0-second window nothing is active");
}

#[tokio::test]
async fn count_distinct_contributors_returns_distinct_user_ids() {
    let Some((db, _g)) = fresh_db().await else { return };

    // Two users, with one and two worker keys respectively → 2 distinct contributors.
    let alice = nasrudin_pg::query::users::create_firebase_user(
        &db, "fb_alice", "alice@test", None,
    )
    .await
    .unwrap();
    let bob = nasrudin_pg::query::users::create_firebase_user(
        &db, "fb_bob", "bob@test", None,
    )
    .await
    .unwrap();

    nasrudin_pg::query::api_keys::create(
        &db,
        Some(alice.id),
        "worker",
        "alice-w1",
        "nsk_worker_a1",
        "h",
        None,
    )
    .await
    .unwrap();
    nasrudin_pg::query::api_keys::create(
        &db,
        Some(bob.id),
        "worker",
        "bob-w1",
        "nsk_worker_b1",
        "h",
        None,
    )
    .await
    .unwrap();
    nasrudin_pg::query::api_keys::create(
        &db,
        Some(bob.id),
        "worker",
        "bob-w2",
        "nsk_worker_b2",
        "h",
        None,
    )
    .await
    .unwrap();

    let n = workers::count_distinct_contributors(&db).await.unwrap();
    assert_eq!(n, 2, "two distinct user_ids on worker keys");

    // A 'live' key for bob should not count.
    nasrudin_pg::query::api_keys::create(
        &db,
        Some(bob.id),
        "live",
        "bob-live",
        "nsk_live_xyz",
        "h",
        None,
    )
    .await
    .unwrap();
    let n2 = workers::count_distinct_contributors(&db).await.unwrap();
    assert_eq!(n2, 2, "live keys must not change the contributor count");
}
