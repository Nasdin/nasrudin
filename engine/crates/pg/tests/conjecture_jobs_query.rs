//! Integration tests for the conjecture_jobs query layer (Phase E).
//!
//! Skipped gracefully when TEST_DATABASE_URL is unset.

use nasrudin_pg::{connect_simple, query::conjecture_jobs as q, query::users as u, run_migrations};
use sea_orm::{ConnectionTrait, DatabaseConnection};
use tokio::sync::{Mutex, MutexGuard};
use uuid::Uuid;

static TEST_LOCK: Mutex<()> = Mutex::const_new(());

async fn fresh_db() -> Option<(DatabaseConnection, MutexGuard<'static, ()>)> {
    let guard = TEST_LOCK.lock().await;
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    });
    let db = connect_simple(&url).await.ok()?;
    db.execute_unprepared(
        "DROP TABLE IF EXISTS conjecture_events CASCADE; \
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

async fn seed_owner(db: &DatabaseConnection) -> Uuid {
    let m = u::create_user(db, "owner@test", "x", Some("Owner"))
        .await
        .unwrap();
    m.id
}

async fn seed_queued(db: &DatabaseConnection, owner_id: Uuid) -> Uuid {
    let id = q::create(
        db,
        q::CreateInput {
            owner_id,
            hunch: "test".into(),
            domain_hint: None,
            provider: "anthropic".into(),
            model: "claude-sonnet-4-6".into(),
            budget: serde_json::json!({"wall_seconds": 60, "max_candidates": 100}),
        },
    )
    .await
    .unwrap();
    q::set_suggestions(db, id, serde_json::json!([{"axiom_set":[]}]))
        .await
        .unwrap();
    q::set_chosen_seed(db, id, 0, serde_json::json!({"axiom_set":[]}))
        .await
        .unwrap();
    id
}

#[tokio::test]
async fn claim_dequeues_oldest_queued_first() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db).await;
    let id_a = seed_queued(&db, owner).await;
    // Tiny pause so created_at differs deterministically.
    tokio::time::sleep(std::time::Duration::from_millis(5)).await;
    let _id_b = seed_queued(&db, owner).await;

    let claimed = q::claim_next(&db, "worker-1").await.unwrap();
    assert!(claimed.is_some());
    assert_eq!(claimed.unwrap().id, id_a);

    let row = q::get_by_id(&db, id_a).await.unwrap().unwrap();
    assert_eq!(row.state, "Running");
    assert_eq!(row.claimed_by.as_deref(), Some("worker-1"));
    assert!(row.lease_expires_at.is_some());
}

#[tokio::test]
async fn claim_returns_none_when_empty() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    assert!(q::claim_next(&db, "worker-1").await.unwrap().is_none());
}

#[tokio::test]
async fn heartbeat_extends_lease_and_updates_counters() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    let n = q::update_heartbeat_progress(&db, id, "worker-1", 42, 3)
        .await
        .unwrap();
    assert_eq!(n, 1);

    let row = q::get_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(row.candidates_attempted, 42);
    assert_eq!(row.candidates_verified, 3);
}

#[tokio::test]
async fn heartbeat_rejects_wrong_worker() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    let n = q::update_heartbeat_progress(&db, id, "worker-2", 1, 0)
        .await
        .unwrap();
    assert_eq!(n, 0, "wrong worker must not extend the lease");
}

#[tokio::test]
async fn append_verified_theorem_increments_counter() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    let theorem_id = vec![0xde, 0xad, 0xbe, 0xef, 0, 1, 2, 3];
    let n = q::append_verified_theorem(&db, id, "worker-1", theorem_id.clone())
        .await
        .unwrap();
    assert_eq!(n, 1);

    let row = q::get_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(row.candidates_verified, 1);
    assert_eq!(row.verified_theorem_ids.unwrap(), vec![theorem_id]);
}

#[tokio::test]
async fn complete_transitions_state() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    let n = q::complete(&db, id, "worker-1", "NoResult").await.unwrap();
    assert_eq!(n, 1);

    let row = q::get_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(row.state, "Complete");
    assert_eq!(row.outcome.as_deref(), Some("NoResult"));
    assert!(row.completed_at.is_some());
}

#[tokio::test]
async fn complete_rejects_wrong_worker() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    let n = q::complete(&db, id, "worker-2", "NoResult").await.unwrap();
    assert_eq!(n, 0);
}

#[tokio::test]
async fn reaper_requeues_expired_leases() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    db.execute_unprepared(&format!(
        "UPDATE conjecture_jobs SET lease_expires_at = NOW() - INTERVAL '1 minute' WHERE id = '{id}'"
    ))
    .await
    .unwrap();

    let requeued = q::requeue_expired_leases(&db).await.unwrap();
    assert_eq!(requeued, vec![id]);

    let row = q::get_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(row.state, "QueuedForWorker");
    assert!(row.claimed_by.is_none());
    assert!(row.lease_expires_at.is_none());
}

#[tokio::test]
async fn reaper_leaves_active_leases_alone() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    let requeued = q::requeue_expired_leases(&db).await.unwrap();
    assert!(requeued.is_empty());

    let row = q::get_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(row.state, "Running");
}
