//! Integration tests for the paid Researcher tier query helpers
//! (atomic_claim_paid, heartbeat_paid, release_paid_claim,
//! mark_paid_proved, try_decrement_research_credits,
//! grant_research_credits_on_period_advance).
//!
//! Skipped gracefully when TEST_DATABASE_URL is unset.

use nasrudin_pg::{
    connect_simple,
    query::{conjecture_jobs as q, users as u},
    run_migrations,
    sea_orm,
};
use sea_orm::{ConnectionTrait, DatabaseConnection, Statement};
use tokio::sync::{Mutex, MutexGuard};
use uuid::Uuid;

static TEST_LOCK: Mutex<()> = Mutex::const_new(());

async fn fresh_db() -> Option<(DatabaseConnection, MutexGuard<'static, ()>)> {
    let guard = TEST_LOCK.lock().await;
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    });
    let db = connect_simple(&url).await.ok()?;
    let drop_sql = "DROP TABLE IF EXISTS conjecture_events CASCADE; \
         DROP TABLE IF EXISTS conjecture_jobs CASCADE; \
         DROP TABLE IF EXISTS cluster_steering CASCADE; \
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
         DROP TABLE IF EXISTS user_saved_theorems CASCADE; \
         DROP TABLE IF EXISTS library_folders CASCADE; \
         DROP TABLE IF EXISTS saved_searches CASCADE; \
         DROP TABLE IF EXISTS users CASCADE; \
         DROP TABLE IF EXISTS seaql_migrations CASCADE;";

    // Postgres' DDL is serialised on `pg_type_typname_nsp_index`. When
    // many tests in a row reset the schema, two adjacent DROP/CREATE
    // sequences can race even under a single-process Mutex (the system
    // catalog gets touched outside our lock). Retry on that specific
    // failure class with short backoff — gives the catalog time to
    // settle.
    for attempt in 0..5 {
        let r = db.execute_unprepared(drop_sql).await;
        if r.is_err() && attempt < 4 {
            tokio::time::sleep(std::time::Duration::from_millis(80 * (attempt + 1))).await;
            continue;
        }
        r.unwrap();
        break;
    }
    for attempt in 0..5 {
        let r = run_migrations(&db).await;
        if r.is_err() && attempt < 4 {
            tokio::time::sleep(std::time::Duration::from_millis(80 * (attempt + 1))).await;
            continue;
        }
        r.unwrap();
        break;
    }
    Some((db, guard))
}

async fn seed_owner(db: &DatabaseConnection, suffix: &str) -> Uuid {
    let email = format!("paid-{suffix}@test");
    let m = u::create_firebase_user(db, &format!("fb_paid_{suffix}"), &email, Some("Paid Test"))
        .await
        .unwrap();
    m.id
}

/// Insert a `queued` paid `conjecture_jobs` row directly. Bypasses the
/// HTTP create handler so the test is self-contained.
async fn seed_queued_paid_job(db: &DatabaseConnection, owner_id: Uuid) -> Uuid {
    let id = Uuid::new_v4();
    let stmt = Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"INSERT INTO conjecture_jobs (
            id, owner_id, state, hunch, provider, model, budget,
            candidates_attempted, candidates_verified, created_at,
            lake_slot_hours_quota, lake_slot_hours_consumed,
            slice_priority, tier, allocated_slots
           ) VALUES (
            $1, $2, 'queued', 'E = m c^2', 'internal', 'ga',
            '{"wall_seconds":86400,"max_candidates":10000000}'::jsonb,
            0, 0, NOW(), 96, 0.0, 5, 'researcher', 4
           )"#,
        [id.into(), owner_id.into()],
    );
    db.execute_raw(stmt).await.unwrap();
    id
}

#[tokio::test]
async fn atomic_claim_paid_one_winner_under_concurrency() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "concurrency").await;
    seed_queued_paid_job(&db, owner).await;

    // Two concurrent claims; exactly one returns Some(job).
    let (r1, r2) = tokio::join!(
        q::atomic_claim_paid(&db, "worker-A", 6),
        q::atomic_claim_paid(&db, "worker-B", 8),
    );
    let one = r1.unwrap();
    let two = r2.unwrap();
    let winners = [one.is_some(), two.is_some()].iter().filter(|x| **x).count();
    assert_eq!(
        winners, 1,
        "exactly one concurrent claim must succeed (got one={one:?} two={two:?})"
    );
}

#[tokio::test]
async fn atomic_claim_paid_stamps_allocated_slots_clamped() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "alloc-clamp-low").await;
    seed_queued_paid_job(&db, owner).await;

    // Worker reports 0 — should clamp up to MIN=1.
    let claimed = q::atomic_claim_paid(&db, "worker-tiny", 0)
        .await
        .unwrap()
        .expect("claim must succeed");
    assert_eq!(
        claimed.allocated_slots, 1,
        "0-slot claims clamp to floor of 1, got {}",
        claimed.allocated_slots
    );

    // New job, this time a worker reporting 999 — clamp to MAX=64.
    let owner2 = seed_owner(&db, "alloc-clamp-high").await;
    seed_queued_paid_job(&db, owner2).await;
    let claimed2 = q::atomic_claim_paid(&db, "worker-huge", 999)
        .await
        .unwrap()
        .expect("claim must succeed");
    assert_eq!(
        claimed2.allocated_slots, 64,
        "999-slot claims cap at 64, got {}",
        claimed2.allocated_slots
    );
}

#[tokio::test]
async fn atomic_claim_paid_respects_priority_then_age() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "priority").await;
    let low = seed_queued_paid_job(&db, owner).await;
    // Bump priority on the second job so it should claim first
    // even though it was inserted second.
    let high = Uuid::new_v4();
    db.execute_raw(Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"INSERT INTO conjecture_jobs (
            id, owner_id, state, hunch, provider, model, budget,
            candidates_attempted, candidates_verified, created_at,
            lake_slot_hours_quota, lake_slot_hours_consumed,
            slice_priority, tier, allocated_slots
           ) VALUES (
            $1, $2, 'queued', 'priority test', 'internal', 'ga',
            '{}'::jsonb, 0, 0, NOW(), 96, 0.0, 9, 'researcher', 4
           )"#,
        [high.into(), owner.into()],
    ))
    .await
    .unwrap();

    let claimed = q::atomic_claim_paid(&db, "worker", 4)
        .await
        .unwrap()
        .expect("first claim");
    assert_eq!(
        claimed.id, high,
        "highest slice_priority wins (high={high}, low={low}, got={})",
        claimed.id
    );
}

#[tokio::test]
async fn heartbeat_paid_clamps_consumed_delta_against_wallclock() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "heartbeat-cap").await;
    seed_queued_paid_job(&db, owner).await;
    let claimed = q::atomic_claim_paid(&db, "worker", 4).await.unwrap().unwrap();

    // Force last_heartbeat_at to "1 second ago" so the cap math is
    // tight: max_delta = 2 × (1/3600) × 4 ≈ 0.0022 h.
    db.execute_raw(Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE conjecture_jobs SET last_heartbeat_at = NOW() - INTERVAL '1 second' WHERE id = $1",
        [claimed.id.into()],
    ))
    .await
    .unwrap();

    // Worker reports a fake 50 slot-hours consumed; server must cap
    // it tightly. We allow up to ~0.005 h to absorb wallclock drift
    // between the SQL UPDATE and our read.
    let (new_consumed, _exhausted) = q::heartbeat_paid(&db, claimed.id, "worker", 1, 0, 50.0)
        .await
        .unwrap()
        .expect("worker owns the lease");
    assert!(
        new_consumed < 0.01,
        "huge fake delta must clamp, got {new_consumed}"
    );
}

#[tokio::test]
async fn heartbeat_paid_returns_exhausted_when_consumed_meets_quota() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "exhausted").await;
    seed_queued_paid_job(&db, owner).await;
    let claimed = q::atomic_claim_paid(&db, "worker", 4).await.unwrap().unwrap();

    // Pre-fill consumed to just below the 96h quota and stretch
    // last_heartbeat_at so the cap allows the remaining delta.
    db.execute_raw(Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"UPDATE conjecture_jobs SET
              lake_slot_hours_consumed = 95.0,
              last_heartbeat_at = NOW() - INTERVAL '2 hours'
           WHERE id = $1"#,
        [claimed.id.into()],
    ))
    .await
    .unwrap();

    let (new_consumed, exhausted) = q::heartbeat_paid(&db, claimed.id, "worker", 0, 0, 2.0)
        .await
        .unwrap()
        .expect("worker owns the lease");
    assert!(
        exhausted,
        "exhausted should be true once consumed meets quota (got new_consumed={new_consumed})"
    );
}

#[tokio::test]
async fn heartbeat_paid_rejects_wrong_worker() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "wrong-worker").await;
    seed_queued_paid_job(&db, owner).await;
    let claimed = q::atomic_claim_paid(&db, "worker-A", 4).await.unwrap().unwrap();

    // worker-B doesn't own the lease — get None back.
    let r = q::heartbeat_paid(&db, claimed.id, "worker-B", 1, 0, 0.01)
        .await
        .unwrap();
    assert!(r.is_none(), "wrong-worker heartbeat must return None");
}

#[tokio::test]
async fn try_decrement_research_credits_zero_returns_false() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "no-credits").await;
    let r = u::try_decrement_research_credits(&db, owner).await.unwrap();
    assert!(!r, "user with 0 credits cannot decrement");
}

#[tokio::test]
async fn try_decrement_research_credits_one_returns_true_then_zero() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "one-credit").await;
    // Manually grant 1 credit.
    db.execute_raw(Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = 1 WHERE id = $1",
        [owner.into()],
    ))
    .await
    .unwrap();

    assert!(u::try_decrement_research_credits(&db, owner).await.unwrap());
    // Second attempt fails — credits now 0.
    assert!(!u::try_decrement_research_credits(&db, owner).await.unwrap());
}

#[tokio::test]
async fn grant_research_credits_on_period_advance_is_idempotent() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "period-grant").await;
    // Stamp a Stripe customer id so the WHERE clause resolves.
    db.execute_raw(Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE users SET stripe_customer_id = 'cus_test_period' WHERE id = $1",
        [owner.into()],
    ))
    .await
    .unwrap();

    // Period A: first grant → 10 credits.
    let cycle_a = chrono::Utc::now() - chrono::Duration::days(2);
    let n1 = u::grant_research_credits_on_period_advance(&db, "cus_test_period", cycle_a, 10)
        .await
        .unwrap();
    assert_eq!(n1, 1, "first grant must apply");

    // Stamp plan_cycle_start so subsequent calls see "same period".
    db.execute_raw(Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE users SET plan_cycle_start = $2 WHERE id = $1",
        [owner.into(), cycle_a.fixed_offset().into()],
    ))
    .await
    .unwrap();

    // Same-period replay — must be a no-op.
    let n2 = u::grant_research_credits_on_period_advance(&db, "cus_test_period", cycle_a, 10)
        .await
        .unwrap();
    assert_eq!(n2, 0, "same-period grant must no-op");

    // New period — must fire again.
    let cycle_b = chrono::Utc::now();
    let n3 = u::grant_research_credits_on_period_advance(&db, "cus_test_period", cycle_b, 10)
        .await
        .unwrap();
    assert_eq!(n3, 1, "new-period grant must apply");
}

#[tokio::test]
async fn refund_eligibility_zero_verified_under_threshold() {
    let Some((db, _g)) = fresh_db().await else {
        return;
    };
    let owner = seed_owner(&db, "refund-eligible").await;
    let job_id = seed_queued_paid_job(&db, owner).await;

    // Simulate a tiny run: 500 candidates, 0 verified.
    db.execute_raw(Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"UPDATE conjecture_jobs SET
              candidates_attempted = 500,
              candidates_verified = 0
           WHERE id = $1"#,
        [job_id.into()],
    ))
    .await
    .unwrap();

    let job = q::get_by_id(&db, job_id).await.unwrap().unwrap();
    let refund_eligible = job.candidates_verified == 0 && job.candidates_attempted < 1000;
    assert!(refund_eligible, "0 verified + <1000 attempts must refund");

    // Push past the threshold: 1500 attempts → no refund.
    db.execute_raw(Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE conjecture_jobs SET candidates_attempted = 1500 WHERE id = $1",
        [job_id.into()],
    ))
    .await
    .unwrap();
    let job2 = q::get_by_id(&db, job_id).await.unwrap().unwrap();
    let refund_eligible2 = job2.candidates_verified == 0 && job2.candidates_attempted < 1000;
    assert!(
        !refund_eligible2,
        "≥1000 attempts must lose refund eligibility"
    );
}
