//! Integration tests for the theorems query layer.
//!
//! These tests run against a live PostgreSQL test database. They are skipped
//! gracefully if `TEST_DATABASE_URL` is not set and the default connection
//! cannot be established.
//!
//! The default URL points at the dev compose stack:
//! `postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test`.

use sea_orm::ConnectionTrait;
use tokio::sync::{Mutex, MutexGuard};

// Tests in this file share one PostgreSQL test database and each `fresh_db()`
// DROPs and re-creates the schema. Cargo runs `#[tokio::test]` cases
// concurrently by default, which both (a) races migrations (PostgreSQL
// serialises DDL globally — the second concurrent migrate trips
// `pg_type_typname_nsp_index`) and (b) drops tables out from under any test
// still running. We serialise with a process-wide async mutex held for the
// entire test body, making the suite safe under default `cargo test`.
static DB_LOCK: Mutex<()> = Mutex::const_new(());

async fn fresh_db()
-> Option<(sea_orm::DatabaseConnection, MutexGuard<'static, ()>)> {
    let guard = DB_LOCK.lock().await;
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    });
    let db = nasrudin_pg::connect_simple(&url).await.ok()?;
    db.execute_unprepared(
        "DROP TABLE IF EXISTS conjecture_events CASCADE; \
         DROP TABLE IF EXISTS conjecture_jobs CASCADE; \
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
    nasrudin_pg::run_migrations(&db).await.unwrap();
    Some((db, guard))
}

fn sample_theorem(canonical: &str) -> nasrudin_pg::query::theorems::NewTheorem {
    nasrudin_pg::query::theorems::NewTheorem {
        id: nasrudin_core::theorem_id_from_canonical(canonical),
        canonical_hash: nasrudin_core::canonical_hash(canonical),
        canonical_statement: canonical.into(),
        domain: "SpecialRelativity".into(),
        lean_source: "import PhysicsGenerator.Axioms".into(),
        axioms_used: vec!["c_positive".into()],
        chain_json: serde_json::json!([]),
        engine_git_sha: "deadbee".into(),
        lean_version: "4.27.0".into(),
        contributor_id: "test-worker".into(),
        ..Default::default()
    }
}

#[tokio::test]
async fn insert_and_get_by_hash() {
    let Some((db, _guard)) = fresh_db().await else {
        return;
    };

    let n = sample_theorem("E = m*c^2");
    let expected_hash = n.canonical_hash.clone();
    let expected_id = n.id.clone();

    let id = nasrudin_pg::query::theorems::insert_pending(&db, n)
        .await
        .unwrap();
    assert_eq!(id, expected_id);

    let row = nasrudin_pg::query::theorems::get_by_canonical_hash(&db, &expected_hash)
        .await
        .unwrap()
        .expect("row must exist");

    assert_eq!(row.id, expected_id);
    assert_eq!(row.canonical_statement, "E = m*c^2");
    assert_eq!(row.status, "Pending");
    assert_eq!(row.origin_kind, "Axiom"); // default
    assert!(row.verified_at.is_none());
    assert!(row.verification_path.is_none());
}

#[tokio::test]
async fn dedup_returns_existing() {
    let Some((db, _guard)) = fresh_db().await else {
        return;
    };

    let canonical = "p = m*v";
    let n1 = sample_theorem(canonical);
    let hash = n1.canonical_hash.clone();
    let id1 = nasrudin_pg::query::theorems::insert_pending(&db, n1)
        .await
        .unwrap();

    // Same canonical_hash → unique-constraint violation.
    let n2 = sample_theorem(canonical);
    let dup = nasrudin_pg::query::theorems::insert_pending(&db, n2).await;
    assert!(
        dup.is_err(),
        "duplicate canonical_hash insert must fail, got Ok"
    );

    let existing = nasrudin_pg::query::theorems::get_by_canonical_hash(&db, &hash)
        .await
        .unwrap()
        .expect("original row must remain");
    assert_eq!(existing.id, id1);
}

#[tokio::test]
async fn mark_verified_sets_path_and_timestamp() {
    let Some((db, _guard)) = fresh_db().await else {
        return;
    };

    let n = sample_theorem("F = m*a");
    let id = nasrudin_pg::query::theorems::insert_pending(&db, n)
        .await
        .unwrap();

    nasrudin_pg::query::theorems::mark_verified(&db, &id, "A", "nlinarith", 42)
        .await
        .unwrap();

    let row = nasrudin_pg::query::theorems::get_by_id(&db, &id)
        .await
        .unwrap()
        .expect("row must exist");
    assert_eq!(row.status, "Verified");
    assert_eq!(row.verification_path.as_deref(), Some("A"));
    assert_eq!(row.verification_tactic.as_deref(), Some("nlinarith"));
    assert_eq!(row.verification_duration_ms, Some(42));
    assert!(row.verified_at.is_some());
}

#[tokio::test]
async fn list_with_cursor_returns_in_order_and_paginates() {
    let Some((db, _guard)) = fresh_db().await else {
        return;
    };

    // Seed 5 distinct verified theorems. Different canonical statements →
    // different IDs/hashes. Verify them in order so verified_at is monotonic.
    let mut ids: Vec<Vec<u8>> = Vec::new();
    for i in 0..5 {
        let stmt = format!("theorem_{i}: E_{i} = m_{i}*c^2");
        let n = sample_theorem(&stmt);
        let id = nasrudin_pg::query::theorems::insert_pending(&db, n)
            .await
            .unwrap();
        nasrudin_pg::query::theorems::mark_verified(&db, &id, "A", "nlinarith", 10 + i as i32)
            .await
            .unwrap();
        ids.push(id);
        // Ensure verified_at differs across rows so ordering is deterministic.
        tokio::time::sleep(std::time::Duration::from_millis(5)).await;
    }

    let page1 = nasrudin_pg::query::theorems::list_verified(&db, None, 3, None)
        .await
        .unwrap();
    assert_eq!(page1.items.len(), 3);
    assert!(page1.next_cursor.is_some(), "must have next cursor");
    assert_eq!(page1.total, 5);
    assert!(!page1.total_capped);

    // Order: most recently verified first (verified_at DESC).
    assert_eq!(page1.items[0].canonical_statement, "theorem_4: E_4 = m_4*c^2");
    assert_eq!(page1.items[1].canonical_statement, "theorem_3: E_3 = m_3*c^2");
    assert_eq!(page1.items[2].canonical_statement, "theorem_2: E_2 = m_2*c^2");

    let page2 = nasrudin_pg::query::theorems::list_verified(&db, page1.next_cursor, 3, None)
        .await
        .unwrap();
    assert_eq!(page2.items.len(), 2);
    assert!(page2.next_cursor.is_none(), "no more pages");
    assert_eq!(page2.items[0].canonical_statement, "theorem_1: E_1 = m_1*c^2");
    assert_eq!(page2.items[1].canonical_statement, "theorem_0: E_0 = m_0*c^2");
}
