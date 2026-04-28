//! Integration tests for boot-time RocksDB hydration from Postgres.
//!
//! These tests run against a live PostgreSQL test database. They are skipped
//! gracefully if `TEST_DATABASE_URL` is not set and the default connection
//! cannot be established. The default URL points at the dev compose stack:
//! `postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test`.
//!
//! Tests share one Postgres database and each one DROPs + re-creates the
//! schema. We serialise with a process-wide async mutex held for the full
//! body of every test — both because PostgreSQL serialises DDL globally
//! (concurrent migrations race on `pg_type_typname_nsp_index`) and because
//! one test's DROP would otherwise yank tables out from under another.

use std::sync::Arc;

use physics_api::hydration::hydrate_rocks_from_pg_if_empty;
use sea_orm::ConnectionTrait;
use tempfile::tempdir;
use tokio::sync::Mutex;

use nasrudin_pg::{connect_simple, query::theorems, run_migrations};
use nasrudin_rocks::TheoremDb;

static TEST_LOCK: Mutex<()> = Mutex::const_new(());

/// SQL drop statement matching the rest of the suite (theorems, auth, sessions,
/// preferences, saved searches, users, migrations metadata).
const RESET_SQL: &str = "DROP TABLE IF EXISTS theorems CASCADE; \
     DROP TABLE IF EXISTS workers CASCADE; \
     DROP TABLE IF EXISTS api_keys CASCADE; \
     DROP TABLE IF EXISTS sessions CASCADE; \
     DROP TABLE IF EXISTS user_preferences CASCADE; \
     DROP TABLE IF EXISTS saved_searches CASCADE; \
     DROP TABLE IF EXISTS users CASCADE; \
     DROP TABLE IF EXISTS seaql_migrations CASCADE;";

fn test_db_url() -> String {
    std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    })
}

#[tokio::test]
async fn empty_rocks_hydrates_from_pg() {
    let _g = TEST_LOCK.lock().await;
    let pg = match connect_simple(&test_db_url()).await {
        Ok(p) => p,
        Err(_) => return,
    };
    pg.execute_unprepared(RESET_SQL).await.unwrap();
    run_migrations(&pg).await.unwrap();

    // Seed 3 verified theorems with distinct canonical hashes.
    for i in 0..3u8 {
        let canonical = format!("test_{i}");
        let id = nasrudin_core::canonical_hash(&canonical);
        let row = theorems::NewTheorem {
            id: id.clone(),
            canonical_hash: id.clone(),
            canonical_statement: canonical.clone(),
            domain: "PureMath".into(),
            lean_source: format!("theorem t{i} : True := trivial"),
            chain_json: serde_json::json!([]),
            engine_git_sha: "test".into(),
            lean_version: "4.27.0".into(),
            contributor_id: "test".into(),
            ..Default::default()
        };
        theorems::insert_pending(&pg, row).await.unwrap();
        theorems::mark_verified(&pg, &id, "A", "rfl", 1).await.unwrap();
    }

    let rocks_dir = tempdir().unwrap();
    let rocks = Arc::new(TheoremDb::new(rocks_dir.path().to_str().unwrap()).unwrap());

    hydrate_rocks_from_pg_if_empty(&rocks, &pg).await.unwrap();

    let stats = rocks.get_stats().unwrap();
    assert_eq!(
        stats.total_theorems, 3,
        "all 3 verified theorems should be hydrated"
    );
    assert_eq!(
        stats.total_axioms, 0,
        "hydrated rows should be tagged Imported, not Axiom — \
         total_axioms must remain 0 after hydration"
    );

    for i in 0..3u8 {
        let id_vec = nasrudin_core::canonical_hash(&format!("test_{i}"));
        let mut id_arr = [0u8; 8];
        id_arr.copy_from_slice(&id_vec);
        assert!(
            rocks.theorem_exists(&id_arr).unwrap(),
            "theorem {i} should exist in RocksDB"
        );
    }
}

#[tokio::test]
async fn nonempty_rocks_skips_hydration() {
    let _g = TEST_LOCK.lock().await;
    let pg = match connect_simple(&test_db_url()).await {
        Ok(p) => p,
        Err(_) => return,
    };
    pg.execute_unprepared(RESET_SQL).await.unwrap();
    run_migrations(&pg).await.unwrap();

    let id = nasrudin_core::canonical_hash("seed");
    let row = theorems::NewTheorem {
        id: id.clone(),
        canonical_hash: id.clone(),
        canonical_statement: "seed".into(),
        domain: "PureMath".into(),
        lean_source: "x".into(),
        chain_json: serde_json::json!([]),
        engine_git_sha: "t".into(),
        lean_version: "1".into(),
        contributor_id: "t".into(),
        ..Default::default()
    };
    theorems::insert_pending(&pg, row).await.unwrap();
    theorems::mark_verified(&pg, &id, "A", "rfl", 1).await.unwrap();

    let rocks_dir = tempdir().unwrap();
    let rocks = Arc::new(TheoremDb::new(rocks_dir.path().to_str().unwrap()).unwrap());

    // First call hydrates the seeded theorem so total_theorems > 0.
    hydrate_rocks_from_pg_if_empty(&rocks, &pg).await.unwrap();
    let stats1 = rocks.get_stats().unwrap();
    assert_eq!(stats1.total_theorems, 1);

    // Second call should be a no-op (skip): if it weren't, the put_theorem
    // path would re-increment stats and total_theorems would jump to 2.
    hydrate_rocks_from_pg_if_empty(&rocks, &pg).await.unwrap();
    let stats2 = rocks.get_stats().unwrap();
    assert_eq!(
        stats2.total_theorems, 1,
        "second hydration should not double-count"
    );
}
