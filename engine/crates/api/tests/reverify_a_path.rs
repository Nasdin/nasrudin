//! Integration test for the reverify queue's full ingest-to-Verified flow.
//!
//! Phase 9 / Task 3.4. The current `try_regenerate_lean` is a stub that
//! returns `None` on every call, which forces every job through the B-path
//! (verify the worker-submitted Lean directly). This test asserts that the
//! B-path lifecycle works end-to-end:
//!
//!  1. A `Pending` row exists in PostgreSQL.
//!  2. A `ReverifyJob` exists in the RocksDB `reverify_queue` CF.
//!  3. `process_one(job)` runs preflight, `lake build`, and on success:
//!     - flips the row to `Verified` with `verification_path = "B"`,
//!     - increments the contributor's `theorems_contributed`,
//!     - broadcasts a `DiscoveryEvent::TheoremVerified`,
//!     - dequeues the job from RocksDB.
//!
//! The test is `#[ignore]`d because it shells out to `lake build`, which
//! requires the Lean toolchain to be installed and the `prover/` workspace
//! to be in a buildable state. Run nightly via:
//!
//! ```text
//! cargo test -p physics-api --test reverify_a_path -- --ignored --nocapture
//! ```

use std::sync::Arc;

use nasrudin_pg::query::{theorems as theorem_q, workers as worker_q};
use nasrudin_rocks::{ReverifyJob, TheoremDb};
use physics_api::lake_builder::LakeBuilder;
use physics_api::reverify::{DiscoveryEvent, ReverifyQueue};
use sea_orm::ConnectionTrait;
use tempfile::TempDir;
use tokio::sync::Mutex;

// Tests in this file share one PostgreSQL test database. We serialise with a
// process-wide async mutex held for the full body so concurrent migrations
// don't race on `pg_type_typname_nsp_index`.
static TEST_LOCK: Mutex<()> = Mutex::const_new(());

#[allow(clippy::type_complexity)]
async fn fresh_test_state() -> Option<(
    sea_orm::DatabaseConnection,
    Arc<TheoremDb>,
    tokio::sync::MutexGuard<'static, ()>,
    TempDir,
)> {
    let guard = TEST_LOCK.lock().await;
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    });
    let pg = nasrudin_pg::connect_simple(&url).await.ok()?;
    pg.execute_unprepared(
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
    .ok()?;
    nasrudin_pg::run_migrations(&pg).await.ok()?;

    let dir = tempfile::tempdir().ok()?;
    let rocks = Arc::new(TheoremDb::new(dir.path().to_str()?).ok()?);
    Some((pg, rocks, guard, dir))
}

/// Resolve the `prover/` workspace root from the crate manifest dir
/// (`engine/crates/api`), walking up to `engine/` then to the workspace root.
fn prover_root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("..")
        .join("prover")
}

#[tokio::test]
#[ignore] // Real `lake build` required; run with `cargo test -- --ignored`.
async fn b_path_verified_flips_status_and_increments_contributor() {
    let Some((pg, rocks, _guard, _dir)) = fresh_test_state().await else {
        eprintln!(
            "skipping: TEST_DATABASE_URL unreachable; \
             expected dev compose stack on 127.0.0.1:5432"
        );
        return;
    };

    // 1. Register the contributor that the theorem references.
    worker_q::register(&pg, "w1", None, None).await.unwrap();

    // 2. Build a LakeBuilder pointing at the real `prover/` tree.
    let lake = Arc::new(LakeBuilder::new(
        prover_root(),
        std::env::temp_dir(),
        1,
    ));
    let axiom_store =
        physics_api::state::SharedAxiomStore::new(nasrudin_derive::AxiomStore::new());
    let (tx, mut rx) = tokio::sync::broadcast::channel::<DiscoveryEvent>(16);

    // 3. Insert a Pending theorem with a trivially-true proof. The B-path
    //    will preflight + lake-build this source. Because `True := trivial`
    //    has no fresh axioms and no `sorry`, it passes preflight; lake build
    //    succeeds against the unmodified prover template.
    let canonical = "True";
    let id = nasrudin_core::theorem_id_from_canonical(canonical);
    let canonical_hash = nasrudin_core::canonical_hash(canonical);
    let row = theorem_q::NewTheorem {
        id: id.clone(),
        canonical_hash,
        canonical_statement: canonical.into(),
        domain: "PureMath".into(),
        lean_source: "theorem submission_proof : True := trivial".into(),
        chain_json: serde_json::json!([]),
        engine_git_sha: "test".into(),
        lean_version: "4.27.0".into(),
        contributor_id: "w1".into(),
        ..Default::default()
    };
    theorem_q::insert_pending(&pg, row).await.unwrap();

    let mut id_arr = [0u8; 8];
    id_arr.copy_from_slice(&id);
    rocks
        .enqueue_reverify(&ReverifyJob {
            theorem_id: id_arr,
            attempts: 0,
            enqueued_at_micros: 0,
        })
        .unwrap();

    // 4. Build the queue and drive one job.
    let q = Arc::new(ReverifyQueue {
        rocks: Arc::clone(&rocks),
        pg: pg.clone(),
        lake,
        axiom_store,
        discovery_tx: tx,
        cache_ctx: None,
        naming_client: None,
        naming_semaphore: Arc::new(tokio::sync::Semaphore::new(3)),
    });

    let job = rocks
        .list_reverify_pending(1)
        .unwrap()
        .into_iter()
        .next()
        .expect("queue non-empty after enqueue");
    q.process_one(job).await.unwrap();

    // 5. Assertions.
    let row_after = theorem_q::get_by_id(&pg, &id).await.unwrap().unwrap();
    assert_eq!(
        row_after.status, "Verified",
        "expected Verified after process_one"
    );
    assert_eq!(
        row_after.verification_path.as_deref(),
        Some("B"),
        "A-path is stubbed; B-path should have flipped this row"
    );

    let w = worker_q::get(&pg, "w1").await.unwrap().unwrap();
    assert_eq!(
        w.theorems_contributed, 1,
        "B-path success must increment the contributor counter"
    );

    // SSE event was broadcast.
    let evt = tokio::time::timeout(std::time::Duration::from_secs(1), rx.recv())
        .await
        .expect("DiscoveryEvent should arrive within 1s")
        .expect("channel must still be open");
    assert!(
        matches!(evt, DiscoveryEvent::TheoremVerified { .. }),
        "expected TheoremVerified event, got {evt:?}"
    );

    // Queue is empty after success.
    assert_eq!(rocks.reverify_queue_depth().unwrap(), 0);
}
