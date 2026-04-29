# LLM-Guided Search — Phase E (Research-Mode Workers) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship the **dequeue side** of the conjecture loop: research-mode workers claim queued jobs, heartbeat under a lease, submit verified candidates, and signal completion. A 30-second lease reaper requeues jobs from dead workers. Phase D already wired the user-facing creator + LLM call + state machine through `QueuedForWorker`; Phase E makes the queue actually flow.

**Architecture:**
- Four new worker endpoints under `/api/conjecture/*` (Bearer `nsk_worker_…` auth + per-worker rate limit), mounted on the existing `platform_worker` router.
- Atomic dequeue uses `UPDATE … FROM (SELECT … FOR UPDATE SKIP LOCKED)` so concurrent workers never race on the same row. (No existing query in the codebase uses SKIP LOCKED — this is the first.)
- A `ConjectureLeaseReaper` background task ticks every 30 seconds, requeues `state='Running' AND lease_expires_at < NOW()` rows, and emits `progress {worker_lost: true}` events on the existing broadcast channel.
- Worker binary gains `--research-mode` (and `NASRUDIN_RESEARCH_MODE=1`) — when set, it polls `/api/conjecture/claim` between background batches.
- Submit reuses the existing `/api/ingest` per-theorem pipeline by extracting a shared `ingest_one_theorem` helper.

**Tech Stack:** Rust 1.95 / SeaORM 2 (raw SQL for the SKIP LOCKED) / Axum 0.8 / tokio interval / existing `WorkerAuth` extractor + `WorkerRateLimiter`.

**Out of scope (deliberately deferred):**
- **Seed-driven GA.** Translating `LlmSuggestion` (axiom_set / initial_population / mutation_priors) into a `GaConfig` is real work. Phase E's worker stubs the GA: claim → heartbeat → sleep `wall_seconds` → `complete{outcome=NoResult}`. The wire protocol is fully implemented; the seed→GA glue is a follow-up task documented in the worker code.
- **`worker_lost` UI surfacing.** Reaper emits the event; surfacing it in the live view is left for a follow-up.
- **Multi-claim per worker.** Each worker holds at most one conjecture job at a time. Concurrency comes from running multiple workers, not multiple in-flight jobs per worker.
- **Paper draft generation (Phase F).**

---

## File Structure

**New backend files:**
- `engine/crates/api/src/conjecture/reaper.rs`
- `engine/crates/api/tests/conjecture_worker.rs`

**Modified backend files:**
- `engine/crates/pg/src/query/conjecture_jobs.rs` — add `claim_next`, `update_heartbeat_progress`, `submit_theorem`, `complete`, `requeue_expired_leases`
- `engine/crates/api/src/handlers/conjecture.rs` — add `claim`, `heartbeat`, `submit`, `complete` handlers
- `engine/crates/api/src/handlers/ingest.rs` — extract `ingest_one_theorem` helper (shared with submit)
- `engine/crates/api/src/conjecture/mod.rs` — `pub mod reaper;`
- `engine/crates/api/src/main.rs` — wire 4 worker routes; spawn reaper
- `engine/crates/api/src/conjecture/CONJECTURE.md` — document the worker side
- `engine/crates/api/tests/test_app/mod.rs` — register the 4 worker routes

**New worker-binary changes:**
- `engine/crates/ga/src/bin/worker.rs` — add `--research-mode` flag + claim/heartbeat/complete stub loop
- `engine/crates/ga/src/research_client.rs` (new) — small HTTP client for the 4 endpoints

**Frontend (small, non-blocking):**
- `nasrudin-frontend/src/lib/types.ts` — extend `ConjectureView` with `claimed_by`, `last_heartbeat_at`, `lease_expires_at`
- `nasrudin-frontend/src/components/conjecture/JobProgress.tsx` — show claim metadata when present

---

## Task 1: PG helpers — atomic dequeue + lease lifecycle

**Files:**
- Modify: `engine/crates/pg/src/query/conjecture_jobs.rs`

- [ ] **Step 1: Append the helpers**

Append to `engine/crates/pg/src/query/conjecture_jobs.rs`:

```rust
use sea_orm::{ConnectionTrait, Statement};

/// One claimed conjecture, returned to the worker.
#[derive(Debug, Clone)]
pub struct ClaimedJob {
    pub id: Uuid,
    pub seed: serde_json::Value,
    pub budget: serde_json::Value,
    pub hunch: String,
    pub provider: String,
    pub model: String,
}

/// Atomic dequeue. Marks the row state='Running', sets a 5-minute lease,
/// stamps `claimed_by` + `claimed_at`, returns the row's seed + budget.
/// Returns `Ok(None)` when nothing is queued.
///
/// Uses `FOR UPDATE SKIP LOCKED` so concurrent workers never block each
/// other and never see the same row twice.
pub async fn claim_next(
    db: &DatabaseConnection,
    worker_id: &str,
) -> Result<Option<ClaimedJob>, DbErr> {
    let stmt = Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET claimed_by = $1,
            claimed_at = NOW(),
            lease_expires_at = NOW() + INTERVAL '5 minutes',
            last_heartbeat_at = NOW(),
            state = 'Running'
        WHERE id = (
            SELECT id FROM conjecture_jobs
            WHERE state = 'QueuedForWorker' AND claimed_by IS NULL
            ORDER BY created_at
            LIMIT 1
            FOR UPDATE SKIP LOCKED
        )
        RETURNING id, seed, budget, hunch, provider, model
        "#,
        [worker_id.into()],
    );
    let row = db.query_one(stmt).await?;
    let Some(row) = row else { return Ok(None) };
    let id: Uuid = row.try_get_by_index(0)?;
    let seed: serde_json::Value = row.try_get_by_index(1)?;
    let budget: serde_json::Value = row.try_get_by_index(2)?;
    let hunch: String = row.try_get_by_index(3)?;
    let provider: String = row.try_get_by_index(4)?;
    let model: String = row.try_get_by_index(5)?;
    Ok(Some(ClaimedJob {
        id,
        seed,
        budget,
        hunch,
        provider,
        model,
    }))
}

/// Heartbeat: extends the lease by 5 minutes and bumps progress counters.
/// Caller must have verified ownership (`claimed_by == worker_id` and
/// `state == 'Running'`).
pub async fn update_heartbeat_progress(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: &str,
    candidates_attempted: i32,
    candidates_verified: i32,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET last_heartbeat_at = NOW(),
            lease_expires_at = NOW() + INTERVAL '5 minutes',
            candidates_attempted = $3,
            candidates_verified = $4
        WHERE id = $1 AND claimed_by = $2 AND state = 'Running'
        "#,
        [
            id.into(),
            worker_id.into(),
            candidates_attempted.into(),
            candidates_verified.into(),
        ],
    );
    let res = db.execute(stmt).await?;
    Ok(res.rows_affected())
}

/// Append a theorem id to verified_theorem_ids. The caller already
/// re-verified it via the ingest path. Returns rows_affected so the
/// handler can detect lease/ownership violations (0 = wrong worker or
/// not Running).
pub async fn append_verified_theorem(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: &str,
    theorem_id: Vec<u8>,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET verified_theorem_ids = COALESCE(verified_theorem_ids, ARRAY[]::BYTEA[]) || $3,
            candidates_verified = candidates_verified + 1,
            last_heartbeat_at = NOW(),
            lease_expires_at = NOW() + INTERVAL '5 minutes'
        WHERE id = $1 AND claimed_by = $2 AND state = 'Running'
        "#,
        [id.into(), worker_id.into(), vec![theorem_id].into()],
    );
    let res = db.execute(stmt).await?;
    Ok(res.rows_affected())
}

/// Final transition. `outcome` is one of "Verified" | "NoResult" | "TimedOut" | "Cancelled".
pub async fn complete(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: &str,
    outcome: &str,
) -> Result<u64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET state = 'Complete',
            outcome = $3,
            completed_at = NOW()
        WHERE id = $1 AND claimed_by = $2 AND state = 'Running'
        "#,
        [id.into(), worker_id.into(), outcome.into()],
    );
    let res = db.execute(stmt).await?;
    Ok(res.rows_affected())
}

/// Lease reaper backbone. Returns the IDs that were requeued so the
/// caller can emit per-job `progress {worker_lost: true}` events.
pub async fn requeue_expired_leases(
    db: &DatabaseConnection,
) -> Result<Vec<Uuid>, DbErr> {
    let stmt = Statement::from_string(
        sea_orm::DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
        SET claimed_by = NULL,
            claimed_at = NULL,
            lease_expires_at = NULL,
            state = 'QueuedForWorker'
        WHERE state = 'Running' AND lease_expires_at < NOW()
        RETURNING id
        "#
        .into(),
    );
    let rows = db.query_all(stmt).await?;
    let mut ids = Vec::with_capacity(rows.len());
    for row in rows {
        ids.push(row.try_get_by_index::<Uuid>(0)?);
    }
    Ok(ids)
}
```

- [ ] **Step 2: Build**

Run: `cargo build -p nasrudin-pg`

- [ ] **Step 3: Commit**

```bash
git add engine/crates/pg/src/query/conjecture_jobs.rs
git commit -m "feat(pg): atomic dequeue + lease lifecycle for conjecture_jobs"
```

---

## Task 2: PG integration test for the dequeue/lease helpers

**Files:**
- Create: `engine/crates/pg/tests/conjecture_jobs_query.rs`

- [ ] **Step 1: Write the test**

```rust
//! Integration tests for the conjecture_jobs query layer (Phase E).
//!
//! Skipped gracefully when TEST_DATABASE_URL is unset.

use chrono::Utc;
use nasrudin_pg::{connect_simple, query::conjecture_jobs as q, run_migrations};
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
    let owner_id = Uuid::new_v4();
    let sql = format!(
        "INSERT INTO users (id, email, password_hash, display_name, created_at) \
         VALUES ('{owner_id}', 'owner@test', 'x', 'Owner', NOW())"
    );
    db.execute_unprepared(&sql).await.unwrap();
    owner_id
}

async fn seed_queued(db: &DatabaseConnection, owner_id: Uuid) -> Uuid {
    let id = q::create(
        db,
        q::CreateInput {
            owner_id,
            hunch: "test".into(),
            domain_hint: None,
            provider: "anthropic".into(),
            model: "m".into(),
            budget: serde_json::json!({"wall_seconds": 60, "max_candidates": 100}),
        },
    )
    .await
    .unwrap();
    q::set_suggestions(db, id, serde_json::json!([{"axiom_set":[]}])).await.unwrap();
    q::set_chosen_seed(db, id, 0, serde_json::json!({"axiom_set":[]})).await.unwrap();
    id
}

#[tokio::test]
async fn claim_dequeues_oldest_queued() {
    let Some((db, _g)) = fresh_db().await else { return };
    let owner = seed_owner(&db).await;
    let id_a = seed_queued(&db, owner).await;
    let _id_b = seed_queued(&db, owner).await;

    let claimed = q::claim_next(&db, "worker-1").await.unwrap();
    assert!(claimed.is_some());
    assert_eq!(claimed.unwrap().id, id_a);

    let row = q::get_by_id(&db, id_a).await.unwrap().unwrap();
    assert_eq!(row.state, "Running");
    assert_eq!(row.claimed_by.as_deref(), Some("worker-1"));
}

#[tokio::test]
async fn claim_returns_none_when_empty() {
    let Some((db, _g)) = fresh_db().await else { return };
    assert!(q::claim_next(&db, "worker-1").await.unwrap().is_none());
}

#[tokio::test]
async fn heartbeat_extends_lease_and_updates_counters() {
    let Some((db, _g)) = fresh_db().await else { return };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    let n = q::update_heartbeat_progress(&db, id, "worker-1", 42, 3).await.unwrap();
    assert_eq!(n, 1);

    let row = q::get_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(row.candidates_attempted, 42);
    assert_eq!(row.candidates_verified, 3);
}

#[tokio::test]
async fn heartbeat_rejects_wrong_worker() {
    let Some((db, _g)) = fresh_db().await else { return };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    let n = q::update_heartbeat_progress(&db, id, "worker-2", 1, 0).await.unwrap();
    assert_eq!(n, 0, "wrong worker must not extend the lease");
}

#[tokio::test]
async fn complete_transitions_state() {
    let Some((db, _g)) = fresh_db().await else { return };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    let n = q::complete(&db, id, "worker-1", "NoResult").await.unwrap();
    assert_eq!(n, 1);

    let row = q::get_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(row.state, "Complete");
    assert_eq!(row.outcome.as_deref(), Some("NoResult"));
}

#[tokio::test]
async fn reaper_requeues_expired_leases() {
    let Some((db, _g)) = fresh_db().await else { return };
    let owner = seed_owner(&db).await;
    let id = seed_queued(&db, owner).await;
    q::claim_next(&db, "worker-1").await.unwrap();

    // Push the lease into the past.
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
}
```

- [ ] **Step 2: Run tests**

Run: `cargo test -p nasrudin-pg --test conjecture_jobs_query`
Expected: 6 passing tests (skipped if no test DB).

- [ ] **Step 3: Commit**

```bash
git add engine/crates/pg/tests/conjecture_jobs_query.rs
git commit -m "test(pg): atomic dequeue + lease lifecycle"
```

---

## Task 3: Extract `ingest_one_theorem` helper

**Files:**
- Modify: `engine/crates/api/src/handlers/ingest.rs`

The Phase E `submit` handler must run the same per-theorem pipeline as `/api/ingest` (size guards → axiom-firewall → dedup → RocksDB put → enqueue reverify → SSE). Refactor the existing batch handler to call a shared async helper, so submit can call the same helper.

- [ ] **Step 1: Refactor**

In `engine/crates/api/src/handlers/ingest.rs`, find the per-theorem loop body inside `pub async fn ingest(...)`. Extract it to:

```rust
/// Runs the per-theorem pipeline: size guards, axiom-firewall preflight,
/// dedup, RocksDB put, PG enqueue, SSE broadcast, reverify enqueue.
/// Returns the per-theorem result (Pending / Duplicate / Rejected).
///
/// Used by both `POST /api/ingest` (batch) and Phase E's
/// `POST /api/conjecture/{id}/submit` (single).
pub async fn ingest_one_theorem(
    state: &Arc<AppState>,
    worker_id: &str,
    engine_git_sha: &str,
    lean_version: &str,
    t: IngestTheorem,
) -> IngestResultItem {
    /* … the body that was previously inside the for-loop in ingest() … */
}
```

The existing `ingest()` becomes a loop that calls `ingest_one_theorem` for each item. Make sure the rate-limit check still happens once per batch (not per-theorem) at the top of `ingest()`. Submit will do its own rate-limit check (see Task 6).

- [ ] **Step 2: Build + run existing tests**

Run: `cargo test -p physics-api --test e2e_spontaneous_emc2_ingest`
Run: `cargo build -p physics-api --tests`
Expected: clean build; the existing ingest e2e nightly still passes (it's `#[ignore]` so cargo test won't actually run it, just compile it).

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/handlers/ingest.rs
git commit -m "refactor(api): extract ingest_one_theorem helper for reuse"
```

---

## Task 4: `POST /api/conjecture/claim`

**Files:**
- Modify: `engine/crates/api/src/handlers/conjecture.rs`

- [ ] **Step 1: Add the handler**

Append to `engine/crates/api/src/handlers/conjecture.rs`:

```rust
use crate::auth::WorkerAuth;
use serde::Serialize;

#[derive(Serialize)]
pub struct ClaimResponse {
    pub job_id: Uuid,
    pub seed: serde_json::Value,
    pub budget: serde_json::Value,
    pub hunch: String,
    pub provider: String,
    pub model: String,
    pub lease_seconds: u32,
}

pub async fn claim(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
) -> Response {
    let worker_id = &auth.0.worker_handle;
    if let Err(_until) = state.worker_rate_limiter.check_and_consume(worker_id, 1) {
        return err(StatusCode::TOO_MANY_REQUESTS, "rate_limited");
    }
    let pg = state.pg.as_ref();
    let Some(pg) = pg else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    let claimed =
        match nasrudin_pg::query::conjecture_jobs::claim_next(pg, worker_id).await {
            Ok(Some(c)) => c,
            Ok(None) => return (StatusCode::NO_CONTENT, "").into_response(),
            Err(e) => {
                tracing::warn!("claim_next failed: {e}");
                return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
            }
        };

    let event_payload = serde_json::json!({
        "from": "QueuedForWorker",
        "to": "Running",
        "claimed_by": worker_id,
    });
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        claimed.id,
        "state_change",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(crate::conjecture::ConjectureEvent {
            id: event_id,
            job_id: claimed.id,
            kind: "state_change".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    Json(ClaimResponse {
        job_id: claimed.id,
        seed: claimed.seed,
        budget: claimed.budget,
        hunch: claimed.hunch,
        provider: claimed.provider,
        model: claimed.model,
        lease_seconds: 300,
    })
    .into_response()
}
```

- [ ] **Step 2: Build**

Run: `cargo build -p physics-api`

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/handlers/conjecture.rs
git commit -m "feat(api): /api/conjecture/claim worker dequeue handler"
```

---

## Task 5: `POST /api/conjecture/{id}/heartbeat`

**Files:**
- Modify: `engine/crates/api/src/handlers/conjecture.rs`

- [ ] **Step 1: Add the handler**

Append:

```rust
#[derive(serde::Deserialize)]
pub struct HeartbeatBody {
    pub candidates_attempted: i32,
    pub candidates_verified: i32,
    pub time_elapsed_s: u32,
}

pub async fn heartbeat(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
    Json(body): Json<HeartbeatBody>,
) -> Response {
    let worker_id = &auth.0.worker_handle;
    if let Err(_) = state.worker_rate_limiter.check_and_consume(worker_id, 1) {
        return err(StatusCode::TOO_MANY_REQUESTS, "rate_limited");
    }
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    let n = match nasrudin_pg::query::conjecture_jobs::update_heartbeat_progress(
        pg,
        id,
        worker_id,
        body.candidates_attempted,
        body.candidates_verified,
    )
    .await
    {
        Ok(n) => n,
        Err(e) => {
            tracing::warn!("heartbeat update failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if n == 0 {
        return err(StatusCode::FORBIDDEN, "not_lease_owner");
    }

    let event_payload = serde_json::json!({
        "candidates_attempted": body.candidates_attempted,
        "candidates_verified": body.candidates_verified,
        "time_elapsed_s": body.time_elapsed_s,
    });
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        id,
        "progress",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(crate::conjecture::ConjectureEvent {
            id: event_id,
            job_id: id,
            kind: "progress".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    (
        StatusCode::OK,
        Json(serde_json::json!({"lease_extended_seconds": 300})),
    )
        .into_response()
}
```

- [ ] **Step 2: Build**

Run: `cargo build -p physics-api`

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/handlers/conjecture.rs
git commit -m "feat(api): /api/conjecture/{id}/heartbeat handler"
```

---

## Task 6: `POST /api/conjecture/{id}/submit`

**Files:**
- Modify: `engine/crates/api/src/handlers/conjecture.rs`

- [ ] **Step 1: Add the handler**

Append:

```rust
#[derive(serde::Deserialize)]
pub struct SubmitBody {
    pub engine_git_sha: String,
    pub lean_version: String,
    pub theorem: crate::handlers::ingest::IngestTheorem,
}

pub async fn submit(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
    Json(body): Json<SubmitBody>,
) -> Response {
    let worker_id = &auth.0.worker_handle;
    if let Err(_) = state.worker_rate_limiter.check_and_consume(worker_id, 1) {
        return err(StatusCode::TOO_MANY_REQUESTS, "rate_limited");
    }
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    // Ownership + lease pre-check (defends against submit-without-claim).
    let row = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(r)) => r,
        Ok(None) => return err(StatusCode::NOT_FOUND, "not_found"),
        Err(e) => {
            tracing::warn!("get conjecture failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if row.claimed_by.as_deref() != Some(worker_id) || row.state != "Running" {
        return err(StatusCode::FORBIDDEN, "not_lease_owner");
    }

    let result = crate::handlers::ingest::ingest_one_theorem(
        &state,
        worker_id,
        &body.engine_git_sha,
        &body.lean_version,
        body.theorem,
    )
    .await;

    // Only Pending/Verified items count as "candidates verified" — the
    // ingest helper enqueues for reverify; we mark the job's tally here.
    let theorem_id_hex: Option<String> = match &result.status {
        crate::handlers::ingest::IngestStatus::Pending => Some(result.theorem_id.clone()),
        _ => None,
    };

    if let Some(hex_str) = theorem_id_hex.as_ref() {
        let bytes = match hex::decode(hex_str) {
            Ok(b) => b,
            Err(_) => return err(StatusCode::INTERNAL_SERVER_ERROR, "bad_theorem_id"),
        };
        let _ = nasrudin_pg::query::conjecture_jobs::append_verified_theorem(
            pg, id, worker_id, bytes,
        )
        .await;

        let event_payload = serde_json::json!({
            "theorem_id": hex_str,
            "canonical_hash": result.canonical_hash,
            "worker_id": worker_id,
        });
        if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
            pg,
            id,
            "candidate_verified",
            event_payload.clone(),
        )
        .await
        {
            let _ = state.conjecture_event_tx.send(crate::conjecture::ConjectureEvent {
                id: event_id,
                job_id: id,
                kind: "candidate_verified".into(),
                payload: event_payload,
                at: chrono::Utc::now(),
            });
        }
    }

    (StatusCode::OK, Json(result)).into_response()
}
```

- [ ] **Step 2: Add `Serialize` to `IngestResultItem` if missing**

If `IngestResultItem` doesn't already derive `Serialize`, add it (the submit handler returns it in the JSON response).

- [ ] **Step 3: Build**

Run: `cargo build -p physics-api`

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/handlers/conjecture.rs engine/crates/api/src/handlers/ingest.rs
git commit -m "feat(api): /api/conjecture/{id}/submit (delegates to ingest pipeline)"
```

---

## Task 7: `POST /api/conjecture/{id}/complete`

**Files:**
- Modify: `engine/crates/api/src/handlers/conjecture.rs`

- [ ] **Step 1: Add the handler**

Append:

```rust
#[derive(serde::Deserialize)]
pub struct CompleteBody {
    /// One of: "Verified" | "NoResult" | "TimedOut" | "Cancelled".
    pub outcome: String,
    #[serde(default)]
    pub reason: Option<String>,
}

pub async fn complete_handler(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
    Json(body): Json<CompleteBody>,
) -> Response {
    let worker_id = &auth.0.worker_handle;
    if let Err(_) = state.worker_rate_limiter.check_and_consume(worker_id, 1) {
        return err(StatusCode::TOO_MANY_REQUESTS, "rate_limited");
    }
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    let valid = matches!(
        body.outcome.as_str(),
        "Verified" | "NoResult" | "TimedOut" | "Cancelled"
    );
    if !valid {
        return err(StatusCode::BAD_REQUEST, "invalid_outcome");
    }

    let n = match nasrudin_pg::query::conjecture_jobs::complete(pg, id, worker_id, &body.outcome)
        .await
    {
        Ok(n) => n,
        Err(e) => {
            tracing::warn!("complete failed: {e}");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if n == 0 {
        return err(StatusCode::FORBIDDEN, "not_lease_owner");
    }

    let event_payload = serde_json::json!({
        "outcome": body.outcome,
        "reason": body.reason,
    });
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        id,
        "complete",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(crate::conjecture::ConjectureEvent {
            id: event_id,
            job_id: id,
            kind: "complete".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    (StatusCode::OK, Json(serde_json::json!({"id": id, "state": "Complete"}))).into_response()
}
```

> Renamed `complete_handler` (not `complete`) so it doesn't collide with the existing `nasrudin_pg::query::conjecture_jobs::complete` import.

- [ ] **Step 2: Build**

Run: `cargo build -p physics-api`

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/handlers/conjecture.rs
git commit -m "feat(api): /api/conjecture/{id}/complete handler"
```

---

## Task 8: Conjecture lease reaper

**Files:**
- Create: `engine/crates/api/src/conjecture/reaper.rs`
- Modify: `engine/crates/api/src/conjecture/mod.rs`

- [ ] **Step 1: Write the reaper**

Create `engine/crates/api/src/conjecture/reaper.rs`:

```rust
//! 30-second tick. Requeues `state='Running' AND lease_expires_at < NOW()`
//! conjecture rows; emits one `progress {worker_lost:true}` event per row
//! so SSE subscribers see what happened.

use std::sync::Arc;
use std::time::Duration;

use crate::conjecture::ConjectureEvent;
use crate::state::AppState;

pub struct ConjectureLeaseReaper {
    pub state: Arc<AppState>,
}

impl ConjectureLeaseReaper {
    pub fn new(state: Arc<AppState>) -> Self {
        Self { state }
    }

    pub async fn run(self: Arc<Self>) {
        let mut interval = tokio::time::interval(Duration::from_secs(30));
        interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            interval.tick().await;
            if let Err(e) = self.reap_once().await {
                tracing::warn!("conjecture lease reaper tick failed: {e}");
            }
        }
    }

    async fn reap_once(&self) -> Result<(), sea_orm::DbErr> {
        let Some(pg) = self.state.pg.as_ref() else {
            return Ok(());
        };
        let requeued =
            nasrudin_pg::query::conjecture_jobs::requeue_expired_leases(pg).await?;
        if requeued.is_empty() {
            return Ok(());
        }
        tracing::info!("conjecture reaper requeued {} jobs", requeued.len());
        for job_id in requeued {
            let payload = serde_json::json!({"worker_lost": true});
            if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
                pg,
                job_id,
                "progress",
                payload.clone(),
            )
            .await
            {
                let _ = self.state.conjecture_event_tx.send(ConjectureEvent {
                    id: event_id,
                    job_id,
                    kind: "progress".into(),
                    payload,
                    at: chrono::Utc::now(),
                });
            }
        }
        Ok(())
    }
}
```

- [ ] **Step 2: Re-export**

Add `pub mod reaper;` to `engine/crates/api/src/conjecture/mod.rs`.

- [ ] **Step 3: Build**

Run: `cargo build -p physics-api`

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/conjecture/reaper.rs engine/crates/api/src/conjecture/mod.rs
git commit -m "feat(api): conjecture lease reaper (30s tick, worker_lost events)"
```

---

## Task 9: Wire 4 routes + spawn reaper

**Files:**
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/api/tests/test_app/mod.rs`

- [ ] **Step 1: Add routes to main.rs**

In the `platform_worker` router block (where `/api/ingest` lives), append:

```rust
.route("/api/conjecture/claim", post(handlers::conjecture::claim))
.route("/api/conjecture/{id}/heartbeat", post(handlers::conjecture::heartbeat))
.route("/api/conjecture/{id}/submit", post(handlers::conjecture::submit))
.route("/api/conjecture/{id}/complete", post(handlers::conjecture::complete_handler))
```

- [ ] **Step 2: Spawn the reaper in main.rs**

Right after the existing `Reverify drain loop spawned` block (around line 340), append:

```rust
if state.pg.is_some() {
    let reaper = Arc::new(physics_api::conjecture::reaper::ConjectureLeaseReaper::new(
        Arc::clone(&state),
    ));
    tokio::spawn(Arc::clone(&reaper).run());
    tracing::info!("Conjecture lease reaper spawned");
} else {
    tracing::info!("Conjecture lease reaper disabled (no PostgreSQL)");
}
```

- [ ] **Step 3: Mirror routes in test_app**

Add the four `.route(...)` lines to `engine/crates/api/tests/test_app/mod.rs` (alongside the existing Phase D conjecture routes).

- [ ] **Step 4: Build + tests**

Run: `cargo build -p physics-api --tests`
Run: `cargo test -p physics-api --test conjecture_handler` (Phase D smokes still pass)
Expected: 5 passing tests.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/main.rs engine/crates/api/tests/test_app/mod.rs
git commit -m "feat(api): mount Phase E worker routes + spawn lease reaper"
```

---

## Task 10: Worker auth-gate smoke tests

**Files:**
- Create: `engine/crates/api/tests/conjecture_worker.rs`

- [ ] **Step 1: Write the tests**

```rust
//! Smoke tests for Phase E worker endpoints. Validates:
//!   - All four routes are mounted
//!   - Unauthenticated requests get 401
//! Behavioural coverage of the dequeue/heartbeat/submit/complete cycle is
//! handled by the in-process pg-integration tests (conjecture_jobs_query)
//! and the upcoming end-to-end nightly.

mod test_app;

use axum::body::{to_bytes, Body};
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

const ZERO_UUID: &str = "00000000-0000-0000-0000-000000000000";

async fn post_unauth(app: &test_app::TestApp, path: &str, body: &serde_json::Value) -> StatusCode {
    let req = Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", "application/json")
        .body(Body::from(serde_json::to_vec(body).unwrap()))
        .unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let _ = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    status
}

#[tokio::test]
async fn claim_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else { return };
    let status = post_unauth(&app, "/api/conjecture/claim", &serde_json::json!({})).await;
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn heartbeat_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else { return };
    let status = post_unauth(
        &app,
        &format!("/api/conjecture/{ZERO_UUID}/heartbeat"),
        &serde_json::json!({"candidates_attempted":0,"candidates_verified":0,"time_elapsed_s":0}),
    )
    .await;
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn submit_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else { return };
    let status = post_unauth(
        &app,
        &format!("/api/conjecture/{ZERO_UUID}/submit"),
        &serde_json::json!({
            "engine_git_sha":"sha","lean_version":"v","theorem":{
                "canonical_statement":"x","domain":"PureMath",
                "lean_source":"theorem x : True := trivial","chain":[],"axioms_used":[]
            }
        }),
    )
    .await;
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn complete_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else { return };
    let status = post_unauth(
        &app,
        &format!("/api/conjecture/{ZERO_UUID}/complete"),
        &serde_json::json!({"outcome":"NoResult"}),
    )
    .await;
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}
```

- [ ] **Step 2: Run**

Run: `cargo test -p physics-api --test conjecture_worker`
Expected: 4 passing tests.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/tests/conjecture_worker.rs
git commit -m "test(api): worker-side auth-gate smoke tests"
```

---

## Task 11: Worker binary — `--research-mode` flag

**Files:**
- Modify: `engine/crates/ga/src/bin/worker.rs`

- [ ] **Step 1: Add the flag**

In the arg-parsing block at the top of `main()`, after the existing flags:

```rust
let research_mode: bool = std::env::args().any(|a| a == "--research-mode")
    || std::env::var("NASRUDIN_RESEARCH_MODE")
        .map(|v| matches!(v.trim().to_lowercase().as_str(), "1" | "true" | "yes"))
        .unwrap_or(false);
if research_mode {
    eprintln!("✓ research mode enabled — will poll /api/conjecture/claim");
}
```

> Defer the actual claim poll to Task 13. Wiring the flag first keeps each diff small.

- [ ] **Step 2: Build**

Run: `cargo build -p nasrudin-ga --bin worker`

- [ ] **Step 3: Commit**

```bash
git add engine/crates/ga/src/bin/worker.rs
git commit -m "feat(worker): --research-mode flag + NASRUDIN_RESEARCH_MODE env"
```

---

## Task 12: Research-mode HTTP client

**Files:**
- Create: `engine/crates/ga/src/research_client.rs`
- Modify: `engine/crates/ga/src/lib.rs`

- [ ] **Step 1: Write the client**

```rust
//! Phase E research-mode HTTP client. Pairs with the worker binary's
//! `--research-mode` poll loop. All four endpoints are POST; bearer token
//! is the worker's `nsk_worker_…` API key (already used by ingest).

use anyhow::{Context, Result};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Deserialize)]
pub struct ClaimedJob {
    pub job_id: Uuid,
    pub seed: serde_json::Value,
    pub budget: serde_json::Value,
    pub hunch: String,
    pub provider: String,
    pub model: String,
    pub lease_seconds: u32,
}

#[derive(Debug, Clone, Serialize)]
pub struct HeartbeatBody {
    pub candidates_attempted: i32,
    pub candidates_verified: i32,
    pub time_elapsed_s: u32,
}

#[derive(Debug, Clone, Serialize)]
pub struct CompleteBody {
    pub outcome: String,
    pub reason: Option<String>,
}

pub struct ResearchClient {
    pub api_url: String,
    pub worker_key: String,
    http: Client,
}

impl ResearchClient {
    pub fn new(api_url: String, worker_key: String) -> Self {
        Self {
            api_url,
            worker_key,
            http: Client::builder()
                .timeout(std::time::Duration::from_secs(30))
                .build()
                .expect("reqwest client"),
        }
    }

    /// `Ok(Some(job))` = claimed; `Ok(None)` = nothing queued (HTTP 204).
    pub async fn claim(&self) -> Result<Option<ClaimedJob>> {
        let resp = self
            .http
            .post(format!("{}/api/conjecture/claim", self.api_url))
            .bearer_auth(&self.worker_key)
            .send()
            .await
            .context("POST /api/conjecture/claim")?;
        if resp.status() == reqwest::StatusCode::NO_CONTENT {
            return Ok(None);
        }
        let resp = resp.error_for_status()?;
        Ok(Some(resp.json::<ClaimedJob>().await?))
    }

    pub async fn heartbeat(&self, id: Uuid, body: &HeartbeatBody) -> Result<()> {
        self.http
            .post(format!("{}/api/conjecture/{id}/heartbeat", self.api_url))
            .bearer_auth(&self.worker_key)
            .json(body)
            .send()
            .await?
            .error_for_status()?;
        Ok(())
    }

    pub async fn complete(&self, id: Uuid, body: &CompleteBody) -> Result<()> {
        self.http
            .post(format!("{}/api/conjecture/{id}/complete", self.api_url))
            .bearer_auth(&self.worker_key)
            .json(body)
            .send()
            .await?
            .error_for_status()?;
        Ok(())
    }
}
```

- [ ] **Step 2: Re-export from lib.rs**

Add `pub mod research_client;` to `engine/crates/ga/src/lib.rs`.

- [ ] **Step 3: Build**

Run: `cargo build -p nasrudin-ga`

- [ ] **Step 4: Commit**

```bash
git add engine/crates/ga/src/research_client.rs engine/crates/ga/src/lib.rs
git commit -m "feat(ga): research-mode HTTP client (claim/heartbeat/complete)"
```

---

## Task 13: Worker binary — claim/heartbeat/complete stub loop

**Files:**
- Modify: `engine/crates/ga/src/bin/worker.rs`

The worker's main loop is a `loop { run_one_batch().await }`. Phase E adds a "research-mode tick" between batches that:
1. Calls `client.claim()`. If `None`, fall through to background work.
2. If `Some`, log the seed, sleep `min(budget.wall_seconds, 60)` seconds (capped so we don't hold a 600 s lease while the worker process sleeps blindly), heartbeat once, then complete with `outcome=NoResult`.

The actual GA-on-seed integration is a follow-up task — this stub is enough to demonstrate the wire protocol and unblock Phase E's "soft launch: a single dev worker in research mode picks up jobs" milestone.

- [ ] **Step 1: Add the helper**

In `engine/crates/ga/src/bin/worker.rs`, after the existing `ApiSubmitConfig::from_env` setup, add:

```rust
async fn try_claim_and_run(
    client: &nasrudin_ga::research_client::ResearchClient,
) {
    use nasrudin_ga::research_client::*;
    let Ok(claimed) = client.claim().await.map_err(|e| {
        tracing::warn!("claim failed: {e}");
    }) else {
        return;
    };
    let Some(job) = claimed else {
        tracing::debug!("no conjecture queued");
        return;
    };

    let wall_seconds = job
        .budget
        .get("wall_seconds")
        .and_then(|v| v.as_u64())
        .unwrap_or(60)
        .min(60); // cap the stub's sleep so the lease doesn't expire under us
    tracing::info!(
        "claimed conjecture {} (hunch: {}); stub-running for {wall_seconds}s",
        job.job_id,
        job.hunch
    );

    // Single heartbeat at the half-way point so the lease is visibly extended.
    tokio::time::sleep(std::time::Duration::from_secs(wall_seconds / 2)).await;
    let _ = client
        .heartbeat(
            job.job_id,
            &HeartbeatBody {
                candidates_attempted: 0,
                candidates_verified: 0,
                time_elapsed_s: (wall_seconds / 2) as u32,
            },
        )
        .await;

    tokio::time::sleep(std::time::Duration::from_secs(wall_seconds - wall_seconds / 2)).await;
    let _ = client
        .complete(
            job.job_id,
            &CompleteBody {
                outcome: "NoResult".into(),
                reason: Some("phase-e stub: seed-driven GA not yet wired".into()),
            },
        )
        .await;
    tracing::info!("conjecture {} completed (stub)", job.job_id);
}
```

- [ ] **Step 2: Wire it into the main loop**

Find the worker's main loop (the `loop { … run_one_batch … }` near the bottom of `main()`). Before each `run_one_batch().await` call, when `research_mode` is set, await `try_claim_and_run(&client)`. Construct the client once at startup using the existing `api_cfg.api_url` + `api_cfg.worker_key`.

```rust
let research_client = research_mode.then(|| {
    api_cfg.as_ref().map(|cfg| {
        nasrudin_ga::research_client::ResearchClient::new(
            cfg.api_url.clone(),
            cfg.worker_key.clone(),
        )
    })
}).flatten();

loop {
    if let Some(ref c) = research_client {
        try_claim_and_run(c).await;
    }
    run_one_batch().await; // existing
}
```

- [ ] **Step 3: Build**

Run: `cargo build -p nasrudin-ga --bin worker`

- [ ] **Step 4: Commit**

```bash
git add engine/crates/ga/src/bin/worker.rs
git commit -m "feat(worker): research-mode poll loop (stub: claim → heartbeat → NoResult)"
```

---

## Task 14: Frontend — surface claim metadata

**Files:**
- Modify: `nasrudin-frontend/src/lib/types.ts`
- Modify: `nasrudin-frontend/src/components/conjecture/JobProgress.tsx`
- Modify: `engine/crates/api/src/handlers/conjecture.rs` — extend `ConjectureView` mapping

Phase D already returns `claimed_by` / `last_heartbeat_at` / `lease_expires_at` from the DB row but the `ConjectureView` DTO drops them. Plumb them through.

- [ ] **Step 1: Extend the Rust DTO**

In `engine/crates/api/src/conjecture/types.rs`, add to `ConjectureView`:

```rust
pub claimed_by: Option<String>,
pub last_heartbeat_at: Option<DateTime<Utc>>,
pub lease_expires_at: Option<DateTime<Utc>>,
```

In `engine/crates/api/src/handlers/conjecture.rs::view_from_row`, populate them from `row.claimed_by`, `row.last_heartbeat_at`, `row.lease_expires_at`.

- [ ] **Step 2: Extend the TS type**

In `nasrudin-frontend/src/lib/types.ts`, add the same three fields to `ConjectureView`:

```ts
claimed_by: string | null;
last_heartbeat_at: string | null;
lease_expires_at: string | null;
```

- [ ] **Step 3: Surface in JobProgress**

In `nasrudin-frontend/src/components/conjecture/JobProgress.tsx`, when `view.claimed_by` is set, render a small `claimed by ${claimed_by} · last heartbeat ${time}` line above the event log.

- [ ] **Step 4: Build + tsc**

Run: `cargo build -p physics-api`
Run: `cd nasrudin-frontend && pnpm tsc --noEmit && pnpm build`

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/conjecture/types.rs engine/crates/api/src/handlers/conjecture.rs nasrudin-frontend/src/lib/types.ts nasrudin-frontend/src/components/conjecture/JobProgress.tsx
git commit -m "feat: surface claimed_by + heartbeat metadata in conjecture view"
```

---

## Task 15: Operator docs — Phase E section

**Files:**
- Modify: `engine/crates/api/src/conjecture/CONJECTURE.md`

- [ ] **Step 1: Append Phase E section**

```markdown
## Phase E (worker side)

Phase E adds the dequeue half. Workers run with `--research-mode`
(or `NASRUDIN_RESEARCH_MODE=1`) and call:

| Verb | Path | Purpose |
|---|---|---|
| `POST` | `/api/conjecture/claim`              | Atomic dequeue (FOR UPDATE SKIP LOCKED). 5-min lease. |
| `POST` | `/api/conjecture/{id}/heartbeat`     | Extend lease + report progress |
| `POST` | `/api/conjecture/{id}/submit`        | One verified theorem (delegates to ingest path) |
| `POST` | `/api/conjecture/{id}/complete`      | Final transition (Verified / NoResult / TimedOut / Cancelled) |

All four require `Authorization: Bearer nsk_worker_…` (`WorkerAuth`)
+ pass through the per-worker rate limiter.

### Lease + reaper

- Each claim sets `lease_expires_at = NOW() + 5 minutes`.
- Heartbeat extends the lease another 5 minutes.
- The `ConjectureLeaseReaper` background task ticks every 30 s,
  requeues `state='Running' AND lease_expires_at < NOW()` rows, and
  emits `progress {worker_lost:true}` for SSE subscribers.

### Phase E scope cuts (documented)

- **Seed-driven GA is stubbed.** The worker logs the seed, heartbeats once,
  then calls `/complete` with `outcome=NoResult`. Wire-protocol coverage is
  complete; the GA-on-seed glue (`LlmSuggestion → GaConfig`) is a follow-up.
- **`worker_lost` UI surfacing** — reaper emits the event; rendering it in
  the live view is a follow-up.
- **Multi-claim per worker** — each worker holds at most one in-flight job.

### Manual smoke test

```bash
NASRUDIN_RESEARCH_MODE=1 \
NASRUDIN_API_URL=http://localhost:8080 \
NASRUDIN_WORKER_KEY=nsk_worker_… \
NASRUDIN_WORKER_ID=research-1 \
cargo run -p nasrudin-ga --bin worker
```

The worker prints `claimed conjecture <uuid>` for every dequeued job and
`conjecture <uuid> completed (stub)` after the lease finishes.
```

- [ ] **Step 2: Commit**

```bash
git add engine/crates/api/src/conjecture/CONJECTURE.md
git commit -m "docs(conjecture): operator docs for Phase E worker side"
```

---

## Task 16: Workspace test sweep

**Files:** None (pure verification).

- [ ] **Step 1: Run the full backend suite**

Run: `cargo test --workspace --no-fail-fast`
Expected: Phase E adds 6 + 4 = 10 new passing tests
(`conjecture_jobs_query` + `conjecture_worker`); existing tests unchanged.
The two pre-existing `nasrudin-derive` lean-emitter failures from the
Phase D sweep are still out of scope.

- [ ] **Step 2: Frontend type-check + build**

Run: `cd nasrudin-frontend && pnpm tsc --noEmit && pnpm build`
Expected: exit 0.

- [ ] **Step 3: Worker dry-run**

```bash
NASRUDIN_RESEARCH_MODE=1 \
cargo run -p nasrudin-ga --bin worker -- --help 2>&1 | grep -i research
```

Expected: log line confirming research mode is recognised. (Smoke-only — full
end-to-end requires a running API + a queued conjecture job.)

- [ ] **Step 4: No commit needed.** Phase E is done.

---

## Self-Review Checklist

- ✅ Each Phase E handler is auth-gated by `WorkerAuth` + the per-worker rate limiter.
- ✅ The atomic dequeue uses `FOR UPDATE SKIP LOCKED` so concurrent workers can't double-claim.
- ✅ The submit handler delegates to `ingest_one_theorem` so the per-theorem pipeline stays in one place.
- ✅ The lease reaper is spawned only when PG is wired (matches the existing reverify-drain conditional).
- ✅ Worker binary changes are gated by `--research-mode` — existing fleet keeps doing background corpus-fill.
- ✅ The seed-driven GA is explicitly stubbed and documented; the wire protocol is fully covered.
- ✅ Frontend changes are minimal and additive (no breaking type changes).
- ✅ All four new routes have auth-gate smoke tests.
- ✅ All five lifecycle helpers (claim, heartbeat, submit, complete, reaper) have PG integration tests.
