# Effort Slider Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let researchers size each paid conjecture from 1 to N credits at submit time (1 credit = 96 lake-slot-hours) and toggle a +1-credit "rush" priority bump, with race-safe Postgres-transactional debit/refund.

**Architecture:** Two new optional fields (`credits_budget`, `rush`) on `POST /api/research/jobs`. The submit handler runs decrement+insert as a single transaction; the cancel handler runs state-transition+refund as a single transaction with conditional `UPDATE ... WHERE state IN ('queued','claimed','running') RETURNING ...` so double-clicks are idempotent and concurrent heartbeats can't un-cancel. The frontend gains a slider and rush checkbox in `NewJobForm` and a `RUSH` chip in `JobRow`.

**Tech Stack:** Rust + Axum + SeaORM (raw `Statement` for transactional SQL); React + TanStack Query + TanStack Router; Postgres for the credit ledger.

**Spec:** `docs/superpowers/specs/2026-05-01-effort-slider-design.md` — note the spec uses `research_credits_remaining` in places; the actual column is `research_credits`. This plan uses the correct name throughout.

**Note on the existing column name discrepancy:** the spec was written against a misremembered column name. The truth-source is `engine/crates/pg/src/entity/users.rs:20` which defines `pub research_credits: i32`. All code in this plan uses `research_credits`.

---

## File Map

**Backend — modify:**
- `engine/crates/api/src/auth.rs` — add `research_credits` to `AuthUser` (struct + `from_model`).
- `engine/crates/pg/src/query/users.rs` — add `try_decrement_research_credits_n` and `refund_research_credits_n`; rewrite the existing single-credit fns as thin wrappers.
- `engine/crates/pg/src/query/conjecture_jobs.rs` — fix `heartbeat_paid` to no-op on terminal rows (add `state IN ('claimed','running')` to the `WHERE`); add new `cancel_paid_with_refund` function that runs conditional UPDATE + refund in one transaction.
- `engine/crates/api/src/handlers/research_jobs.rs` — extend `CreateBody` with `credits_budget`/`rush`; rewrite `create` to run decrement+insert in one transaction; rewrite `cancel` to call the new query helper.
- `engine/crates/api/src/jobs/mod.rs` (or wherever `JobEvent` lives) — add `refunded_credits` to `JobEvent::Cancelled`.

**Backend — tests:**
- `engine/crates/pg/tests/paid_researcher_queries.rs` — extend.
- `engine/crates/api/tests/research_jobs_submit.rs` — new file (integration tests for the create handler).
- `engine/crates/api/tests/research_jobs_cancel.rs` — new file.

**Frontend — modify:**
- `nasrudin-frontend/src/lib/types.ts` — add `research_credits` to `AuthUser`; extend `CreateResearchJobRequest`; change cancel response to `refunded_credits`; update `ResearchJobEvent` cancelled variant.
- `nasrudin-frontend/src/lib/queries.ts` — type updates only.
- `nasrudin-frontend/src/routes/research.tsx` — slider + rush toggle in `NewJobForm`; RUSH chip in `JobRow`; updated cancel copy + toast.

---

## Task 1: Add `research_credits` to `AuthUser` so `/api/auth/me` exposes it

**Files:**
- Modify: `engine/crates/api/src/auth.rs:35-70`
- Test: extend `engine/crates/api/tests/` (find existing auth-me test or add inline to a relevant file; if none exists, new file `engine/crates/api/tests/auth_me_credits.rs`)

- [ ] **Step 1: Find the existing `/api/auth/me` test (if any)**

Run: `grep -rn "/api/auth/me\|auth/me" engine/crates/api/tests/ 2>/dev/null`

If a relevant test file exists, extend it. Otherwise create `engine/crates/api/tests/auth_me_credits.rs` from scratch.

- [ ] **Step 2: Write failing test that `/api/auth/me` returns `research_credits`**

The exact test scaffolding depends on existing test harness. Pattern:

```rust
// engine/crates/api/tests/auth_me_credits.rs (or extension of existing)
#[tokio::test]
async fn auth_me_exposes_research_credits() {
    let (pg, _container) = test_pg().await; // existing helper
    let user_id = create_user_with_credits(&pg, 7).await;
    let app = build_app(pg.clone()).await;
    let token = sign_in_as(&app, user_id).await;

    let resp = app
        .oneshot(
            http::Request::builder()
                .uri("/api/auth/me")
                .header("cookie", token)
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let body: serde_json::Value =
        serde_json::from_slice(&hyper::body::to_bytes(resp.into_body()).await.unwrap())
            .unwrap();
    assert_eq!(body["research_credits"], serde_json::json!(7));
}
```

If the harness uses different helpers (likely — check first), adapt. The assertion is what matters.

- [ ] **Step 3: Run test, expect failure**

Run: `cargo test -p physics_api auth_me_exposes_research_credits`
Expected: FAIL — field `research_credits` is `null` or absent.

- [ ] **Step 4: Add `research_credits` to `AuthUser`**

In `engine/crates/api/src/auth.rs`:

```rust
pub struct AuthUser {
    pub id: Uuid,
    pub email: String,
    pub display_name: Option<String>,
    pub created_at: chrono::DateTime<chrono::FixedOffset>,
    pub plan_tier: String,
    pub stripe_customer_id: Option<String>,
    pub stripe_subscription_id: Option<String>,
    pub current_period_end: Option<chrono::DateTime<chrono::FixedOffset>>,
    pub plan_cycle_start: Option<chrono::DateTime<chrono::FixedOffset>>,
    pub firebase_uid: String,
    /// Lose-it-or-use-it research credits. Read on every paid-job
    /// submit; debited atomically inside the submit transaction.
    pub research_credits: i32,
}

impl AuthUser {
    pub fn from_model(m: nasrudin_pg::entity::users::Model) -> Self {
        Self {
            id: m.id,
            email: m.email,
            display_name: m.display_name,
            created_at: m.created_at,
            plan_tier: m.plan_tier,
            stripe_customer_id: m.stripe_customer_id,
            stripe_subscription_id: m.stripe_subscription_id,
            current_period_end: m.current_period_end,
            plan_cycle_start: m.plan_cycle_start,
            firebase_uid: m.firebase_uid,
            research_credits: m.research_credits,
        }
    }
}
```

- [ ] **Step 5: Run the test, expect pass**

Run: `cargo test -p physics_api auth_me_exposes_research_credits`
Expected: PASS.

- [ ] **Step 6: Run the wider auth test module**

Run: `cargo test -p physics_api auth`
Expected: All pass. The `AuthUser` change is additive; existing serialised payloads gain a field but don't lose any.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/auth.rs engine/crates/api/tests/
git commit -m "auth: surface research_credits on AuthUser / /api/auth/me

The effort-slider UI on /research needs to read the user's remaining
credits to bound the slider. Add the column to the AuthUser struct
and from_model mapping so /api/auth/me exposes it."
```

---

## Task 2: Add multi-credit decrement helper

**Files:**
- Modify: `engine/crates/pg/src/query/users.rs:117-145`
- Test: `engine/crates/pg/tests/paid_researcher_queries.rs`

- [ ] **Step 1: Write failing tests for `try_decrement_research_credits_n`**

Append to `engine/crates/pg/tests/paid_researcher_queries.rs`:

```rust
#[tokio::test]
async fn try_decrement_n_succeeds_when_remaining_ge_n() {
    let (db, _c) = test_pg().await;
    let owner = create_user(&db).await;
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = 5 WHERE id = $1",
        [owner.into()],
    ))
    .await
    .unwrap();

    let r = u::try_decrement_research_credits_n(&db, owner, 3).await.unwrap();
    assert_eq!(r, Some(2)); // returns new remaining
}

#[tokio::test]
async fn try_decrement_n_fails_when_remaining_lt_n() {
    let (db, _c) = test_pg().await;
    let owner = create_user(&db).await;
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = 2 WHERE id = $1",
        [owner.into()],
    ))
    .await
    .unwrap();

    let r = u::try_decrement_research_credits_n(&db, owner, 3).await.unwrap();
    assert_eq!(r, None);
    // ledger untouched
    let m = nasrudin_pg::entity::users::Entity::find_by_id(owner)
        .one(&db).await.unwrap().unwrap();
    assert_eq!(m.research_credits, 2);
}

#[tokio::test]
async fn try_decrement_n_zero_request_is_a_noop_returning_current() {
    // Defensive: n=0 should be allowed and report current remaining
    // without changing it. Saves a branch in the caller.
    let (db, _c) = test_pg().await;
    let owner = create_user(&db).await;
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = 4 WHERE id = $1",
        [owner.into()],
    ))
    .await
    .unwrap();

    let r = u::try_decrement_research_credits_n(&db, owner, 0).await.unwrap();
    assert_eq!(r, Some(4));
}
```

- [ ] **Step 2: Run the new tests, expect failure**

Run: `cargo test -p nasrudin-pg --test paid_researcher_queries try_decrement_n`
Expected: FAIL — function does not exist.

- [ ] **Step 3: Implement `try_decrement_research_credits_n`**

In `engine/crates/pg/src/query/users.rs`, replace lines 112–129 with:

```rust
/// Atomic multi-credit decrement for the paid Researcher tier.
/// Returns `Some(new_remaining)` when the predicate `research_credits >= n`
/// holds and the row was updated; `None` when the user can't afford `n`.
/// The `WHERE research_credits >= $n` clause makes this safe under
/// concurrent submission attempts — only one wins.
///
/// `n = 0` is allowed: returns the current value without modifying it,
/// so callers can read-without-decrementing if they want.
pub async fn try_decrement_research_credits_n(
    db: &impl ConnectionTrait,
    user_id: Uuid,
    n: i32,
) -> Result<Option<i32>, DbErr> {
    if n == 0 {
        // Pure read path — keep the same return shape.
        let m = crate::entity::users::Entity::find_by_id(user_id)
            .one(db)
            .await?;
        return Ok(m.map(|u| u.research_credits));
    }
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = research_credits - $2 \
         WHERE id = $1 AND research_credits >= $2 \
         RETURNING research_credits",
        [user_id.into(), n.into()],
    );
    let row = db.query_one(stmt).await?;
    let Some(row) = row else { return Ok(None) };
    Ok(Some(row.try_get_by_index::<i32>(0)?))
}

/// Single-credit wrapper. Kept for backward compatibility with callers
/// that haven't been ported to the multi-credit path; equivalent to
/// `try_decrement_research_credits_n(db, user_id, 1).map(|x| x.is_some())`.
pub async fn try_decrement_research_credits(
    db: &impl ConnectionTrait,
    user_id: Uuid,
) -> Result<bool, DbErr> {
    Ok(try_decrement_research_credits_n(db, user_id, 1)
        .await?
        .is_some())
}
```

Note the trait change: `&impl ConnectionTrait` instead of `&DatabaseConnection`. This lets the function take either a connection or a transaction handle — required for Task 6 (submit handler runs it inside `pg.begin()`). If existing callers pass `&DatabaseConnection`, that still satisfies `ConnectionTrait`, so no caller-side changes are needed.

Add to the imports at the top of `users.rs` if not already present:

```rust
use sea_orm::{ConnectionTrait, DatabaseBackend, DbErr, Statement};
```

- [ ] **Step 4: Run the new tests, expect pass**

Run: `cargo test -p nasrudin-pg --test paid_researcher_queries try_decrement`
Expected: PASS for both `_n` tests AND the existing `try_decrement_research_credits_zero_returns_false` and `try_decrement_research_credits_one_returns_true_then_zero` — the wrapper preserves their behavior.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/query/users.rs engine/crates/pg/tests/paid_researcher_queries.rs
git commit -m "pg: try_decrement_research_credits_n — multi-credit atomic decrement

Generalises the existing single-credit helper. Takes &impl ConnectionTrait
so callers can run it inside a transaction. Returns Option<new_remaining>
so 402 responses can echo the fresh remaining count back to the client."
```

---

## Task 3: Add multi-credit refund helper

**Files:**
- Modify: `engine/crates/pg/src/query/users.rs:131-145`
- Test: `engine/crates/pg/tests/paid_researcher_queries.rs`

- [ ] **Step 1: Write failing test**

```rust
#[tokio::test]
async fn refund_research_credits_n_increments() {
    let (db, _c) = test_pg().await;
    let owner = create_user(&db).await;
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = 1 WHERE id = $1",
        [owner.into()],
    ))
    .await
    .unwrap();

    let _ = u::refund_research_credits_n(&db, owner, 4).await.unwrap();
    let m = nasrudin_pg::entity::users::Entity::find_by_id(owner)
        .one(&db).await.unwrap().unwrap();
    assert_eq!(m.research_credits, 5);
}

#[tokio::test]
async fn refund_research_credits_n_zero_is_noop() {
    let (db, _c) = test_pg().await;
    let owner = create_user(&db).await;
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = 3 WHERE id = $1",
        [owner.into()],
    ))
    .await
    .unwrap();

    let _ = u::refund_research_credits_n(&db, owner, 0).await.unwrap();
    let m = nasrudin_pg::entity::users::Entity::find_by_id(owner)
        .one(&db).await.unwrap().unwrap();
    assert_eq!(m.research_credits, 3);
}
```

- [ ] **Step 2: Run, expect failure**

Run: `cargo test -p nasrudin-pg --test paid_researcher_queries refund_research_credits_n`
Expected: FAIL — function not defined.

- [ ] **Step 3: Implement**

Replace the existing `refund_research_credit` (engine/crates/pg/src/query/users.rs:131-145) with:

```rust
/// Multi-credit refund for the paid Researcher tier. No bound check —
/// refunds are privileged operations the caller has already justified
/// (cancel-with-no-progress, transaction-rollback path, etc).
///
/// `n = 0` is a no-op (returns 0 rows affected) so it's safe to call
/// unconditionally on cancel paths.
pub async fn refund_research_credits_n(
    db: &impl ConnectionTrait,
    user_id: Uuid,
    n: i32,
) -> Result<u64, DbErr> {
    if n <= 0 {
        return Ok(0);
    }
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = research_credits + $2 WHERE id = $1",
        [user_id.into(), n.into()],
    );
    let r = db.execute(stmt).await?;
    Ok(r.rows_affected())
}

/// Single-credit wrapper. Kept for backward compatibility.
pub async fn refund_research_credit(
    db: &impl ConnectionTrait,
    user_id: Uuid,
) -> Result<u64, DbErr> {
    refund_research_credits_n(db, user_id, 1).await
}
```

- [ ] **Step 4: Run, expect pass**

Run: `cargo test -p nasrudin-pg --test paid_researcher_queries refund_research_credit`
Expected: PASS for both new tests AND any existing tests of the single-credit version.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/query/users.rs engine/crates/pg/tests/paid_researcher_queries.rs
git commit -m "pg: refund_research_credits_n — multi-credit refund helper

Generalises the existing single-credit refund. n=0 is an explicit no-op
so cancel paths can call it unconditionally."
```

---

## Task 4: Fix heartbeat to no-op on terminal rows (regression for cancel race)

**Files:**
- Modify: `engine/crates/pg/src/query/conjecture_jobs.rs:454-470` (the heartbeat UPDATE)
- Test: `engine/crates/pg/tests/paid_researcher_queries.rs`

- [ ] **Step 1: Write failing regression test**

A heartbeat that lands after the row has been cancelled must not modify the row. Today's heartbeat would happily reset state to `'running'` and bump consumed.

```rust
#[tokio::test]
async fn heartbeat_after_cancel_is_a_noop() {
    let (db, _c) = test_pg().await;
    let (job_id, owner, worker) = setup_claimed_job(&db).await; // existing helper
    // Mark the row cancelled directly (simulating the cancel transaction
    // having terminalized the row before this stale heartbeat lands).
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE conjecture_jobs SET state = 'cancelled' WHERE id = $1",
        [job_id.into()],
    ))
    .await
    .unwrap();
    let before = nasrudin_pg::entity::conjecture_jobs::Entity::find_by_id(job_id)
        .one(&db).await.unwrap().unwrap();

    // Stale heartbeat from the same worker — must be ignored.
    let r = nasrudin_pg::query::conjecture_jobs::heartbeat_paid(
        &db, job_id, &worker, /* attempted */ 100, /* verified */ 0, /* delta_h */ 1.0,
    )
    .await
    .unwrap();
    // Old behavior: returns Some(...) and updates the row.
    // New behavior: returns None (row not eligible), no row mutation.
    assert!(r.is_none(), "heartbeat must be ignored when row is terminal");

    let after = nasrudin_pg::entity::conjecture_jobs::Entity::find_by_id(job_id)
        .one(&db).await.unwrap().unwrap();
    assert_eq!(after.state, "cancelled");
    assert_eq!(after.lake_slot_hours_consumed, before.lake_slot_hours_consumed);
    assert_eq!(after.candidates_attempted, before.candidates_attempted);
}
```

If `setup_claimed_job` doesn't exist, write it minimally:

```rust
async fn setup_claimed_job(db: &DatabaseConnection) -> (Uuid, Uuid, String) {
    let owner = create_user(db).await;
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = 5 WHERE id = $1",
        [owner.into()],
    )).await.unwrap();
    let job_id = nasrudin_pg::query::conjecture_jobs::create(
        db,
        nasrudin_pg::query::conjecture_jobs::CreateInput {
            owner_id: owner,
            hunch: "test".into(),
            domain_hint: None,
            provider: "internal".into(),
            model: "ga".into(),
            budget: serde_json::json!({}),
        },
    ).await.unwrap();
    let worker = "worker-test".to_string();
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE conjecture_jobs SET state='claimed', claimed_by=$2, allocated_slots=4, \
         lake_slot_hours_quota=96, last_heartbeat_at=NOW() WHERE id=$1",
        [job_id.into(), worker.clone().into()],
    )).await.unwrap();
    (job_id, owner, worker)
}
```

- [ ] **Step 2: Run, expect failure**

Run: `cargo test -p nasrudin-pg --test paid_researcher_queries heartbeat_after_cancel`
Expected: FAIL — heartbeat happily updates the cancelled row.

- [ ] **Step 3: Add state guard to `heartbeat_paid`**

In `engine/crates/pg/src/query/conjecture_jobs.rs:423-475`, modify the function:

1. Change the early `get_by_id` filter to also reject terminal rows:

```rust
pub async fn heartbeat_paid(
    db: &DatabaseConnection,
    id: Uuid,
    worker_id: &str,
    cand_attempted_delta: i32,
    cand_verified_delta: i32,
    consumed_delta_requested: f32,
) -> Result<Option<(f32, bool)>, DbErr> {
    let job = match get_by_id(db, id).await? {
        Some(j) => j,
        None => return Ok(None),
    };
    if job.claimed_by.as_deref() != Some(worker_id) {
        return Ok(None);
    }
    // Heartbeats are only valid while the row is in the active band.
    // Cancellation, budget exhaustion, and proved transitions all set
    // a terminal state — a late heartbeat must not reset state to
    // 'running' or eat more quota.
    if !matches!(job.state.as_str(), "claimed" | "running") {
        return Ok(None);
    }
    // ... rest unchanged: sanity cap, compute new_consumed, exhausted ...
```

2. Add the same guard to the UPDATE's WHERE so a row that flips to terminal *between* the SELECT and the UPDATE is also caught:

```rust
let stmt = Statement::from_sql_and_values(
    DatabaseBackend::Postgres,
    r#"UPDATE conjecture_jobs SET
        last_heartbeat_at = NOW(),
        lease_expires_at = NOW() + INTERVAL '5 minutes',
        state = 'running',
        candidates_attempted = candidates_attempted + $2,
        candidates_verified = candidates_verified + $3,
        lake_slot_hours_consumed = lake_slot_hours_consumed + $4
       WHERE id = $1
         AND claimed_by = $5
         AND state IN ('claimed', 'running')"#,
    [
        id.into(),
        cand_attempted_delta.into(),
        cand_verified_delta.into(),
        consumed_delta.into(),
        worker_id.into(),
    ],
);
```

If `r.rows_affected() == 0` after the execute (because the row terminalised between read and write), return `Ok(None)` — same as the early-return shape.

- [ ] **Step 4: Run, expect pass**

Run: `cargo test -p nasrudin-pg --test paid_researcher_queries heartbeat`
Expected: PASS for the new test plus existing heartbeat tests (the guard is additive — claimed/running rows still update).

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/query/conjecture_jobs.rs engine/crates/pg/tests/paid_researcher_queries.rs
git commit -m "pg: heartbeat_paid no-ops on terminal rows

Required prerequisite for the cancel-with-refund transaction (next
commit). Without this guard, a late heartbeat from the same worker
would reset state to 'running' and bump lake_slot_hours_consumed
after the cancel transaction had committed."
```

---

## Task 5: Add `cancel_paid_with_refund` query

**Files:**
- Modify: `engine/crates/pg/src/query/conjecture_jobs.rs` (add new function near `release_paid_claim`)
- Test: `engine/crates/pg/tests/paid_researcher_queries.rs`

- [ ] **Step 1: Write failing tests covering the refund matrix**

```rust
/// Helper to create a queued/running job with given quota and consumed.
async fn setup_job_for_cancel(
    db: &DatabaseConnection,
    state: &str,
    quota: i32,
    consumed: f32,
    verified: i32,
    rush: bool,
) -> (Uuid, Uuid /*owner*/, i32 /*credits_before*/) {
    let owner = create_user(db).await;
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = 0 WHERE id = $1",
        [owner.into()],
    )).await.unwrap();
    let job_id = Uuid::new_v4();
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "INSERT INTO conjecture_jobs \
            (id, owner_id, state, hunch, provider, model, budget, \
             candidates_attempted, candidates_verified, created_at, \
             lake_slot_hours_quota, lake_slot_hours_consumed, slice_priority, \
             tier, allocated_slots) \
         VALUES ($1, $2, $3, 'hunch', 'internal', 'ga', '{}', 0, $4, NOW(), \
                 $5, $6, $7, 'researcher', 4)",
        [
            job_id.into(),
            owner.into(),
            state.into(),
            verified.into(),
            quota.into(),
            consumed.into(),
            (if rush { 6i32 } else { 5i32 }).into(),
        ],
    )).await.unwrap();
    (job_id, owner, 0)
}

#[tokio::test]
async fn cancel_with_refund_running_job_marks_was_in_flight_true() {
    // 5-credit job (480 quota), 192 consumed (40%), no verified.
    // Refund = floor(5 * (1 - 192/480)) = floor(5 * 0.6) = 3.
    let (db, _c) = test_pg().await;
    let (job, owner, _) =
        setup_job_for_cancel(&db, "running", 480, 192.0, 0, false).await;

    let r = q::cancel_paid_with_refund(&db, job, owner).await.unwrap();
    assert!(r.row_was_cancelled);
    assert!(r.was_in_flight, "running state must report was_in_flight");
    assert_eq!(r.refunded_credits, 3);
    assert_eq!(r.allocated_slots, 4);

    let user = nasrudin_pg::entity::users::Entity::find_by_id(owner)
        .one(&db).await.unwrap().unwrap();
    assert_eq!(user.research_credits, 3);

    let row = q::get_by_id(&db, job).await.unwrap().unwrap();
    assert_eq!(row.state, "cancelled");
    assert!(row.completed_at.is_some());
}

#[tokio::test]
async fn cancel_with_refund_queued_job_marks_was_in_flight_false() {
    // Critical: a queued job never reserved cluster capacity, so the
    // caller must NOT release_paid_slots(...). Prove was_in_flight is
    // false in this case so the handler can branch correctly.
    let (db, _c) = test_pg().await;
    let (job, owner, _) =
        setup_job_for_cancel(&db, "queued", 480, 0.0, 0, false).await;

    let r = q::cancel_paid_with_refund(&db, job, owner).await.unwrap();
    assert!(r.row_was_cancelled);
    assert!(!r.was_in_flight, "queued state must report was_in_flight=false");
    assert_eq!(r.refunded_credits, 5);
}

#[tokio::test]
async fn cancel_with_refund_claimed_job_marks_was_in_flight_true() {
    // claimed (post-claim, pre-first-heartbeat) is still a state that
    // reserved cluster capacity. Treated like running.
    let (db, _c) = test_pg().await;
    let (job, owner, _) =
        setup_job_for_cancel(&db, "claimed", 96, 0.0, 0, false).await;

    let r = q::cancel_paid_with_refund(&db, job, owner).await.unwrap();
    assert!(r.was_in_flight);
}

#[tokio::test]
async fn cancel_with_refund_with_rush_includes_rush_credit() {
    // 3-credit budget + 1 rush = 4 spent. quota=288, consumed=0.
    let (db, _c) = test_pg().await;
    let (job, owner, _) =
        setup_job_for_cancel(&db, "queued", 288, 0.0, 0, true).await;

    let r = q::cancel_paid_with_refund(&db, job, owner).await.unwrap();
    assert_eq!(r.refunded_credits, 4);
}

#[tokio::test]
async fn cancel_with_refund_verified_gives_zero() {
    // Even with 0 consumed, any verified theorem disables refund.
    let (db, _c) = test_pg().await;
    let (job, owner, _) =
        setup_job_for_cancel(&db, "running", 480, 100.0, 1, false).await;

    let r = q::cancel_paid_with_refund(&db, job, owner).await.unwrap();
    assert_eq!(r.refunded_credits, 0);
}

#[tokio::test]
async fn cancel_with_refund_consumed_overshoot_clamps_to_zero() {
    // Lying worker pushed consumed past quota. (1 - consumed/quota) < 0
    // must clamp; refund must not be negative.
    let (db, _c) = test_pg().await;
    let (job, owner, _) =
        setup_job_for_cancel(&db, "running", 96, 200.0, 0, false).await;

    let r = q::cancel_paid_with_refund(&db, job, owner).await.unwrap();
    assert_eq!(r.refunded_credits, 0);
}

#[tokio::test]
async fn cancel_with_refund_already_terminal_returns_none() {
    let (db, _c) = test_pg().await;
    let (job, owner, _) =
        setup_job_for_cancel(&db, "proved", 96, 50.0, 1, false).await;

    let r = q::cancel_paid_with_refund(&db, job, owner).await.unwrap();
    assert!(!r.row_was_cancelled);
    assert!(!r.was_in_flight);
    let user = nasrudin_pg::entity::users::Entity::find_by_id(owner)
        .one(&db).await.unwrap().unwrap();
    assert_eq!(user.research_credits, 0); // no refund applied
}

#[tokio::test]
async fn cancel_with_refund_wrong_owner_returns_none() {
    let (db, _c) = test_pg().await;
    let (job, _owner, _) =
        setup_job_for_cancel(&db, "queued", 96, 0.0, 0, false).await;
    let other = create_user(&db).await;

    let r = q::cancel_paid_with_refund(&db, job, other).await.unwrap();
    assert!(!r.row_was_cancelled);
    assert!(!r.was_in_flight);
}

#[tokio::test]
async fn cancel_with_refund_is_idempotent_under_double_call() {
    let (db, _c) = test_pg().await;
    let (job, owner, _) =
        setup_job_for_cancel(&db, "queued", 480, 0.0, 0, false).await;

    let r1 = q::cancel_paid_with_refund(&db, job, owner).await.unwrap();
    let r2 = q::cancel_paid_with_refund(&db, job, owner).await.unwrap();

    assert!(r1.row_was_cancelled);
    assert_eq!(r1.refunded_credits, 5);
    assert!(!r2.row_was_cancelled, "second call must be a no-op");
    assert_eq!(r2.refunded_credits, 0);

    let user = nasrudin_pg::entity::users::Entity::find_by_id(owner)
        .one(&db).await.unwrap().unwrap();
    assert_eq!(user.research_credits, 5, "credits applied exactly once");
}
```

- [ ] **Step 2: Run, expect failure**

Run: `cargo test -p nasrudin-pg --test paid_researcher_queries cancel_with_refund`
Expected: FAIL — `cancel_paid_with_refund` doesn't exist.

- [ ] **Step 3: Implement `cancel_paid_with_refund`**

Add to `engine/crates/pg/src/query/conjecture_jobs.rs` after `release_paid_claim`:

```rust
/// Result of `cancel_paid_with_refund`.
#[derive(Debug, Clone)]
pub struct CancelOutcome {
    /// True iff the conditional UPDATE actually transitioned the row.
    /// Idempotent against double-clicks: the second call sees this as
    /// false and applies no refund.
    pub row_was_cancelled: bool,
    /// Credits returned to the user. 0 if `row_was_cancelled` is false
    /// or if any theorem was verified.
    pub refunded_credits: i32,
    /// True iff the row's prior state was `claimed` or `running`. The
    /// caller uses this to decide whether to release in-memory cluster
    /// capacity — for a `queued` cancel no slots were ever reserved.
    pub was_in_flight: bool,
    /// `allocated_slots` value the row carried at cancel time. Only
    /// meaningful when `was_in_flight == true`.
    pub allocated_slots: i32,
}

/// Atomically cancel a paid Researcher job and refund the user
/// proportionally to the unused budget. Single transaction:
///   1. SELECT ... FOR UPDATE to lock the row and capture its prior
///      state (we need pre-cancel state to decide whether the job was
///      in-flight; the UPDATE's RETURNING shows post-update values).
///   2. Bail if the row doesn't exist, the owner mismatches, or the
///      state is already terminal.
///   3. UPDATE state→'cancelled', clear claim columns; RETURNING gives
///      us quota/consumed/verified/priority for the refund calc.
///   4. If verified == 0, increment users.research_credits by
///      floor(credits_spent × max(0, 1 - consumed/quota)).
/// `credits_spent` is reconstructed from the row:
///   credits_spent = (lake_slot_hours_quota / 96)
///                 + (slice_priority > 5 ? 1 : 0)
pub async fn cancel_paid_with_refund(
    db: &DatabaseConnection,
    job_id: Uuid,
    owner_id: Uuid,
) -> Result<CancelOutcome, DbErr> {
    let txn = db.begin().await?;

    // Step 1: lock + snapshot prior state. FOR UPDATE serialises
    // concurrent heartbeats and double-cancel attempts behind us.
    let lock_stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        SELECT state, allocated_slots
          FROM conjecture_jobs
         WHERE id = $1 AND owner_id = $2
         FOR UPDATE
        "#,
        [job_id.into(), owner_id.into()],
    );
    let lock_row = txn.query_one(lock_stmt).await?;
    let Some(lock_row) = lock_row else {
        // Row doesn't exist or owner mismatched.
        txn.rollback().await?;
        return Ok(CancelOutcome {
            row_was_cancelled: false,
            refunded_credits: 0,
            was_in_flight: false,
            allocated_slots: 0,
        });
    };
    let prior_state: String = lock_row.try_get_by_index(0)?;
    let allocated_slots: i32 = lock_row.try_get_by_index(1)?;
    if !matches!(prior_state.as_str(), "queued" | "claimed" | "running") {
        // Already terminal — nothing to do.
        txn.rollback().await?;
        return Ok(CancelOutcome {
            row_was_cancelled: false,
            refunded_credits: 0,
            was_in_flight: false,
            allocated_slots: 0,
        });
    }
    let was_in_flight = matches!(prior_state.as_str(), "claimed" | "running");

    // Step 2: terminal transition + refund-amount calc in one statement.
    let cancel_stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs
           SET state = 'cancelled',
               completed_at = NOW(),
               claimed_by = NULL,
               claimed_at = NULL,
               lease_expires_at = NULL
         WHERE id = $1
        RETURNING
            CASE
                WHEN candidates_verified = 0 THEN
                  FLOOR(
                    ((lake_slot_hours_quota / 96)
                     + CASE WHEN slice_priority > 5 THEN 1 ELSE 0 END)::float
                    * GREATEST(0.0, 1.0 - (lake_slot_hours_consumed / lake_slot_hours_quota::float))
                  )::int
                ELSE 0
            END AS refund_credits
        "#,
        [job_id.into()],
    );
    let row = txn.query_one(cancel_stmt).await?
        .ok_or_else(|| DbErr::Custom(
            "cancel_paid_with_refund: row vanished between SELECT FOR UPDATE and UPDATE".into()
        ))?;
    let refund: i32 = row.try_get_by_index(0)?;

    // Step 3: apply refund (no-op when refund == 0).
    if refund > 0 {
        crate::query::users::refund_research_credits_n(&txn, owner_id, refund).await?;
    }

    txn.commit().await?;

    Ok(CancelOutcome {
        row_was_cancelled: true,
        refunded_credits: refund,
        was_in_flight,
        allocated_slots,
    })
}
```

- [ ] **Step 4: Run, expect pass**

Run: `cargo test -p nasrudin-pg --test paid_researcher_queries cancel_with_refund`
Expected: PASS for all eight tests.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/query/conjecture_jobs.rs engine/crates/pg/tests/paid_researcher_queries.rs
git commit -m "pg: cancel_paid_with_refund — atomic cancel + proportional refund

Single transaction: conditional UPDATE on state+owner, then refund
based on (1 - consumed/quota). Idempotent against double-clicks
because the conditional WHERE only fires once. Heartbeat race closed
by the prior commit's state guard on heartbeat_paid."
```

---

## Task 6: Submit handler — `credits_budget` + `rush` + transactional decrement+insert

**Files:**
- Modify: `engine/crates/api/src/handlers/research_jobs.rs:44-137`
- Test: new file `engine/crates/api/tests/research_jobs_submit.rs`

- [ ] **Step 1: Find or scaffold the API integration test harness**

Run: `ls engine/crates/api/tests/ && grep -l "fn test_app\|build_app\|axum::Router" engine/crates/api/tests/*.rs 2>/dev/null | head -3`

If a harness exists (e.g. `common.rs` or `helpers.rs`), reuse it. If not, copy the pattern from any existing integration test in that directory.

- [ ] **Step 2: Write failing tests covering the new submit semantics**

In `engine/crates/api/tests/research_jobs_submit.rs`:

```rust
use axum::http::StatusCode;
use serde_json::json;
// ... use whichever test helpers already exist in the crate.
// The pattern below assumes `app_with_user(credits)` returns
// (test app, user_id, signed-in cookie) — adapt to actual helpers.

#[tokio::test]
async fn submit_defaults_to_one_credit_and_priority_5() {
    let (app, _user, cookie) = app_with_user(3).await;
    let resp = post_json(&app, "/api/research/jobs", &cookie, json!({
        "hunch": "E = m c^2",
    })).await;
    assert_eq!(resp.status, StatusCode::CREATED);
    let job_id = resp.body["job_id"].as_str().unwrap().to_string();

    let row = job_row(&app, &job_id).await;
    assert_eq!(row.lake_slot_hours_quota, 96);
    assert_eq!(row.slice_priority, 5);
    let me_after = me_credits(&app, &cookie).await;
    assert_eq!(me_after, 2);
}

#[tokio::test]
async fn submit_with_credits_budget_3_sets_quota_288() {
    let (app, _user, cookie) = app_with_user(5).await;
    let resp = post_json(&app, "/api/research/jobs", &cookie, json!({
        "hunch": "test",
        "credits_budget": 3,
    })).await;
    assert_eq!(resp.status, StatusCode::CREATED);
    let row = job_row(&app, resp.body["job_id"].as_str().unwrap()).await;
    assert_eq!(row.lake_slot_hours_quota, 288);
    assert_eq!(row.slice_priority, 5);
    assert_eq!(me_credits(&app, &cookie).await, 2);
}

#[tokio::test]
async fn submit_with_rush_charges_extra_credit_and_priority_6() {
    let (app, _user, cookie) = app_with_user(5).await;
    let resp = post_json(&app, "/api/research/jobs", &cookie, json!({
        "hunch": "test",
        "credits_budget": 2,
        "rush": true,
    })).await;
    assert_eq!(resp.status, StatusCode::CREATED);
    let row = job_row(&app, resp.body["job_id"].as_str().unwrap()).await;
    assert_eq!(row.lake_slot_hours_quota, 192);
    assert_eq!(row.slice_priority, 6);
    assert_eq!(me_credits(&app, &cookie).await, 2); // 5 - 3 = 2
}

#[tokio::test]
async fn submit_with_zero_credits_budget_is_400() {
    let (app, _user, cookie) = app_with_user(5).await;
    let resp = post_json(&app, "/api/research/jobs", &cookie, json!({
        "hunch": "test",
        "credits_budget": 0,
    })).await;
    assert_eq!(resp.status, StatusCode::BAD_REQUEST);
    assert_eq!(resp.body["error"], "invalid_credits_budget");
    assert_eq!(me_credits(&app, &cookie).await, 5);
}

#[tokio::test]
async fn submit_402_when_insufficient_credits_with_required_remaining_body() {
    let (app, _user, cookie) = app_with_user(2).await;
    let resp = post_json(&app, "/api/research/jobs", &cookie, json!({
        "hunch": "test",
        "credits_budget": 5,
    })).await;
    assert_eq!(resp.status, StatusCode::PAYMENT_REQUIRED);
    assert_eq!(resp.body["error"], "insufficient_research_credits");
    assert_eq!(resp.body["required"], 5);
    assert_eq!(resp.body["remaining"], 2);
    assert_eq!(me_credits(&app, &cookie).await, 2); // untouched
}

#[tokio::test]
async fn submit_402_when_rush_pushes_total_over_remaining() {
    let (app, _user, cookie) = app_with_user(1).await;
    // 1 budget + 1 rush = 2 needed, only 1 remaining.
    let resp = post_json(&app, "/api/research/jobs", &cookie, json!({
        "hunch": "test",
        "credits_budget": 1,
        "rush": true,
    })).await;
    assert_eq!(resp.status, StatusCode::PAYMENT_REQUIRED);
    assert_eq!(resp.body["required"], 2);
    assert_eq!(resp.body["remaining"], 1);
}

#[tokio::test]
async fn submit_with_empty_hunch_400_does_not_decrement() {
    let (app, _user, cookie) = app_with_user(5).await;
    let resp = post_json(&app, "/api/research/jobs", &cookie, json!({
        "hunch": "   ",
        "credits_budget": 3,
    })).await;
    assert_eq!(resp.status, StatusCode::BAD_REQUEST);
    assert_eq!(me_credits(&app, &cookie).await, 5);
}
```

- [ ] **Step 3: Run, expect failure**

Run: `cargo test -p physics_api --test research_jobs_submit`
Expected: FAIL across the board — handler still hardcodes 96/5/1-credit and the new fields aren't read.

- [ ] **Step 4: Rewrite the `create` handler**

Replace `engine/crates/api/src/handlers/research_jobs.rs:44-137` with:

```rust
#[derive(Deserialize)]
pub struct CreateBody {
    pub hunch: String,
    #[serde(default)]
    pub domain_hint: Option<String>,
    /// Number of credits worth of cluster compute the user wants to
    /// spend (1 credit = 96 lake-slot-hours). Default 1 reproduces
    /// the legacy single-credit behavior.
    #[serde(default = "default_credits_budget")]
    pub credits_budget: i32,
    /// When true, costs +1 credit and bumps slice_priority to 6 so the
    /// job claims ahead of normal-priority work.
    #[serde(default)]
    pub rush: bool,
}

fn default_credits_budget() -> i32 { 1 }

/// `POST /api/research/jobs` — atomically debit `credits_budget + (rush ? 1 : 0)`
/// research_credits and queue a paid conjecture, both inside one transaction.
pub async fn create(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Json(body): Json<CreateBody>,
) -> impl IntoResponse {
    if body.hunch.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "hunch_required" })),
        )
            .into_response();
    }
    if body.credits_budget < 1 {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "invalid_credits_budget" })),
        )
            .into_response();
    }
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    let user_id = auth.user.id;
    let total_cost: i32 = body.credits_budget + if body.rush { 1 } else { 0 };
    let quota: i32 = 96 * body.credits_budget;
    let priority: i32 = 5 + if body.rush { 1 } else { 0 };

    use nasrudin_pg::sea_orm::*;
    let txn = match pg.begin().await {
        Ok(t) => t,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };

    // Atomic decrement-or-bail. Returns Some(new_remaining) on success.
    let decrement = nasrudin_pg::query::users::try_decrement_research_credits_n(
        &txn,
        user_id,
        total_cost,
    )
    .await;
    let new_remaining = match decrement {
        Ok(Some(r)) => r,
        Ok(None) => {
            // Read fresh remaining for the 402 body, then rollback.
            let remaining = nasrudin_pg::query::users::try_decrement_research_credits_n(
                &txn, user_id, 0,
            )
            .await
            .unwrap_or(Some(0))
            .unwrap_or(0);
            let _ = txn.rollback().await;
            return (
                StatusCode::PAYMENT_REQUIRED,
                Json(serde_json::json!({
                    "error": "insufficient_research_credits",
                    "required": total_cost,
                    "remaining": remaining,
                })),
            )
                .into_response();
        }
        Err(e) => {
            let _ = txn.rollback().await;
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };

    let id = Uuid::new_v4();
    let am = nasrudin_pg::entity::conjecture_jobs::ActiveModel {
        id: Set(id),
        owner_id: Set(user_id),
        state: Set("queued".into()),
        outcome: Set(None),
        hunch: Set(body.hunch),
        domain_hint: Set(body.domain_hint),
        provider: Set("internal".into()),
        model: Set("ga".into()),
        suggestions: Set(None),
        chosen_index: Set(None),
        seed: Set(None),
        budget: Set(serde_json::json!({
            "wall_seconds": 86400,
            "max_candidates": 10_000_000,
        })),
        claimed_by: Set(None),
        claimed_at: Set(None),
        lease_expires_at: Set(None),
        last_heartbeat_at: Set(None),
        candidates_attempted: Set(0),
        candidates_verified: Set(0),
        verified_theorem_ids: Set(None),
        created_at: Set(chrono::Utc::now().into()),
        completed_at: Set(None),
        paper_draft: Set(None),
        lake_slot_hours_quota: Set(quota),
        lake_slot_hours_consumed: Set(0.0),
        slice_priority: Set(priority),
        tier: Set("researcher".into()),
        // Default 4 — `atomic_claim_paid` overwrites this with the
        // claiming worker's reported available_lake_slots.
        allocated_slots: Set(4),
    };
    if let Err(e) = am.insert(&txn).await {
        // Transaction rollback automatically restores the credits.
        let _ = txn.rollback().await;
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response();
    }
    if let Err(e) = txn.commit().await {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response();
    }

    tracing::info!(
        user = %user_id,
        job = %id,
        credits = total_cost,
        budget = body.credits_budget,
        rush = body.rush,
        remaining = new_remaining,
        "submit_decremented",
    );

    (
        StatusCode::CREATED,
        Json(serde_json::json!({
            "job_id": id,
            "state": "queued",
            "credits_spent": total_cost,
            "credits_remaining": new_remaining,
        })),
    )
        .into_response()
}
```

- [ ] **Step 5: Run the new test file, expect pass**

Run: `cargo test -p physics_api --test research_jobs_submit`
Expected: PASS for all submit tests.

- [ ] **Step 6: Run the wider api test suite to confirm no regressions**

Run: `cargo test -p physics_api`
Expected: PASS. Existing callers that POST `{hunch, domain_hint}` still get the 1-credit / 96-quota / priority-5 default behavior.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/handlers/research_jobs.rs engine/crates/api/tests/research_jobs_submit.rs
git commit -m "research_jobs: credits_budget + rush, transactional submit

Decrement and insert run inside a single pg transaction. On insert
failure the rollback automatically restores the credits — no
separate refund call needed. 402 response now carries
{required, remaining} so the frontend can resync without a
separate /api/me round-trip."
```

---

## Task 7: Cancel handler — call new query, return `refunded_credits`

**Files:**
- Modify: `engine/crates/api/src/handlers/research_jobs.rs:216-276` (the `cancel` fn)
- Modify: `engine/crates/api/src/jobs/mod.rs` — extend `JobEvent::Cancelled`
- Test: new file `engine/crates/api/tests/research_jobs_cancel.rs`

- [ ] **Step 1: Locate `JobEvent::Cancelled`**

Run: `grep -n "Cancelled" engine/crates/api/src/jobs/mod.rs engine/crates/api/src/jobs/*.rs`

- [ ] **Step 2: Write failing cancel tests**

```rust
// engine/crates/api/tests/research_jobs_cancel.rs

#[tokio::test]
async fn cancel_zero_consumed_full_refund() {
    let (app, _user, cookie) = app_with_user(5).await;
    let job = submit_job(&app, &cookie, 5, false).await;

    let resp = post(&app, &format!("/api/research/jobs/{}/cancel", job), &cookie).await;
    assert_eq!(resp.status, StatusCode::OK);
    assert_eq!(resp.body["cancelled"], true);
    assert_eq!(resp.body["refunded_credits"], 5);
    assert_eq!(me_credits(&app, &cookie).await, 5);
}

#[tokio::test]
async fn cancel_partial_consumed_proportional_refund() {
    let (app, user, cookie) = app_with_user(5).await;
    let job = submit_job(&app, &cookie, 5, false).await; // quota 480
    set_consumed(&app, &job, 192.0).await; // 40%

    let resp = post(&app, &format!("/api/research/jobs/{}/cancel", job), &cookie).await;
    assert_eq!(resp.status, StatusCode::OK);
    assert_eq!(resp.body["refunded_credits"], 3);
}

#[tokio::test]
async fn cancel_with_verified_no_refund() {
    let (app, user, cookie) = app_with_user(5).await;
    let job = submit_job(&app, &cookie, 5, false).await;
    set_verified(&app, &job, 1).await;

    let resp = post(&app, &format!("/api/research/jobs/{}/cancel", job), &cookie).await;
    assert_eq!(resp.status, StatusCode::OK);
    assert_eq!(resp.body["refunded_credits"], 0);
}

#[tokio::test]
async fn cancel_already_terminal_returns_409() {
    let (app, _user, cookie) = app_with_user(5).await;
    let job = submit_job(&app, &cookie, 1, false).await;
    let _ = post(&app, &format!("/api/research/jobs/{}/cancel", job), &cookie).await;

    let r2 = post(&app, &format!("/api/research/jobs/{}/cancel", job), &cookie).await;
    assert_eq!(r2.status, StatusCode::CONFLICT);
}

#[tokio::test]
async fn cancel_double_click_refunds_exactly_once() {
    let (app, _user, cookie) = app_with_user(5).await;
    let job = submit_job(&app, &cookie, 3, false).await;

    let (r1, r2) = tokio::join!(
        post(&app, &format!("/api/research/jobs/{}/cancel", job), &cookie),
        post(&app, &format!("/api/research/jobs/{}/cancel", job), &cookie),
    );
    let oks = [&r1, &r2].iter().filter(|r| r.status == StatusCode::OK).count();
    let conflicts = [&r1, &r2].iter().filter(|r| r.status == StatusCode::CONFLICT).count();
    assert_eq!(oks, 1);
    assert_eq!(conflicts, 1);
    assert_eq!(me_credits(&app, &cookie).await, 5); // 5 - 3 (debit) + 3 (refund)
}
```

- [ ] **Step 3: Run, expect failure**

Run: `cargo test -p physics_api --test research_jobs_cancel`
Expected: FAIL — current handler returns `refunded: bool`, doesn't gate on consumed/quota proportionally, etc.

- [ ] **Step 4: Extend `JobEvent::Cancelled`**

In `engine/crates/api/src/jobs/mod.rs` (or wherever the enum lives):

Find the `Cancelled` variant (something like `Cancelled,` or `Cancelled {}`) and replace with:

```rust
Cancelled {
    refunded_credits: i32,
},
```

Update any `match` arms that destructure `JobEvent::Cancelled` (compile errors will tell you where).

- [ ] **Step 5: Rewrite the `cancel` handler**

Replace `engine/crates/api/src/handlers/research_jobs.rs:216-276`:

```rust
/// `POST /api/research/jobs/{id}/cancel` — single-transaction terminal
/// transition + proportional refund. Idempotent: a second call after
/// the row is terminal returns 409.
pub async fn cancel(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };

    let outcome = match nasrudin_pg::query::conjecture_jobs::cancel_paid_with_refund(
        pg, id, auth.user.id,
    )
    .await
    {
        Ok(o) => o,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };

    if !outcome.row_was_cancelled {
        // Either the row was already terminal, doesn't exist, or the
        // owner mismatched. We can distinguish 404 vs 403 vs 409 with
        // a follow-up read, but for now collapse to 409 — the user
        // can refresh to see the current state.
        return (StatusCode::CONFLICT, Json(serde_json::json!({
            "error": "terminal_state",
        }))).into_response();
    }

    // Release in-memory cluster capacity outside the transaction —
    // ONLY for jobs that were actually in-flight. For a queued-then-
    // cancelled job, no slots were ever reserved, so calling
    // release_paid_slots(allocated) would credit phantom slots back
    // to the pool and inflate cluster capacity.
    if outcome.was_in_flight {
        let allocated = (outcome.allocated_slots as u32).max(1);
        state.capacity.release_paid_slots(allocated);
    }

    tracing::info!(
        user = %auth.user.id,
        job = %id,
        refund = outcome.refunded_credits,
        "cancel_refunded",
    );

    emit_job_event(
        &state,
        id,
        JobEvent::Cancelled {
            refunded_credits: outcome.refunded_credits,
        },
    );
    (
        StatusCode::OK,
        Json(serde_json::json!({
            "cancelled": true,
            "refunded_credits": outcome.refunded_credits,
        })),
    )
        .into_response()
}
```

- [ ] **Step 6: Run cancel tests, expect pass**

Run: `cargo test -p physics_api --test research_jobs_cancel`
Expected: PASS for all five tests.

- [ ] **Step 7: Run full api test suite**

Run: `cargo test -p physics_api`
Expected: PASS. Any consumer of `JobEvent::Cancelled` should already be fixed (compile errors in step 4 would have flagged them).

- [ ] **Step 8: Commit**

```bash
git add engine/crates/api/src/handlers/research_jobs.rs engine/crates/api/src/jobs/mod.rs engine/crates/api/tests/research_jobs_cancel.rs
git commit -m "research_jobs: transactional cancel with proportional refund

Cancel now goes through cancel_paid_with_refund (single PG transaction,
idempotent against double-clicks). Response carries refunded_credits.
JobEvent::Cancelled gains the refund amount so SSE subscribers see it
alongside the state change."
```

---

## Task 8: Frontend types — `AuthUser.research_credits`, `CreateResearchJobRequest`, cancel response, SSE event

**Files:**
- Modify: `nasrudin-frontend/src/lib/types.ts:112-118, 374-427`
- Modify: `nasrudin-frontend/src/lib/queries.ts:702-715` (cancel mutation type)

- [ ] **Step 1: Update `AuthUser`**

In `nasrudin-frontend/src/lib/types.ts`, replace the `AuthUser` interface (lines 112-118):

```ts
export interface AuthUser {
  id: string;
  email: string;
  display_name: string | null;
  created_at: string;
  firebase_uid: string;
  /** Lose-it-or-use-it Researcher-tier credits remaining this period. */
  research_credits: number;
}
```

- [ ] **Step 2: Update `CreateResearchJobRequest` and the response shape**

In `nasrudin-frontend/src/lib/types.ts`, replace `CreateResearchJobRequest` and `CreateResearchJobResponse`:

```ts
export interface CreateResearchJobRequest {
  hunch: string;
  domain_hint?: string | null;
  /** Number of credits to spend on cluster compute (default 1, each = 96 slot-h). */
  credits_budget?: number;
  /** When true, costs +1 credit and raises queue priority by 1. */
  rush?: boolean;
}

export interface CreateResearchJobResponse {
  job_id: string;
  state: string;
  credits_spent: number;
  credits_remaining: number;
}
```

- [ ] **Step 3: Update the `cancelled` SSE event variant**

In the same file, in the `ResearchJobEvent` union, replace `{ kind: 'cancelled' }` with:

```ts
| { kind: 'cancelled'; refunded_credits: number }
```

- [ ] **Step 4: Update the cancel mutation response type**

In `nasrudin-frontend/src/lib/queries.ts:702-715`, replace `useCancelResearchJob`:

```ts
export function useCancelResearchJob() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (id: string) =>
      apiFetch<{ cancelled: true; refunded_credits: number }>(
        `/api/research/jobs/${id}/cancel`,
        { method: 'POST' },
      ),
    onSuccess: (_data, id) => {
      qc.invalidateQueries({ queryKey: researchJobsQueryKey });
      qc.invalidateQueries({ queryKey: ['research-job', id] });
      qc.invalidateQueries({ queryKey: meQueryKey });
    },
  });
}
```

(Note: `qc.invalidateQueries({ queryKey: meQueryKey })` is a change from `meProfileQueryKey` — the credit balance lives on `/api/auth/me`, not `/api/me/profile`. Same change applies to `useCreateResearchJob`'s `onSuccess` block at line 695-699; update that too while you're here.)

In `useCreateResearchJob`'s `onSuccess`:

```ts
onSuccess: () => {
  qc.invalidateQueries({ queryKey: researchJobsQueryKey });
  qc.invalidateQueries({ queryKey: meQueryKey });
},
```

- [ ] **Step 5: Verify type-check**

Run: `cd nasrudin-frontend && pnpm type-check` (or `tsc --noEmit` — check `package.json` scripts for the actual command).
Expected: PASS, but compile errors may surface in `research.tsx` because we changed the cancel response shape (`refunded` → `refunded_credits`) and the `me.data?.research_credits` wasn't present before. The next task fixes those.

- [ ] **Step 6: Commit**

```bash
git add nasrudin-frontend/src/lib/types.ts nasrudin-frontend/src/lib/queries.ts
git commit -m "frontend: types for credits_budget/rush + research_credits + refunded_credits

Mirrors the backend changes from the prior commits. The next commit
wires these into the research page UI."
```

---

## Task 9: `NewJobForm` — slider + rush toggle + 402 cache update + clamp

**Files:**
- Modify: `nasrudin-frontend/src/routes/research.tsx:69-167`
- Test: `nasrudin-frontend/src/routes/research.test.tsx` (new — match existing test conventions; if no test setup exists for routes, we test via the `qa` skill flow at the end instead)

- [ ] **Step 1: Find existing test patterns**

Run: `find nasrudin-frontend/src -name "*.test.tsx" -o -name "*.test.ts" | head; cat nasrudin-frontend/package.json | grep -A2 '"test"'`

If route tests exist, follow that pattern. If they don't, skip the test file and rely on the type-check + manual QA (the `qa` skill is available; we'll invoke it at the end).

- [ ] **Step 2: Rewrite `NewJobForm`**

Replace `nasrudin-frontend/src/routes/research.tsx:69-167`:

```tsx
function NewJobForm() {
  const create = useCreateResearchJob();
  const navigate = useNavigate();
  const qc = useQueryClient();
  const me = useMe();
  const [hunch, setHunch] = useState('');
  const [domainHint, setDomainHint] = useState('');
  const [creditsBudget, setCreditsBudget] = useState(1);
  const [rush, setRush] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const remaining = me.data?.research_credits ?? 0;
  const totalCost = creditsBudget + (rush ? 1 : 0);
  const slotHours = creditsBudget * 96;

  // Re-clamp the slider when remaining drops or rush flips on/off.
  useEffect(() => {
    const cap = Math.max(1, remaining - (rush ? 1 : 0));
    if (creditsBudget > cap) setCreditsBudget(cap);
    if (rush && remaining < 2) setRush(false);
  }, [remaining, rush, creditsBudget]);

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    try {
      const res = await create.mutateAsync({
        hunch: hunch.trim(),
        domain_hint: domainHint.trim() || null,
        credits_budget: creditsBudget,
        rush,
      });
      navigate({ to: '/research/$id', params: { id: res.job_id } });
    } catch (e) {
      if (isApiError(e)) {
        if (
          e.status === 402 &&
          e.body &&
          typeof e.body === 'object' &&
          'remaining' in e.body
        ) {
          // Backend told us the truth — sync the cache so the slider
          // re-clamps via the useEffect above.
          const remaining = Number((e.body as { remaining: unknown }).remaining ?? 0);
          const required = Number((e.body as { required: unknown }).required ?? totalCost);
          qc.setQueryData(meQueryKey, (old: AuthUser | null | undefined) =>
            old ? { ...old, research_credits: remaining } : old,
          );
          setError(`Need ${required} credits, you have ${remaining}.`);
        } else if (e.body && typeof e.body === 'object' && 'error' in e.body) {
          setError(String((e.body as { error: unknown }).error));
        } else {
          setError(`Request failed (${e.status})`);
        }
      } else {
        setError('Network error');
      }
    }
  }

  const submitDisabled =
    create.isPending ||
    hunch.trim().length === 0 ||
    totalCost > remaining ||
    remaining === 0;

  return (
    <form onSubmit={onSubmit} style={{ maxWidth: 640, marginTop: 32 }}>
      <div className="field">
        <label htmlFor="hunch">Conjecture</label>
        <textarea
          id="hunch"
          value={hunch}
          onChange={(e) => setHunch(e.target.value)}
          rows={5}
          required
          placeholder="E = m c^2"
          style={{
            background: 'var(--bg-raised)',
            border: '1px solid var(--paper-200)',
            borderRadius: 'var(--radius-md)',
            padding: '12px 14px',
            fontFamily: 'var(--font-mono)',
            fontSize: 15,
            color: 'var(--ink-900)',
            resize: 'vertical',
          }}
        />
        <span className="hint">
          LaTeX preferred — the runner compiles it into a canonical-form hash and marks the job{' '}
          <code>proved</code> when a kernel-verified theorem matches. Plain English works too but
          disables exact-match checking; the runner falls back to "first kernel-verified theorem in
          the slice is the proof" and your refund eligibility depends on whether it produced any
          verified results.
        </span>
      </div>

      <div className="field">
        <label htmlFor="domain">Domain hint (optional)</label>
        <select id="domain" value={domainHint} onChange={(e) => setDomainHint(e.target.value)}>
          <option value="">—</option>
          <option value="special_relativity">Special Relativity</option>
          <option value="electromagnetism">Electromagnetism</option>
          <option value="classical_mechanics">Classical Mechanics</option>
          <option value="thermodynamics">Thermodynamics</option>
          <option value="quantum_mechanics">Quantum Mechanics</option>
          <option value="general_relativity">General Relativity</option>
          <option value="pure_math">Pure Math</option>
        </select>
        <span className="hint">
          Steers the explorer fleet's bias toward prerequisite lemmas in the relevant domain.
        </span>
      </div>

      {remaining === 0 ? (
        <div
          className="hint"
          style={{
            marginTop: 24,
            padding: 12,
            border: '1px solid var(--paper-200)',
            borderRadius: 'var(--radius-md)',
            background: 'var(--bg-raised)',
          }}
        >
          0 credits available. Wait for renewal or{' '}
          <a href="/pricing">upgrade your plan</a>.
        </div>
      ) : (
        <div className="field" style={{ marginTop: 24 }}>
          <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'baseline' }}>
            <label htmlFor="credits-budget">Effort</label>
            <span style={{ fontFamily: 'var(--font-mono)', fontSize: 13 }}>
              {creditsBudget} credit{creditsBudget === 1 ? '' : 's'}
            </span>
          </div>
          <input
            id="credits-budget"
            type="range"
            min={1}
            max={Math.max(1, remaining - (rush ? 1 : 0))}
            step={1}
            value={creditsBudget}
            onChange={(e) => setCreditsBudget(Number(e.target.value))}
            style={{ width: '100%', marginTop: 8 }}
          />
          <span className="hint">
            {slotHours} lake-slot-hours of cluster time
            {' · '}
            ≈ 4 slots × {slotHours / 4} h, or 12 slots × {(slotHours / 12).toFixed(1)} h
          </span>

          <label
            style={{
              display: 'flex',
              alignItems: 'center',
              gap: 8,
              marginTop: 16,
              fontSize: 14,
              color: rush || remaining >= 2 ? 'var(--ink-900)' : 'var(--ink-500)',
            }}
          >
            <input
              type="checkbox"
              checked={rush}
              disabled={!rush && remaining - creditsBudget < 1}
              onChange={(e) => setRush(e.target.checked)}
            />
            <span>
              <strong>Rush</strong> — +1 credit, jumps your job ahead of normal-priority work
            </span>
          </label>

          <div
            style={{
              marginTop: 16,
              display: 'flex',
              justifyContent: 'space-between',
              fontSize: 13,
              color: 'var(--ink-600)',
            }}
          >
            <span>
              Total: <strong>{totalCost}</strong> credit{totalCost === 1 ? '' : 's'}
            </span>
            <span>{remaining} remaining</span>
          </div>
        </div>
      )}

      {error && (
        <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginTop: 12 }}>
          {error}
        </div>
      )}

      <div style={{ marginTop: 24 }}>
        <button type="submit" className="btn btn-primary" disabled={submitDisabled}>
          {create.isPending
            ? 'Submitting…'
            : `Submit (${totalCost} credit${totalCost === 1 ? '' : 's'})`}
        </button>
      </div>
    </form>
  );
}
```

Imports at the top of the file need additions:

```tsx
import { useEffect, useState, type FormEvent } from 'react';
import { useQueryClient } from '@tanstack/react-query';
import { meQueryKey } from '~/lib/queries';
import type { AuthUser } from '~/lib/types';
```

`useMe` is already imported.

- [ ] **Step 3: Type-check**

Run: `cd nasrudin-frontend && pnpm type-check` (or equivalent).
Expected: PASS.

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/src/routes/research.tsx
git commit -m "research: effort slider + rush toggle in NewJobForm

Slider runs 1..remaining_credits, value shown in credits and slot-hours.
Rush checkbox costs +1 credit and is auto-disabled when the user can't
afford it. 402 responses from the API resync research_credits in the me
cache so subsequent renders show accurate state."
```

---

## Task 10: `JobRow` — RUSH chip, updated cancel copy + toast

**Files:**
- Modify: `nasrudin-frontend/src/routes/research.tsx:169-272` (JobRow + StateBadge)

- [ ] **Step 1: Add RUSH chip to JobRow**

Replace the JobRow component:

```tsx
function JobRow({ job }: { job: ResearchJob }) {
  const cancel = useCancelResearchJob();
  const terminal = ['proved', 'budget_exhausted', 'cancelled', 'Complete'];
  const isTerminal = terminal.includes(job.state);
  const slotPct = Math.min(
    100,
    Math.round((job.lake_slot_hours_consumed / job.lake_slot_hours_quota) * 100),
  );

  return (
    <li
      style={{
        padding: 16,
        marginBottom: 12,
        background: 'var(--bg-raised)',
        border: '1px solid var(--paper-200)',
        borderRadius: 'var(--radius-md)',
      }}
    >
      <div
        style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'baseline',
          gap: 12,
          flexWrap: 'wrap',
        }}
      >
        <a href={`/research/${job.id}`} style={{ fontFamily: 'var(--font-mono)', fontSize: 14 }}>
          {job.hunch.slice(0, 80)}
          {job.hunch.length > 80 && '…'}
        </a>
        <div style={{ display: 'flex', gap: 6 }}>
          {job.slice_priority > 5 && (
            <span
              style={{
                fontSize: 11,
                textTransform: 'uppercase',
                letterSpacing: 0.5,
                padding: '4px 8px',
                borderRadius: 'var(--radius-sm)',
                background: 'var(--terracotta-100, var(--paper-300))',
                color: 'var(--terracotta-700, var(--ink-700))',
              }}
            >
              RUSH
            </span>
          )}
          <StateBadge state={job.state} />
        </div>
      </div>
      <div
        style={{
          marginTop: 8,
          display: 'flex',
          gap: 16,
          flexWrap: 'wrap',
          fontSize: 12,
          color: 'var(--ink-600)',
        }}
      >
        <span>
          {job.candidates_verified.toLocaleString()} verified ·{' '}
          {job.candidates_attempted.toLocaleString()} tried
        </span>
        <span>
          {job.lake_slot_hours_consumed.toFixed(1)} / {job.lake_slot_hours_quota} slot-h ({slotPct}
          %)
        </span>
        <span>{new Date(job.created_at).toLocaleDateString()}</span>
      </div>
      {!isTerminal && (
        <div style={{ marginTop: 12 }}>
          <button
            type="button"
            className="btn btn-secondary"
            disabled={cancel.isPending}
            onClick={() => {
              if (
                confirm(
                  'Cancel this conjecture? If no theorems were verified, you\'ll be refunded credits proportional to the unused budget.',
                )
              ) {
                cancel
                  .mutateAsync(job.id)
                  .then((r) => {
                    if (r.refunded_credits > 0) {
                      // The cache invalidation in onSuccess refreshes
                      // both `research-jobs` and `me`. Surface the
                      // refund to the user via a non-blocking alert.
                      // (Replace with toast() if a toast system exists.)
                      alert(`Cancelled. Refunded ${r.refunded_credits} credit${r.refunded_credits === 1 ? '' : 's'}.`);
                    } else {
                      alert('Cancelled. No refund (work was completed or in-flight).');
                    }
                  })
                  .catch(() => {
                    /* mutation error already surfaced via cancel.error if needed */
                  });
              }
            }}
          >
            {cancel.isPending ? 'Cancelling…' : 'Cancel'}
          </button>
        </div>
      )}
    </li>
  );
}
```

(`alert()` is a placeholder — match whatever toast/snackbar pattern already exists in the codebase by grepping for an existing toast usage. If none, leave the `alert()` and flag for follow-up.)

- [ ] **Step 2: Type-check**

Run: `cd nasrudin-frontend && pnpm type-check`
Expected: PASS.

- [ ] **Step 3: Manual QA via the `qa` skill**

Use `/qa` skill or the `gstack` browser to walk through:
1. Sign in as a user with 5 credits.
2. Open `/research`. The slider should render with min 1, max 5, value 1. Submit button reads "Submit (1 credit)".
3. Drag slider to 3. Readout shows "288 lake-slot-hours…". Submit reads "Submit (3 credits)".
4. Toggle Rush on. Slider max should drop to 4. Submit reads "Submit (4 credits)".
5. Toggle Rush back off; max returns to 5.
6. Submit. Navigate to `/research/$id`. Confirm row shows quota=288, RUSH chip absent (we toggled rush off before submit). `me_credits` is now 2.
7. Resubmit a 1-credit job; refresh; cancel it. Toast says "Refunded 1 credit". Credits back to 2.
8. Resubmit at credits_budget=2 + rush=true. Cancel before any work. Refund = 3 credits.
9. Edge case: drain wallet to 0 by cancelling jobs that have completed (no refund). Slider area replaced by "0 credits available — wait for renewal or upgrade your plan".

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/src/routes/research.tsx
git commit -m "research: RUSH chip on JobRow + refund-aware cancel toast

Cancel confirmation copy now matches the proportional-refund rule.
The toast surfaces refunded_credits from the response so users see
exactly how much came back."
```

---

## Task 11: Spec correction — `research_credits_remaining` → `research_credits`

**Files:**
- Modify: `docs/superpowers/specs/2026-05-01-effort-slider-design.md`

- [ ] **Step 1: Replace mentions of the wrong column name**

Run from repo root: `grep -n "research_credits_remaining" docs/superpowers/specs/2026-05-01-effort-slider-design.md`

For each match, update the spec to say `research_credits`. There should be ~6 occurrences (in the API surface, error matrix, frontend state block, and the open-verifications section).

- [ ] **Step 2: Update the spec's open-verifications section**

The "open implementation-time verifications" section listed three items. Two are now resolved:

1. ~~Heartbeat WHERE clause includes state guard.~~ — Resolved by Task 4.
2. **Capacity counter rebuilds from DB on API restart.** Still open; flag as a follow-up to verify in operations.
3. ~~`/api/me` exposes `research_credits_remaining`.~~ — Resolved by Task 1 (the actual surface is `/api/auth/me` carrying `research_credits`).

Update the section to reflect this.

- [ ] **Step 3: Commit**

```bash
git add docs/superpowers/specs/2026-05-01-effort-slider-design.md
git commit -m "spec: align column name with the source of truth (research_credits)

The original spec used research_credits_remaining throughout, but the
column on users is research_credits. The implementation uses the
correct name; this commit aligns the prose."
```

---

## Self-Review Checklist (run after writing the plan)

- **Spec coverage:** Walk each section of the spec.
  - Architecture: covered by Tasks 6 (submit) and 7 (cancel). ✓
  - Data model: Tasks 2, 3 (helpers); migration unchanged. ✓
  - API surface — submit: Task 6. ✓
  - API surface — cancel: Task 7. ✓
  - UI surface — NewJobForm: Task 9. ✓
  - UI surface — JobRow: Task 10. ✓
  - Error handling matrix: Task 6 covers 400/402; Task 7 covers 409; transactional rollback is implicit in Task 6. ✓
  - Backwards compatibility: defaults reproduce today's behavior — covered by Tasks 6 step 4 (`default_credits_budget`) and Task 8 step 2 (optional fields). ✓
  - Testing: each backend task has tests; frontend gets type-check + manual QA. Existing test suites must continue to pass — explicit `cargo test -p physics_api` checkpoints in Tasks 6 and 7. ✓

- **Placeholder scan:** No "TODO" / "TBD" / "implement later" in any task. The `alert()` in Task 10 is flagged as a placeholder if no toast system exists, with instructions to grep first. The "find existing harness" step in Task 6 is unavoidable — the agent must look at what the crate already provides; the bar is not "no investigation required" but "no required code is missing". ✓

- **Type consistency:**
  - `try_decrement_research_credits_n` is `&impl ConnectionTrait`, `Uuid`, `i32` → `Result<Option<i32>, DbErr>`. Used identically in Tasks 2 and 6. ✓
  - `cancel_paid_with_refund` returns `CancelOutcome { row_was_cancelled, refunded_credits, allocated_slots }`. Used identically in Tasks 5 and 7. ✓
  - `JobEvent::Cancelled { refunded_credits }` (i32) — defined in Task 7 step 4, consumed by frontend `ResearchJobEvent` (number) in Task 8. ✓
  - HTTP cancel response `{cancelled, refunded_credits}` — Task 7 emits, Task 8 types it, Task 10 reads `r.refunded_credits`. ✓
  - `AuthUser.research_credits` — Task 1 adds (Rust `i32`), Task 8 mirrors (TS `number`), Task 9 reads. ✓

---

## Execution Handoff

**Plan complete and saved to `docs/superpowers/plans/2026-05-01-effort-slider.md`. Two execution options:**

**1. Subagent-Driven (recommended)** — I dispatch a fresh subagent per task, review between tasks, fast iteration

**2. Inline Execution** — Execute tasks in this session using executing-plans, batch execution with checkpoints

Which approach?
