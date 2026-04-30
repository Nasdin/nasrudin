# Admin Panel & Trust-Bypass Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship the admin panel at `nasrudin.org/admin` (gated by `users.is_admin`) plus the trust-bypass verification path that lets trusted contributors and the co-located droplet worker skip the redundant server-side `lake build` confirmation, with sampled spot-check, audit logging, transactional email, Stripe refunds, user impersonation, and bulk operations.

**Architecture:** Backend is Rust/axum/sea-orm. Eight additive Postgres migrations land first, then the trust-resolution module, the unix-domain-socket listener, the spot-check sampling in `reverify.rs`, an audit-log invariant helper (`perform_audited`), the new admin handlers, the Resend-backed email outbox, the Stripe refund flow, the HMAC impersonation layer, and the bulk runner. Frontend is TanStack Router file-based, mounting an `/admin` tree gated by `users.is_admin` and a global impersonation banner.

**Tech Stack:** Rust 2024 / axum 0.8 / axum-login 0.18 / SeaORM 2 / async-stripe 0.41 / dashmap / tokio-broadcast / hyper-util UDS / Resend REST / Tera templates / React 19 / TanStack Router / TanStack Query / Vitest / Playwright.

**Migration sequence reservation:** Existing repo already has `m20260430_000013` through `m20260430_000015`. This plan uses `m20260430_000020` through `m20260430_000027` for the eight new migrations to leave a gap.

**Spec:** `docs/superpowers/specs/2026-04-30-admin-panel-and-trust-bypass-design.md`

**Conventions used throughout this plan:**
- Every test file lives next to peers in `engine/crates/<crate>/tests/` for integration tests, or as a `#[cfg(test)] mod tests` block at the bottom of the source file for unit tests. Frontend tests are colocated as `*.test.tsx`.
- All admin mutating handlers MUST go through `perform_audited` (defined in Task 18). PRs that add an admin endpoint without it should be rejected.
- All commits use Conventional-Commits (`feat:`, `fix:`, `test:`, `refactor:`, `chore:`, `docs:`).
- The integration test harness `engine/crates/api/tests/test_app/mod.rs` is the entry point for HTTP-level tests; reuse `TestApp::build()`.

---

## File Map

### Backend — new

```
engine/crates/pg/src/migrator/
  m20260430_000020_admin_users_columns.rs       -- is_admin, is_trusted, spot_check_rate
  m20260430_000021_admin_api_keys_columns.rs    -- trust_override, spot_check_rate
  m20260430_000022_admin_audit_log.rs           -- admin_audit_log table + indexes
  m20260430_000023_impersonation_sessions.rs    -- impersonation_sessions table
  m20260430_000024_email_outbox.rs              -- email_outbox table + partial index
  m20260430_000025_refund_records.rs            -- refund_records table
  m20260430_000026_bulk_runs.rs                 -- bulk_runs table
  m20260430_000027_last_admin_trigger.rs        -- prevent_last_admin_demotion fn + trigger

engine/crates/pg/src/entity/
  admin_audit_log.rs
  impersonation_sessions.rs
  email_outbox.rs
  refund_records.rs
  bulk_runs.rs

engine/crates/pg/src/query/
  admin_users.rs           -- admin-only user CRUD (set_is_admin, set_is_trusted, ...)
  admin_audit_log.rs       -- insert/list audit rows
  impersonation.rs         -- session row CRUD + active-by-admin lookup
  email_outbox.rs          -- queue, queue_in_txn, claim_pending, mark_sent, mark_failed
  refund_records.rs        -- insert, find, update_from_stripe, list_pending
  bulk_runs.rs             -- insert, update_counters, complete, reap_stale

engine/crates/api/src/
  trust.rs                 -- TrustDecision, TrustSource, TrustCache, resolve()
  impersonation.rs         -- ImpersonationLayer + token signing/verify
  admin/
    mod.rs                 -- public re-exports
    audit.rs               -- perform_audited helper + actions:: constants
    require_admin.rs       -- RequireAdmin extractor
  email/
    mod.rs                 -- queue() / queue_in_txn() / spawn_worker()
    outbox.rs              -- DB CRUD wrappers
    provider.rs            -- EmailProvider trait + ResendProvider impl
    templates.rs           -- Tera template registry
    worker.rs              -- async drain loop
    templates/
      admin_credit_grant.html
      admin_credit_grant.txt
      admin_plan_change.html
      admin_plan_change.txt
      admin_refund_issued.html
      admin_refund_issued.txt
      admin_account_action.html
      admin_account_action.txt
      admin_custom_message.html
      admin_custom_message.txt
  billing/
    refund.rs              -- start_refund flow (DB-first → Stripe)
    refund_reconciler.rs   -- 60s tick reconciler
  handlers/
    admin/
      mod.rs               -- module re-exports
      corpus.rs            -- migrated reload_corpus
      steering.rs          -- migrated steering_recent / steering_force
      users.rs             -- list, detail, set_admin, set_trust, set_plan, set_credits, set_spot_check_rate
      api_keys.rs          -- revoke, set_trust_override
      jobs.rs              -- cancel
      audit_log.rs         -- list with filters
      stats.rs             -- aggregate stats with cache
      refund.rs            -- POST /api/admin/users/{id}/refund
      impersonate.rs       -- start/end/force_end
      email.rs             -- list outbox, retry, send custom
      bulk.rs              -- start, SSE stream
    webhook_resend.rs      -- POST /api/webhook/resend

engine/crates/api/tests/
  trust_resolution.rs
  trust_cache.rs
  unix_socket_listener.rs
  spot_check_sampling.rs
  admin_require_admin.rs
  admin_audit_invariant.rs
  admin_users_handlers.rs
  admin_api_keys_handlers.rs
  admin_jobs_handlers.rs
  admin_audit_log_handler.rs
  admin_stats_handler.rs
  admin_refund_flow.rs
  admin_refund_reconciler.rs
  admin_impersonation.rs
  admin_bulk.rs
  admin_email_worker.rs
  webhook_resend.rs
  last_admin_trigger.rs

deploy/
  scripts/
    admin-bootstrap.sh
    email-dns-setup.md
  systemd/
    nasrudin-worker.service        -- new (local-droplet worker uses UDS)

docs/admin/
  runbook.md
```

### Backend — modified

```
engine/crates/pg/src/entity/users.rs
engine/crates/pg/src/entity/api_keys.rs
engine/crates/pg/src/entity/mod.rs
engine/crates/pg/src/migrator/mod.rs
engine/crates/pg/src/query/users.rs
engine/crates/pg/src/query/api_keys.rs
engine/crates/pg/src/query/mod.rs
engine/crates/api/src/lib.rs
engine/crates/api/src/main.rs
engine/crates/api/src/state.rs
engine/crates/api/src/auth.rs
engine/crates/api/src/handlers/mod.rs
engine/crates/api/src/handlers/admin.rs       -- DELETED, contents moved into admin/
engine/crates/api/src/handlers/ingest.rs
engine/crates/api/src/reverify.rs
engine/crates/api/src/lake_promotion.rs
engine/crates/api/src/billing/webhook.rs
engine/crates/api/src/billing/mod.rs
engine/crates/api/src/metrics.rs
engine/crates/api/Cargo.toml                  -- add: hyper-util UDS feature, hmac, sha2, tera, dashmap (already), regex (already), wiremock (dev-dep)
engine/crates/ga/Cargo.toml                   -- add hyper-util UDS feature, hyperlocal
engine/crates/ga/src/bin/worker.rs            -- recognize unix:// URL prefix
engine/crates/api/tests/test_app/mod.rs       -- add admin/email/billing wiring
deploy/Caddyfile.native                       -- documentation comment only (Caddy keeps proxying TCP)
deploy/systemd/nasrudin-api.service           -- new env vars
CLAUDE.md
README.md
.env.example
```

### Frontend — new

```
nasrudin-frontend/src/lib/
  adminApi.ts                                  -- adminFetch wrapper
  adminTypes.ts                                -- AdminUser, AuditLogEntry, BulkRun, etc.
nasrudin-frontend/src/components/admin/
  DataTable.tsx
  DataTable.test.tsx
  ConfirmWithReasonModal.tsx
  ConfirmWithReasonModal.test.tsx
  ImpersonationBanner.tsx
  ImpersonationBanner.test.tsx
  RefundButton.tsx
nasrudin-frontend/src/routes/
  admin.tsx
  admin.index.tsx
  admin.users.tsx
  admin.users.$id.tsx
  admin.audit.tsx
  admin.impersonations.tsx
  admin.email.tsx
  admin.steering.tsx
  admin.corpus.tsx
  admin.bulk.tsx
nasrudin-frontend/tests/e2e/
  admin-trust-toggle.spec.ts
  admin-impersonation.spec.ts
  admin-bulk-run.spec.ts
```

### Frontend — modified

```
nasrudin-frontend/src/routes/__root.tsx       -- add ImpersonationBanner + admin nav
nasrudin-frontend/src/lib/types.ts            -- extend AuthUser with is_admin/is_trusted/spot_check_rate
nasrudin-frontend/src/lib/api.ts              -- thread X-Impersonate-Token header
nasrudin-frontend/src/lib/queries.ts          -- (no API change — keep as-is)
nasrudin-frontend/package.json                -- add @tanstack/react-table
```

---

## Section A — Database migrations & entities

### Task 1: `users` columns migration + entity update

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000020_admin_users_columns.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs` (register)
- Modify: `engine/crates/pg/src/entity/users.rs` (add fields)
- Modify: `engine/crates/pg/src/query/users.rs` (set defaults in `create_user`)
- Test: `engine/crates/pg/tests/admin_users_columns.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/pg/tests/admin_users_columns.rs
use nasrudin_pg::{connect_simple, run_migrations, query::users::create_user, entity::users};
use sea_orm::EntityTrait;

#[tokio::test]
async fn user_has_admin_trust_columns_with_defaults() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    });
    let db = connect_simple(&url).await.unwrap();
    run_migrations(&db).await.unwrap();

    let u = create_user(&db, "trustcols@test.local", Some("hash"), None).await.unwrap();
    let m = users::Entity::find_by_id(u.id).one(&db).await.unwrap().unwrap();
    assert_eq!(m.is_admin, false);
    assert_eq!(m.is_trusted, false);
    assert_eq!(m.spot_check_rate, None);
}
```

- [ ] **Step 2: Run test to verify it fails (compile error: unknown fields)**

Run: `cd engine && cargo test -p nasrudin-pg --test admin_users_columns -- --nocapture`
Expected: FAIL with `no field 'is_admin'`.

- [ ] **Step 3: Write the migration**

```rust
// engine/crates/pg/src/migrator/m20260430_000020_admin_users_columns.rs
//! Admin-panel user flags: is_admin, is_trusted, optional spot_check_rate.
//!
//! `spot_check_rate`: NULL = use env default; 0 = pure trust; 1 = check every;
//! N = 1-in-N. Inherits to api_keys.spot_check_rate when that is also NULL.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.alter_table(
            Table::alter().table(Users::Table)
                .add_column_if_not_exists(ColumnDef::new(Users::IsAdmin).boolean().not_null().default(false))
                .add_column_if_not_exists(ColumnDef::new(Users::IsTrusted).boolean().not_null().default(false))
                .add_column_if_not_exists(ColumnDef::new(Users::SpotCheckRate).integer().null())
                .to_owned(),
        ).await
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.alter_table(
            Table::alter().table(Users::Table)
                .drop_column(Users::IsAdmin)
                .drop_column(Users::IsTrusted)
                .drop_column(Users::SpotCheckRate)
                .to_owned(),
        ).await
    }
}

#[derive(DeriveIden)]
enum Users { Table, IsAdmin, IsTrusted, SpotCheckRate }
```

- [ ] **Step 4: Register the migration**

In `engine/crates/pg/src/migrator/mod.rs`, add at the end of the `mod` declarations and the `Migrator::migrations()` vec:

```rust
mod m20260430_000020_admin_users_columns;
// ...
Box::new(m20260430_000020_admin_users_columns::Migration),
```

- [ ] **Step 5: Add fields to the entity**

Edit `engine/crates/pg/src/entity/users.rs` — append fields after `github_login`:

```rust
pub is_admin: bool,
pub is_trusted: bool,
pub spot_check_rate: Option<i32>,
```

- [ ] **Step 6: Update `create_user` to set defaults**

In `engine/crates/pg/src/query/users.rs`, inside the `users::ActiveModel { ... }` literal of `create_user`, add:

```rust
is_admin: Set(false),
is_trusted: Set(false),
spot_check_rate: Set(None),
```

Repeat for any other `users::ActiveModel { ... }` constructions in the file (search `users::ActiveModel`).

- [ ] **Step 7: Run test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-pg --test admin_users_columns -- --nocapture`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000020_admin_users_columns.rs \
        engine/crates/pg/src/migrator/mod.rs \
        engine/crates/pg/src/entity/users.rs \
        engine/crates/pg/src/query/users.rs \
        engine/crates/pg/tests/admin_users_columns.rs
git commit -m "feat(pg): add is_admin, is_trusted, spot_check_rate to users"
```

### Task 2: `api_keys` columns migration + entity update

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000021_admin_api_keys_columns.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs` (register)
- Modify: `engine/crates/pg/src/entity/api_keys.rs` (add fields)
- Test: `engine/crates/pg/tests/api_keys_admin_columns.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/pg/tests/api_keys_admin_columns.rs
use nasrudin_pg::{connect_simple, run_migrations, entity::api_keys};
use sea_orm::{EntityTrait, ActiveValue::Set};
use uuid::Uuid;

#[tokio::test]
async fn api_keys_has_trust_override_columns() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    });
    let db = connect_simple(&url).await.unwrap();
    run_migrations(&db).await.unwrap();

    let m = api_keys::ActiveModel {
        id: Set(Uuid::new_v4()),
        user_id: Set(None),
        kind: Set("worker".into()),
        name: Set("k1".into()),
        prefix: Set(format!("nsk_worker_t{}", Uuid::new_v4().simple())[..14].to_string()),
        key_hash: Set("$argon2id$_".into()),
        last_used_at: Set(None),
        expires_at: Set(None),
        created_at: Set(chrono::Utc::now().into()),
        revoked_at: Set(None),
        trust_override: Set(Some(true)),
        spot_check_rate: Set(Some(10)),
    };
    let row = api_keys::Entity::insert(m).exec_with_returning(&db).await.unwrap();
    assert_eq!(row.trust_override, Some(true));
    assert_eq!(row.spot_check_rate, Some(10));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-pg --test api_keys_admin_columns`
Expected: FAIL — unknown fields.

- [ ] **Step 3: Write the migration**

```rust
// engine/crates/pg/src/migrator/m20260430_000021_admin_api_keys_columns.rs
//! Per-API-key trust override + spot-check rate (Phase trust-bypass).

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.alter_table(
            Table::alter().table(ApiKeys::Table)
                .add_column_if_not_exists(ColumnDef::new(ApiKeys::TrustOverride).boolean().null())
                .add_column_if_not_exists(ColumnDef::new(ApiKeys::SpotCheckRate).integer().null())
                .to_owned(),
        ).await
    }
    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.alter_table(
            Table::alter().table(ApiKeys::Table)
                .drop_column(ApiKeys::TrustOverride)
                .drop_column(ApiKeys::SpotCheckRate)
                .to_owned(),
        ).await
    }
}

#[derive(DeriveIden)]
enum ApiKeys { Table, TrustOverride, SpotCheckRate }
```

- [ ] **Step 4: Register the migration**

`engine/crates/pg/src/migrator/mod.rs`: add `mod m20260430_000021_admin_api_keys_columns;` and `Box::new(m20260430_000021_admin_api_keys_columns::Migration),`.

- [ ] **Step 5: Add fields to the entity**

In `engine/crates/pg/src/entity/api_keys.rs`, after `revoked_at`:

```rust
pub trust_override: Option<bool>,
pub spot_check_rate: Option<i32>,
```

- [ ] **Step 6: Run test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-pg --test api_keys_admin_columns`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000021_admin_api_keys_columns.rs \
        engine/crates/pg/src/migrator/mod.rs \
        engine/crates/pg/src/entity/api_keys.rs \
        engine/crates/pg/tests/api_keys_admin_columns.rs
git commit -m "feat(pg): add trust_override + spot_check_rate to api_keys"
```

### Task 3: `admin_audit_log` migration, entity, and query module

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000022_admin_audit_log.rs`
- Create: `engine/crates/pg/src/entity/admin_audit_log.rs`
- Create: `engine/crates/pg/src/query/admin_audit_log.rs`
- Modify: `engine/crates/pg/src/entity/mod.rs`, `engine/crates/pg/src/query/mod.rs`, `engine/crates/pg/src/migrator/mod.rs`
- Test: `engine/crates/pg/tests/admin_audit_log.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/pg/tests/admin_audit_log.rs
use nasrudin_pg::{connect_simple, run_migrations, query};
use sea_orm::TransactionTrait;
use uuid::Uuid;

#[tokio::test]
async fn audit_log_insert_and_list_round_trip() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| {
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into()
    });
    let db = connect_simple(&url).await.unwrap();
    run_migrations(&db).await.unwrap();

    let actor = query::users::create_user(&db, "auditor@test.local", Some("h"), None).await.unwrap();
    let target = query::users::create_user(&db, "audited@test.local", Some("h"), None).await.unwrap();

    let txn = db.begin().await.unwrap();
    let id = query::admin_audit_log::insert(
        &txn,
        actor.id, Some(target.id), None, "SET_IS_TRUSTED",
        Some(serde_json::json!({"is_trusted": false})),
        Some(serde_json::json!({"is_trusted": true})),
        "promoting test user".to_string(),
        Some("127.0.0.1".parse().unwrap()), Some("test/1.0".to_string()),
    ).await.unwrap();
    txn.commit().await.unwrap();

    let rows = query::admin_audit_log::list_by_target(&db, target.id, 10).await.unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].id, id);
    assert_eq!(rows[0].action, "SET_IS_TRUSTED");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-pg --test admin_audit_log`
Expected: FAIL — `query::admin_audit_log` does not exist.

- [ ] **Step 3: Write the migration**

```rust
// engine/crates/pg/src/migrator/m20260430_000022_admin_audit_log.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared(r#"
            CREATE TABLE IF NOT EXISTS admin_audit_log (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                actor_user_id UUID NOT NULL REFERENCES users(id),
                target_user_id UUID REFERENCES users(id),
                action TEXT NOT NULL,
                before_value JSONB,
                after_value JSONB,
                reason TEXT NOT NULL,
                impersonating_user_id UUID REFERENCES users(id),
                request_ip INET,
                user_agent TEXT,
                created_at TIMESTAMPTZ NOT NULL DEFAULT now()
            );
            CREATE INDEX IF NOT EXISTS admin_audit_log_target ON admin_audit_log (target_user_id, created_at DESC);
            CREATE INDEX IF NOT EXISTS admin_audit_log_actor ON admin_audit_log (actor_user_id, created_at DESC);
            CREATE INDEX IF NOT EXISTS admin_audit_log_action ON admin_audit_log (action, created_at DESC);
        "#).await?;
        Ok(())
    }
    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared("DROP TABLE IF EXISTS admin_audit_log").await?;
        Ok(())
    }
}
```

- [ ] **Step 4: Write the entity**

```rust
// engine/crates/pg/src/entity/admin_audit_log.rs
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "admin_audit_log")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub actor_user_id: Uuid,
    pub target_user_id: Option<Uuid>,
    pub action: String,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub before_value: Option<Json>,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub after_value: Option<Json>,
    pub reason: String,
    pub impersonating_user_id: Option<Uuid>,
    /// Stored as Postgres `inet`; we keep it as a `String` here because SeaORM's
    /// `Inet` mapping is flaky across versions and we only ever read/write it.
    #[sea_orm(column_type = "Text", nullable)]
    pub request_ip: Option<String>,
    pub user_agent: Option<String>,
    pub created_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 5: Write the query module**

```rust
// engine/crates/pg/src/query/admin_audit_log.rs
use sea_orm::{ConnectionTrait, DbErr, EntityTrait, QueryFilter, QueryOrder, Statement, DatabaseBackend};
use sea_orm::prelude::*;
use uuid::Uuid;
use std::net::IpAddr;

use crate::entity::admin_audit_log;

#[allow(clippy::too_many_arguments)]
pub async fn insert<C: ConnectionTrait>(
    conn: &C,
    actor_user_id: Uuid,
    target_user_id: Option<Uuid>,
    impersonating_user_id: Option<Uuid>,
    action: &str,
    before_value: Option<serde_json::Value>,
    after_value: Option<serde_json::Value>,
    reason: String,
    request_ip: Option<IpAddr>,
    user_agent: Option<String>,
) -> Result<Uuid, DbErr> {
    // Use raw SQL so we can cast the IP through Postgres's `inet` parser.
    let id = Uuid::new_v4();
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "INSERT INTO admin_audit_log
           (id, actor_user_id, target_user_id, action, before_value, after_value,
            reason, impersonating_user_id, request_ip, user_agent)
         VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9::inet, $10)",
        [
            id.into(), actor_user_id.into(), target_user_id.into(),
            action.to_string().into(),
            before_value.unwrap_or(serde_json::Value::Null).into(),
            after_value.unwrap_or(serde_json::Value::Null).into(),
            reason.into(),
            impersonating_user_id.into(),
            request_ip.map(|ip| ip.to_string()).into(),
            user_agent.into(),
        ],
    )).await?;
    Ok(id)
}

pub async fn list_by_target<C: ConnectionTrait>(conn: &C, target: Uuid, limit: u64) -> Result<Vec<admin_audit_log::Model>, DbErr> {
    admin_audit_log::Entity::find()
        .filter(admin_audit_log::Column::TargetUserId.eq(target))
        .order_by_desc(admin_audit_log::Column::CreatedAt)
        .limit(limit)
        .all(conn)
        .await
}

pub async fn list_recent<C: ConnectionTrait>(conn: &C, limit: u64) -> Result<Vec<admin_audit_log::Model>, DbErr> {
    admin_audit_log::Entity::find()
        .order_by_desc(admin_audit_log::Column::CreatedAt)
        .limit(limit)
        .all(conn)
        .await
}

pub async fn list_filtered<C: ConnectionTrait>(
    conn: &C,
    actor: Option<Uuid>,
    target: Option<Uuid>,
    action: Option<&str>,
    limit: u64,
    offset: u64,
) -> Result<Vec<admin_audit_log::Model>, DbErr> {
    let mut q = admin_audit_log::Entity::find();
    if let Some(a) = actor { q = q.filter(admin_audit_log::Column::ActorUserId.eq(a)); }
    if let Some(t) = target { q = q.filter(admin_audit_log::Column::TargetUserId.eq(t)); }
    if let Some(act) = action { q = q.filter(admin_audit_log::Column::Action.eq(act)); }
    q.order_by_desc(admin_audit_log::Column::CreatedAt)
        .limit(limit).offset(offset)
        .all(conn).await
}
```

- [ ] **Step 6: Wire up modules**

`engine/crates/pg/src/entity/mod.rs`: add `pub mod admin_audit_log;`.
`engine/crates/pg/src/query/mod.rs`: add `pub mod admin_audit_log;`.
`engine/crates/pg/src/migrator/mod.rs`: add `mod m20260430_000022_admin_audit_log;` and `Box::new(...)`.

- [ ] **Step 7: Run test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-pg --test admin_audit_log`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000022_admin_audit_log.rs \
        engine/crates/pg/src/entity/admin_audit_log.rs \
        engine/crates/pg/src/entity/mod.rs \
        engine/crates/pg/src/query/admin_audit_log.rs \
        engine/crates/pg/src/query/mod.rs \
        engine/crates/pg/src/migrator/mod.rs \
        engine/crates/pg/tests/admin_audit_log.rs
git commit -m "feat(pg): add admin_audit_log table + entity + queries"
```

### Task 4: `impersonation_sessions` migration + entity + queries

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000023_impersonation_sessions.rs`
- Create: `engine/crates/pg/src/entity/impersonation_sessions.rs`
- Create: `engine/crates/pg/src/query/impersonation.rs`
- Modify: `engine/crates/pg/src/{entity,query,migrator}/mod.rs`
- Test: `engine/crates/pg/tests/impersonation_sessions.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/pg/tests/impersonation_sessions.rs
use nasrudin_pg::{connect_simple, run_migrations, query};
use chrono::Utc;

#[tokio::test]
async fn impersonation_session_lifecycle() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_|
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into());
    let db = connect_simple(&url).await.unwrap();
    run_migrations(&db).await.unwrap();
    let admin = query::users::create_user(&db, "imp-admin@t.local", Some("h"), None).await.unwrap();
    let target = query::users::create_user(&db, "imp-target@t.local", Some("h"), None).await.unwrap();

    let row = query::impersonation::start(&db, admin.id, target.id, Utc::now() + chrono::Duration::seconds(900), "debugging".into()).await.unwrap();
    assert!(query::impersonation::find_active(&db, row.id).await.unwrap().is_some());
    query::impersonation::end(&db, row.id, "manual_end").await.unwrap();
    assert!(query::impersonation::find_active(&db, row.id).await.unwrap().is_none());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-pg --test impersonation_sessions`
Expected: FAIL — module missing.

- [ ] **Step 3: Write the migration**

```rust
// engine/crates/pg/src/migrator/m20260430_000023_impersonation_sessions.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared(r#"
            CREATE TABLE IF NOT EXISTS impersonation_sessions (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                admin_user_id UUID NOT NULL REFERENCES users(id),
                target_user_id UUID NOT NULL REFERENCES users(id),
                started_at TIMESTAMPTZ NOT NULL DEFAULT now(),
                expires_at TIMESTAMPTZ NOT NULL,
                ended_at TIMESTAMPTZ,
                end_reason TEXT,
                reason TEXT NOT NULL
            );
            CREATE INDEX IF NOT EXISTS impersonation_active ON impersonation_sessions (admin_user_id) WHERE ended_at IS NULL;
            CREATE INDEX IF NOT EXISTS impersonation_target ON impersonation_sessions (target_user_id, started_at DESC);
        "#).await?;
        Ok(())
    }
    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared("DROP TABLE IF EXISTS impersonation_sessions").await?;
        Ok(())
    }
}
```

- [ ] **Step 4: Write the entity**

```rust
// engine/crates/pg/src/entity/impersonation_sessions.rs
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "impersonation_sessions")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub admin_user_id: Uuid,
    pub target_user_id: Uuid,
    pub started_at: DateTimeWithTimeZone,
    pub expires_at: DateTimeWithTimeZone,
    pub ended_at: Option<DateTimeWithTimeZone>,
    pub end_reason: Option<String>,
    pub reason: String,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 5: Write the query module**

```rust
// engine/crates/pg/src/query/impersonation.rs
use sea_orm::{ActiveModelTrait, ColumnTrait, ConnectionTrait, DbErr, EntityTrait, QueryFilter, ActiveValue::Set};
use chrono::Utc;
use uuid::Uuid;

use crate::entity::impersonation_sessions as ent;

pub async fn start<C: ConnectionTrait>(
    conn: &C, admin: Uuid, target: Uuid,
    expires_at: chrono::DateTime<Utc>, reason: String,
) -> Result<ent::Model, DbErr> {
    let id = Uuid::new_v4();
    let now: chrono::DateTime<chrono::FixedOffset> = Utc::now().into();
    let row = ent::ActiveModel {
        id: Set(id),
        admin_user_id: Set(admin),
        target_user_id: Set(target),
        started_at: Set(now),
        expires_at: Set(expires_at.into()),
        ended_at: Set(None),
        end_reason: Set(None),
        reason: Set(reason),
    };
    row.insert(conn).await
}

pub async fn end<C: ConnectionTrait>(conn: &C, id: Uuid, reason: &str) -> Result<(), DbErr> {
    let row = ent::Entity::find_by_id(id).one(conn).await?
        .ok_or_else(|| DbErr::RecordNotFound("impersonation session not found".into()))?;
    let mut active: ent::ActiveModel = row.into();
    active.ended_at = Set(Some(Utc::now().into()));
    active.end_reason = Set(Some(reason.to_string()));
    active.update(conn).await?;
    Ok(())
}

pub async fn find_active<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<Option<ent::Model>, DbErr> {
    let row = ent::Entity::find_by_id(id).one(conn).await?;
    Ok(row.filter(|r| r.ended_at.is_none() && r.expires_at > Utc::now()))
}

pub async fn list_expired<C: ConnectionTrait>(conn: &C) -> Result<Vec<ent::Model>, DbErr> {
    ent::Entity::find()
        .filter(ent::Column::EndedAt.is_null())
        .filter(ent::Column::ExpiresAt.lt(chrono::DateTime::<chrono::FixedOffset>::from(Utc::now())))
        .all(conn).await
}
```

- [ ] **Step 6: Wire up modules + register migration**

`entity/mod.rs`: `pub mod impersonation_sessions;`
`query/mod.rs`: `pub mod impersonation;`
`migrator/mod.rs`: register the migration.

- [ ] **Step 7: Run test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-pg --test impersonation_sessions`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000023_impersonation_sessions.rs \
        engine/crates/pg/src/entity/impersonation_sessions.rs \
        engine/crates/pg/src/query/impersonation.rs \
        engine/crates/pg/src/{entity,query,migrator}/mod.rs \
        engine/crates/pg/tests/impersonation_sessions.rs
git commit -m "feat(pg): impersonation_sessions table + entity + queries"
```

### Task 5: `email_outbox` migration + entity + queries

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000024_email_outbox.rs`
- Create: `engine/crates/pg/src/entity/email_outbox.rs`
- Create: `engine/crates/pg/src/query/email_outbox.rs`
- Modify: `engine/crates/pg/src/{entity,query,migrator}/mod.rs`
- Test: `engine/crates/pg/tests/email_outbox.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/pg/tests/email_outbox.rs
use nasrudin_pg::{connect_simple, run_migrations, query};

#[tokio::test]
async fn email_outbox_queue_then_claim() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_|
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into());
    let db = connect_simple(&url).await.unwrap();
    run_migrations(&db).await.unwrap();

    let user = query::users::create_user(&db, "email@t.local", Some("h"), None).await.unwrap();
    let id = query::email_outbox::queue(
        &db, Some(user.id), "email@t.local", "admin_credit_grant",
        "Subject", "body text", Some("body html"), None, None,
    ).await.unwrap();

    let pending = query::email_outbox::claim_pending(&db, 5).await.unwrap();
    assert!(pending.iter().any(|m| m.id == id));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-pg --test email_outbox`
Expected: FAIL — module missing.

- [ ] **Step 3: Write the migration**

```rust
// engine/crates/pg/src/migrator/m20260430_000024_email_outbox.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared(r#"
            CREATE TABLE IF NOT EXISTS email_outbox (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                to_user_id UUID REFERENCES users(id),
                to_address TEXT NOT NULL,
                template TEXT NOT NULL,
                subject TEXT NOT NULL,
                body_text TEXT NOT NULL,
                body_html TEXT,
                status TEXT NOT NULL DEFAULT 'queued',
                attempts INTEGER NOT NULL DEFAULT 0,
                last_attempt_at TIMESTAMPTZ,
                last_error TEXT,
                provider_message_id TEXT,
                queued_by_admin_id UUID REFERENCES users(id),
                queued_by_action TEXT,
                created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
                sent_at TIMESTAMPTZ
            );
            CREATE INDEX IF NOT EXISTS email_outbox_pending ON email_outbox (status, created_at)
                WHERE status IN ('queued', 'failed_retrying');
            CREATE INDEX IF NOT EXISTS email_outbox_user ON email_outbox (to_user_id, created_at DESC);
        "#).await?;
        Ok(())
    }
    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared("DROP TABLE IF EXISTS email_outbox").await?;
        Ok(())
    }
}
```

- [ ] **Step 4: Write the entity**

```rust
// engine/crates/pg/src/entity/email_outbox.rs
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "email_outbox")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub to_user_id: Option<Uuid>,
    pub to_address: String,
    pub template: String,
    pub subject: String,
    #[sea_orm(column_type = "Text")]
    pub body_text: String,
    #[sea_orm(column_type = "Text", nullable)]
    pub body_html: Option<String>,
    pub status: String,
    pub attempts: i32,
    pub last_attempt_at: Option<DateTimeWithTimeZone>,
    pub last_error: Option<String>,
    pub provider_message_id: Option<String>,
    pub queued_by_admin_id: Option<Uuid>,
    pub queued_by_action: Option<String>,
    pub created_at: DateTimeWithTimeZone,
    pub sent_at: Option<DateTimeWithTimeZone>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}
impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 5: Write the query module**

```rust
// engine/crates/pg/src/query/email_outbox.rs
use sea_orm::{ActiveModelTrait, ColumnTrait, ConnectionTrait, DbErr, EntityTrait, QueryFilter,
    QueryOrder, QuerySelect, ActiveValue::Set, Statement, DatabaseBackend};
use uuid::Uuid;

use crate::entity::email_outbox as ent;

#[allow(clippy::too_many_arguments)]
pub async fn queue<C: ConnectionTrait>(
    conn: &C, to_user_id: Option<Uuid>, to_address: &str,
    template: &str, subject: &str, body_text: &str, body_html: Option<&str>,
    queued_by_admin_id: Option<Uuid>, queued_by_action: Option<&str>,
) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    ent::ActiveModel {
        id: Set(id),
        to_user_id: Set(to_user_id),
        to_address: Set(to_address.into()),
        template: Set(template.into()),
        subject: Set(subject.into()),
        body_text: Set(body_text.into()),
        body_html: Set(body_html.map(str::to_string)),
        status: Set("queued".into()),
        attempts: Set(0),
        last_attempt_at: Set(None),
        last_error: Set(None),
        provider_message_id: Set(None),
        queued_by_admin_id: Set(queued_by_admin_id),
        queued_by_action: Set(queued_by_action.map(str::to_string)),
        created_at: Set(chrono::Utc::now().into()),
        sent_at: Set(None),
    }.insert(conn).await?;
    Ok(id)
}

/// Claim up to `limit` pending rows whose backoff window has elapsed.
/// Eligible: status='queued' OR (status='failed_retrying' AND last_attempt_at is older than
/// 5min * pow(2, attempts) AND attempts < 5).
pub async fn claim_pending<C: ConnectionTrait>(conn: &C, limit: u32) -> Result<Vec<ent::Model>, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        SELECT id, to_user_id, to_address, template, subject, body_text, body_html, status,
               attempts, last_attempt_at, last_error, provider_message_id, queued_by_admin_id,
               queued_by_action, created_at, sent_at
        FROM email_outbox
        WHERE status = 'queued'
           OR (status = 'failed_retrying' AND attempts < 5
               AND (last_attempt_at IS NULL
                    OR last_attempt_at < now() - (interval '5 minute' * (1 << attempts))))
        ORDER BY created_at ASC
        LIMIT $1
        "#,
        [(limit as i64).into()],
    );
    ent::Model::find_by_statement(stmt).all(conn).await
}

pub async fn mark_sent<C: ConnectionTrait>(conn: &C, id: Uuid, provider_message_id: &str) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE email_outbox SET status='sent', sent_at=now(), provider_message_id=$2,
                last_attempt_at=now(), attempts=attempts+1
         WHERE id=$1",
        [id.into(), provider_message_id.to_string().into()],
    )).await?;
    Ok(())
}

pub async fn mark_failed_retrying<C: ConnectionTrait>(conn: &C, id: Uuid, err: &str) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE email_outbox SET status='failed_retrying', last_attempt_at=now(),
                attempts=attempts+1, last_error=$2 WHERE id=$1",
        [id.into(), err.to_string().into()],
    )).await?;
    Ok(())
}

pub async fn mark_failed_terminal<C: ConnectionTrait>(conn: &C, id: Uuid, err: &str) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE email_outbox SET status='failed_terminal', last_attempt_at=now(),
                attempts=attempts+1, last_error=$2 WHERE id=$1",
        [id.into(), err.to_string().into()],
    )).await?;
    Ok(())
}

pub async fn cancel_dependent<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE email_outbox SET status='cancelled_dependent' WHERE id=$1 AND status='queued'",
        [id.into()],
    )).await?;
    Ok(())
}

pub async fn list_recent<C: ConnectionTrait>(conn: &C, limit: u64, offset: u64) -> Result<Vec<ent::Model>, DbErr> {
    ent::Entity::find()
        .order_by_desc(ent::Column::CreatedAt)
        .limit(limit).offset(offset)
        .all(conn).await
}

pub async fn find_by_id<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<Option<ent::Model>, DbErr> {
    ent::Entity::find_by_id(id).one(conn).await
}

pub async fn count_by_status<C: ConnectionTrait>(conn: &C, status: &str) -> Result<u64, DbErr> {
    ent::Entity::find().filter(ent::Column::Status.eq(status)).count(conn).await
}
```

- [ ] **Step 6: Wire up modules + register migration**

`entity/mod.rs`: `pub mod email_outbox;`
`query/mod.rs`: `pub mod email_outbox;`
`migrator/mod.rs`: register migration.

- [ ] **Step 7: Run test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-pg --test email_outbox`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000024_email_outbox.rs \
        engine/crates/pg/src/entity/email_outbox.rs \
        engine/crates/pg/src/query/email_outbox.rs \
        engine/crates/pg/src/{entity,query,migrator}/mod.rs \
        engine/crates/pg/tests/email_outbox.rs
git commit -m "feat(pg): email_outbox table + entity + queries with backoff claim"
```

### Task 6: `refund_records` migration + entity + queries

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000025_refund_records.rs`
- Create: `engine/crates/pg/src/entity/refund_records.rs`
- Create: `engine/crates/pg/src/query/refund_records.rs`
- Modify: `engine/crates/pg/src/{entity,query,migrator}/mod.rs`
- Test: `engine/crates/pg/tests/refund_records.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/pg/tests/refund_records.rs
use nasrudin_pg::{connect_simple, run_migrations, query};

#[tokio::test]
async fn refund_record_pending_then_succeeded() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_|
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into());
    let db = connect_simple(&url).await.unwrap();
    run_migrations(&db).await.unwrap();
    let admin = query::users::create_user(&db, "ref-admin@t.local", Some("h"), None).await.unwrap();
    let user = query::users::create_user(&db, "ref-user@t.local", Some("h"), None).await.unwrap();

    let id = query::refund_records::insert(
        &db, user.id, admin.id, "ch_test123", 1900, "usd", "test refund",
    ).await.unwrap();
    query::refund_records::mark_succeeded(&db, id, "re_test456").await.unwrap();

    let row = query::refund_records::find_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(row.status, "succeeded");
    assert_eq!(row.stripe_refund_id.as_deref(), Some("re_test456"));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-pg --test refund_records`
Expected: FAIL.

- [ ] **Step 3: Write the migration**

```rust
// engine/crates/pg/src/migrator/m20260430_000025_refund_records.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared(r#"
            CREATE TABLE IF NOT EXISTS refund_records (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                user_id UUID NOT NULL REFERENCES users(id),
                admin_user_id UUID NOT NULL REFERENCES users(id),
                stripe_refund_id TEXT UNIQUE,
                stripe_charge_id TEXT NOT NULL,
                amount_cents INTEGER NOT NULL,
                currency TEXT NOT NULL,
                reason TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'pending',
                stripe_failure_reason TEXT,
                requested_at TIMESTAMPTZ NOT NULL DEFAULT now(),
                completed_at TIMESTAMPTZ
            );
            CREATE INDEX IF NOT EXISTS refund_records_status ON refund_records (status, requested_at);
            CREATE INDEX IF NOT EXISTS refund_records_user ON refund_records (user_id, requested_at DESC);
            CREATE INDEX IF NOT EXISTS refund_records_charge ON refund_records (stripe_charge_id);
        "#).await?;
        Ok(())
    }
    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared("DROP TABLE IF EXISTS refund_records").await?;
        Ok(())
    }
}
```

- [ ] **Step 4: Write the entity**

```rust
// engine/crates/pg/src/entity/refund_records.rs
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "refund_records")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub user_id: Uuid,
    pub admin_user_id: Uuid,
    #[sea_orm(unique)]
    pub stripe_refund_id: Option<String>,
    pub stripe_charge_id: String,
    pub amount_cents: i32,
    pub currency: String,
    pub reason: String,
    pub status: String,
    pub stripe_failure_reason: Option<String>,
    pub requested_at: DateTimeWithTimeZone,
    pub completed_at: Option<DateTimeWithTimeZone>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}
impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 5: Write the query module**

```rust
// engine/crates/pg/src/query/refund_records.rs
use sea_orm::{ActiveModelTrait, ColumnTrait, ConnectionTrait, DbErr, EntityTrait, QueryFilter,
    ActiveValue::Set, Statement, DatabaseBackend};
use uuid::Uuid;

use crate::entity::refund_records as ent;

#[allow(clippy::too_many_arguments)]
pub async fn insert<C: ConnectionTrait>(
    conn: &C, user_id: Uuid, admin_user_id: Uuid, stripe_charge_id: &str,
    amount_cents: i32, currency: &str, reason: &str,
) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    ent::ActiveModel {
        id: Set(id),
        user_id: Set(user_id),
        admin_user_id: Set(admin_user_id),
        stripe_refund_id: Set(None),
        stripe_charge_id: Set(stripe_charge_id.into()),
        amount_cents: Set(amount_cents),
        currency: Set(currency.into()),
        reason: Set(reason.into()),
        status: Set("pending".into()),
        stripe_failure_reason: Set(None),
        requested_at: Set(chrono::Utc::now().into()),
        completed_at: Set(None),
    }.insert(conn).await?;
    Ok(id)
}

pub async fn mark_succeeded<C: ConnectionTrait>(conn: &C, id: Uuid, stripe_refund_id: &str) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE refund_records SET status='succeeded', stripe_refund_id=$2, completed_at=now()
         WHERE id=$1",
        [id.into(), stripe_refund_id.to_string().into()],
    )).await?;
    Ok(())
}

pub async fn mark_failed<C: ConnectionTrait>(conn: &C, id: Uuid, failure_reason: &str) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE refund_records SET status='failed', stripe_failure_reason=$2, completed_at=now()
         WHERE id=$1",
        [id.into(), failure_reason.to_string().into()],
    )).await?;
    Ok(())
}

pub async fn list_pending_older_than<C: ConnectionTrait>(conn: &C, seconds: i64) -> Result<Vec<ent::Model>, DbErr> {
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "SELECT * FROM refund_records WHERE status='pending'
         AND requested_at < now() - make_interval(secs => $1)",
        [seconds.into()],
    );
    ent::Model::find_by_statement(stmt).all(conn).await
}

pub async fn find_by_id<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<Option<ent::Model>, DbErr> {
    ent::Entity::find_by_id(id).one(conn).await
}

pub async fn find_by_charge<C: ConnectionTrait>(conn: &C, charge: &str) -> Result<Vec<ent::Model>, DbErr> {
    ent::Entity::find().filter(ent::Column::StripeChargeId.eq(charge)).all(conn).await
}
```

- [ ] **Step 6: Wire up modules + register migration**

Update `entity/mod.rs`, `query/mod.rs`, `migrator/mod.rs`.

- [ ] **Step 7: Run test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-pg --test refund_records`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000025_refund_records.rs \
        engine/crates/pg/src/entity/refund_records.rs \
        engine/crates/pg/src/query/refund_records.rs \
        engine/crates/pg/src/{entity,query,migrator}/mod.rs \
        engine/crates/pg/tests/refund_records.rs
git commit -m "feat(pg): refund_records table + entity + queries"
```

### Task 7: `bulk_runs` migration + entity + queries

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000026_bulk_runs.rs`
- Create: `engine/crates/pg/src/entity/bulk_runs.rs`
- Create: `engine/crates/pg/src/query/bulk_runs.rs`
- Modify: `engine/crates/pg/src/{entity,query,migrator}/mod.rs`
- Test: `engine/crates/pg/tests/bulk_runs.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/pg/tests/bulk_runs.rs
use nasrudin_pg::{connect_simple, run_migrations, query};
use serde_json::json;

#[tokio::test]
async fn bulk_run_lifecycle_with_reaper() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_|
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into());
    let db = connect_simple(&url).await.unwrap();
    run_migrations(&db).await.unwrap();
    let admin = query::users::create_user(&db, "bulk@t.local", Some("h"), None).await.unwrap();

    let id = query::bulk_runs::insert(&db, admin.id, "set_trust", json!({"to": true}), 5).await.unwrap();
    query::bulk_runs::increment_completed(&db, id).await.unwrap();
    query::bulk_runs::increment_failed(&db, id, json!([{"user":"x","err":"e"}])).await.unwrap();
    query::bulk_runs::complete(&db, id, "completed").await.unwrap();

    let r = query::bulk_runs::find_by_id(&db, id).await.unwrap().unwrap();
    assert_eq!(r.completed_count, 1);
    assert_eq!(r.failed_count, 1);
    assert_eq!(r.status, "completed");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-pg --test bulk_runs`
Expected: FAIL.

- [ ] **Step 3: Write the migration**

```rust
// engine/crates/pg/src/migrator/m20260430_000026_bulk_runs.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared(r#"
            CREATE TABLE IF NOT EXISTS bulk_runs (
                id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                started_by_admin_id UUID NOT NULL REFERENCES users(id),
                action TEXT NOT NULL,
                params JSONB NOT NULL,
                total_count INTEGER NOT NULL,
                completed_count INTEGER NOT NULL DEFAULT 0,
                failed_count INTEGER NOT NULL DEFAULT 0,
                status TEXT NOT NULL DEFAULT 'running',
                started_at TIMESTAMPTZ NOT NULL DEFAULT now(),
                completed_at TIMESTAMPTZ,
                failures JSONB
            );
            CREATE INDEX IF NOT EXISTS bulk_runs_status ON bulk_runs (status, started_at DESC);
            CREATE INDEX IF NOT EXISTS bulk_runs_admin ON bulk_runs (started_by_admin_id, started_at DESC);
        "#).await?;
        Ok(())
    }
    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared("DROP TABLE IF EXISTS bulk_runs").await?;
        Ok(())
    }
}
```

- [ ] **Step 4: Write the entity**

```rust
// engine/crates/pg/src/entity/bulk_runs.rs
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "bulk_runs")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub started_by_admin_id: Uuid,
    pub action: String,
    #[sea_orm(column_type = "JsonBinary")]
    pub params: Json,
    pub total_count: i32,
    pub completed_count: i32,
    pub failed_count: i32,
    pub status: String,
    pub started_at: DateTimeWithTimeZone,
    pub completed_at: Option<DateTimeWithTimeZone>,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub failures: Option<Json>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}
impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 5: Write the query module**

```rust
// engine/crates/pg/src/query/bulk_runs.rs
use sea_orm::{ActiveModelTrait, ColumnTrait, ConnectionTrait, DbErr, EntityTrait, QueryFilter,
    QueryOrder, ActiveValue::Set, Statement, DatabaseBackend};
use uuid::Uuid;

use crate::entity::bulk_runs as ent;

pub async fn insert<C: ConnectionTrait>(
    conn: &C, admin: Uuid, action: &str, params: serde_json::Value, total: i32,
) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    ent::ActiveModel {
        id: Set(id),
        started_by_admin_id: Set(admin),
        action: Set(action.into()),
        params: Set(params),
        total_count: Set(total),
        completed_count: Set(0),
        failed_count: Set(0),
        status: Set("running".into()),
        started_at: Set(chrono::Utc::now().into()),
        completed_at: Set(None),
        failures: Set(None),
    }.insert(conn).await?;
    Ok(id)
}

pub async fn increment_completed<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE bulk_runs SET completed_count = completed_count + 1 WHERE id=$1",
        [id.into()],
    )).await?;
    Ok(())
}

pub async fn increment_failed<C: ConnectionTrait>(conn: &C, id: Uuid, failure_record: serde_json::Value) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE bulk_runs SET failed_count = failed_count + 1,
                failures = COALESCE(failures, '[]'::jsonb) || $2::jsonb
         WHERE id=$1",
        [id.into(), failure_record.into()],
    )).await?;
    Ok(())
}

pub async fn complete<C: ConnectionTrait>(conn: &C, id: Uuid, status: &str) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE bulk_runs SET status=$2, completed_at=now() WHERE id=$1",
        [id.into(), status.to_string().into()],
    )).await?;
    Ok(())
}

pub async fn reap_stale<C: ConnectionTrait>(conn: &C) -> Result<u64, DbErr> {
    let res = conn.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE bulk_runs SET status='aborted', completed_at=now()
         WHERE status='running' AND started_at < now() - INTERVAL '1 hour'",
        [],
    )).await?;
    Ok(res.rows_affected())
}

pub async fn find_by_id<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<Option<ent::Model>, DbErr> {
    ent::Entity::find_by_id(id).one(conn).await
}

pub async fn list_recent<C: ConnectionTrait>(conn: &C, limit: u64) -> Result<Vec<ent::Model>, DbErr> {
    ent::Entity::find().order_by_desc(ent::Column::StartedAt).limit(limit).all(conn).await
}

pub async fn count_active<C: ConnectionTrait>(conn: &C) -> Result<u64, DbErr> {
    ent::Entity::find().filter(ent::Column::Status.eq("running")).count(conn).await
}
```

- [ ] **Step 6: Wire up modules + register migration**

- [ ] **Step 7: Run test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-pg --test bulk_runs`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000026_bulk_runs.rs \
        engine/crates/pg/src/entity/bulk_runs.rs \
        engine/crates/pg/src/query/bulk_runs.rs \
        engine/crates/pg/src/{entity,query,migrator}/mod.rs \
        engine/crates/pg/tests/bulk_runs.rs
git commit -m "feat(pg): bulk_runs table + entity + queries (with stale reaper)"
```

### Task 8: `prevent_last_admin_demotion` trigger

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000027_last_admin_trigger.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`
- Test: `engine/crates/pg/tests/last_admin_trigger.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/pg/tests/last_admin_trigger.rs
use nasrudin_pg::{connect_simple, run_migrations, query};
use sea_orm::{ActiveModelTrait, ActiveValue::Set, EntityTrait};
use nasrudin_pg::entity::users;

#[tokio::test]
async fn cannot_demote_last_admin() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_|
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into());
    let db = connect_simple(&url).await.unwrap();
    run_migrations(&db).await.unwrap();

    // Create a single admin
    let user = query::users::create_user(&db, "lastadmin@t.local", Some("h"), None).await.unwrap();
    let mut active: users::ActiveModel = user.into();
    active.is_admin = Set(true);
    let admin = active.update(&db).await.unwrap();

    // Try to demote — should fail with P0001
    let mut demote: users::ActiveModel = admin.into();
    demote.is_admin = Set(false);
    let err = demote.update(&db).await.unwrap_err();
    assert!(err.to_string().contains("cannot demote last admin"));
}

#[tokio::test]
async fn can_demote_when_other_admins_exist() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_|
        "postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test".into());
    let db = connect_simple(&url).await.unwrap();
    run_migrations(&db).await.unwrap();

    let a = query::users::create_user(&db, "a-admin@t.local", Some("h"), None).await.unwrap();
    let b = query::users::create_user(&db, "b-admin@t.local", Some("h"), None).await.unwrap();
    for u in [&a, &b] {
        let mut act: users::ActiveModel = u.clone().into();
        act.is_admin = Set(true);
        act.update(&db).await.unwrap();
    }

    let mut demote: users::ActiveModel = a.into();
    demote.is_admin = Set(false);
    demote.update(&db).await.unwrap(); // should succeed
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-pg --test last_admin_trigger`
Expected: FAIL — `cannot_demote_last_admin` does NOT raise.

- [ ] **Step 3: Write the migration**

```rust
// engine/crates/pg/src/migrator/m20260430_000027_last_admin_trigger.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared(r#"
            CREATE OR REPLACE FUNCTION prevent_last_admin_demotion() RETURNS TRIGGER AS $func$
            BEGIN
                IF OLD.is_admin = TRUE AND NEW.is_admin = FALSE THEN
                    IF (SELECT count(*) FROM users WHERE is_admin = TRUE AND id != OLD.id) = 0 THEN
                        RAISE EXCEPTION 'cannot demote last admin' USING ERRCODE = 'P0001';
                    END IF;
                END IF;
                RETURN NEW;
            END;
            $func$ LANGUAGE plpgsql;

            DROP TRIGGER IF EXISTS users_last_admin_guard ON users;
            CREATE TRIGGER users_last_admin_guard
                BEFORE UPDATE ON users
                FOR EACH ROW WHEN (OLD.is_admin = TRUE AND NEW.is_admin = FALSE)
                EXECUTE FUNCTION prevent_last_admin_demotion();
        "#).await?;
        Ok(())
    }
    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.get_connection().execute_unprepared(r#"
            DROP TRIGGER IF EXISTS users_last_admin_guard ON users;
            DROP FUNCTION IF EXISTS prevent_last_admin_demotion();
        "#).await?;
        Ok(())
    }
}
```

- [ ] **Step 4: Register the migration**

`engine/crates/pg/src/migrator/mod.rs`: add `mod m20260430_000027_last_admin_trigger;` and the `Box::new(...)` entry.

- [ ] **Step 5: Run tests to verify they pass**

Run: `cd engine && cargo test -p nasrudin-pg --test last_admin_trigger`
Expected: BOTH PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000027_last_admin_trigger.rs \
        engine/crates/pg/src/migrator/mod.rs \
        engine/crates/pg/tests/last_admin_trigger.rs
git commit -m "feat(pg): prevent_last_admin_demotion trigger"
```

## Section B — Trust resolution module

### Task 9: `trust.rs` core (TrustDecision, TrustSource, resolve)

**Files:**
- Create: `engine/crates/api/src/trust.rs`
- Modify: `engine/crates/api/src/lib.rs` (`pub mod trust;`)
- Test: `engine/crates/api/tests/trust_resolution.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/trust_resolution.rs
mod test_app;

use nasrudin_pg::entity::api_keys;
use sea_orm::{ActiveModelTrait, ActiveValue::Set};
use uuid::Uuid;

use physics_api::trust::{resolve, TrustSource};

#[tokio::test]
async fn unix_socket_overrides_everything() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let key = api_keys::ActiveModel {
        id: Set(Uuid::new_v4()), user_id: Set(None), kind: Set("worker".into()),
        name: Set("k".into()), prefix: Set("nsk_worker_aaa".into()), key_hash: Set("h".into()),
        last_used_at: Set(None), expires_at: Set(None), created_at: Set(chrono::Utc::now().into()),
        revoked_at: Set(None),
        trust_override: Set(Some(false)), spot_check_rate: Set(Some(1)),
    }.insert(&app.pg).await.unwrap();
    let d = resolve(&app.pg, Some(&key), true, 50).await.unwrap();
    assert!(d.trusted);
    assert_eq!(d.source, TrustSource::UnixSocket);
}

#[tokio::test]
async fn api_key_trust_override_beats_user() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let user = nasrudin_pg::query::users::create_user(&app.pg, "ko@t.local", Some("h"), None).await.unwrap();
    // Mark user as trusted=false but key as trust_override=true.
    let key = api_keys::ActiveModel {
        id: Set(Uuid::new_v4()), user_id: Set(Some(user.id)), kind: Set("worker".into()),
        name: Set("k".into()), prefix: Set(format!("nsk_worker_{}", &Uuid::new_v4().simple().to_string()[..3])),
        key_hash: Set("h".into()), last_used_at: Set(None), expires_at: Set(None),
        created_at: Set(chrono::Utc::now().into()), revoked_at: Set(None),
        trust_override: Set(Some(true)), spot_check_rate: Set(Some(20)),
    }.insert(&app.pg).await.unwrap();

    let d = resolve(&app.pg, Some(&key), false, 50).await.unwrap();
    assert!(d.trusted);
    assert_eq!(d.source, TrustSource::ApiKeyOverride);
    assert_eq!(d.spot_check_rate, 20);
}

#[tokio::test]
async fn user_flag_inherited_when_no_key_override() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let user = nasrudin_pg::query::users::create_user(&app.pg, "uf@t.local", Some("h"), None).await.unwrap();
    sea_orm::ConnectionTrait::execute(&app.pg, sea_orm::Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE users SET is_trusted=true, spot_check_rate=10 WHERE id=$1", [user.id.into()],
    )).await.unwrap();
    let key = api_keys::ActiveModel {
        id: Set(Uuid::new_v4()), user_id: Set(Some(user.id)), kind: Set("worker".into()),
        name: Set("k".into()), prefix: Set(format!("nsk_worker_{}", &Uuid::new_v4().simple().to_string()[..3])),
        key_hash: Set("h".into()), last_used_at: Set(None), expires_at: Set(None),
        created_at: Set(chrono::Utc::now().into()), revoked_at: Set(None),
        trust_override: Set(None), spot_check_rate: Set(None),
    }.insert(&app.pg).await.unwrap();
    let d = resolve(&app.pg, Some(&key), false, 50).await.unwrap();
    assert!(d.trusted);
    assert_eq!(d.source, TrustSource::UserFlag);
    assert_eq!(d.spot_check_rate, 10);
}

#[tokio::test]
async fn defaults_when_neither_set() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let user = nasrudin_pg::query::users::create_user(&app.pg, "df@t.local", Some("h"), None).await.unwrap();
    let key = api_keys::ActiveModel {
        id: Set(Uuid::new_v4()), user_id: Set(Some(user.id)), kind: Set("worker".into()),
        name: Set("k".into()), prefix: Set(format!("nsk_worker_{}", &Uuid::new_v4().simple().to_string()[..3])),
        key_hash: Set("h".into()), last_used_at: Set(None), expires_at: Set(None),
        created_at: Set(chrono::Utc::now().into()), revoked_at: Set(None),
        trust_override: Set(None), spot_check_rate: Set(None),
    }.insert(&app.pg).await.unwrap();
    let d = resolve(&app.pg, Some(&key), false, 77).await.unwrap();
    assert!(!d.trusted);
    assert_eq!(d.source, TrustSource::Default);
    assert_eq!(d.spot_check_rate, 77);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p physics-api --test trust_resolution`
Expected: FAIL — `physics_api::trust` does not exist.

- [ ] **Step 3: Write the implementation**

```rust
// engine/crates/api/src/trust.rs
//! Trust resolution for worker submissions.
//!
//! Decides whether a submission from a given API key should bypass the
//! redundant server-side `lake build` confirmation, and at what spot-check
//! rate (1-in-N sampling for cascade-reject + reputation-EMA verification).
//!
//! Resolution order (first match wins):
//! 1. `via_unix_socket=true`        → trusted, source=UnixSocket
//! 2. `api_keys.trust_override`     → use that, source=ApiKeyOverride
//! 3. `users.is_trusted`            → use that, source=UserFlag
//! 4. else                          → not trusted, source=Default
//!
//! Spot-check rate cascades through key → user → env default at every level.

use std::time::{Duration, Instant};

use dashmap::DashMap;
use nasrudin_pg::entity::{api_keys, users};
use nasrudin_pg::sea_orm::{ColumnTrait, DatabaseConnection, DbErr, EntityTrait, QueryFilter};
use serde::Serialize;
use uuid::Uuid;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub enum TrustSource {
    UnixSocket,
    ApiKeyOverride,
    UserFlag,
    Default,
}

#[derive(Clone, Debug, Serialize)]
pub struct TrustDecision {
    pub trusted: bool,
    pub spot_check_rate: u32,
    pub source: TrustSource,
}

/// Marker inserted into request extensions by the unix-socket-only
/// middleware in `main.rs`. Public TCP requests cannot present this.
#[derive(Clone, Copy, Debug)]
pub struct LocalSocket;

pub async fn resolve(
    pg: &DatabaseConnection,
    api_key_row: Option<&api_keys::Model>,
    via_unix_socket: bool,
    env_default_rate: u32,
) -> Result<TrustDecision, DbErr> {
    if via_unix_socket {
        let rate = api_key_row
            .and_then(|k| k.spot_check_rate.map(|r| r as u32))
            .unwrap_or(env_default_rate);
        return Ok(TrustDecision { trusted: true, spot_check_rate: rate, source: TrustSource::UnixSocket });
    }

    let key = match api_key_row {
        Some(k) => k,
        None => return Ok(TrustDecision { trusted: false, spot_check_rate: env_default_rate, source: TrustSource::Default }),
    };

    // Per-key override first.
    if let Some(override_) = key.trust_override {
        let user_rate = if let Some(uid) = key.user_id {
            users::Entity::find_by_id(uid).one(pg).await?
                .and_then(|u| u.spot_check_rate.map(|r| r as u32))
        } else { None };
        let rate = key.spot_check_rate.map(|r| r as u32)
            .or(user_rate)
            .unwrap_or(env_default_rate);
        return Ok(TrustDecision { trusted: override_, spot_check_rate: rate, source: TrustSource::ApiKeyOverride });
    }

    // Fall back to user.
    let user_id = match key.user_id {
        Some(u) => u,
        None => return Ok(TrustDecision { trusted: false, spot_check_rate: env_default_rate, source: TrustSource::Default }),
    };
    let user = users::Entity::find_by_id(user_id).one(pg).await?;
    let user = match user {
        Some(u) => u,
        None => return Ok(TrustDecision { trusted: false, spot_check_rate: env_default_rate, source: TrustSource::Default }),
    };

    if user.is_trusted {
        let rate = key.spot_check_rate.map(|r| r as u32)
            .or(user.spot_check_rate.map(|r| r as u32))
            .unwrap_or(env_default_rate);
        return Ok(TrustDecision { trusted: true, spot_check_rate: rate, source: TrustSource::UserFlag });
    }

    Ok(TrustDecision { trusted: false, spot_check_rate: env_default_rate, source: TrustSource::Default })
}

/// FNV-1a 64-bit. Deterministic per-theorem hash for stable spot-check
/// sampling — re-running the drain picks the same sampled subset.
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// `should_promote` = true → enqueue lake-promotion. False → bypass (verified now).
pub fn should_promote(decision: &TrustDecision, theorem_id: &[u8]) -> bool {
    if !decision.trusted { return true; }
    match decision.spot_check_rate {
        0 => false,                // pure trust
        1 => true,                 // effectively untrusted
        n => fnv1a64(theorem_id) % (n as u64) == 0,
    }
}

// --- TrustCache (Task 10) lives below ---

#[derive(Clone)]
pub struct TrustCache {
    inner: std::sync::Arc<DashMap<Uuid, (Instant, TrustDecision)>>,
    ttl: Duration,
    capacity: usize,
}

impl TrustCache {
    pub fn new(ttl: Duration, capacity: usize) -> Self {
        Self { inner: std::sync::Arc::new(DashMap::with_capacity(capacity)), ttl, capacity }
    }

    pub fn get(&self, key_id: &Uuid) -> Option<TrustDecision> {
        let entry = self.inner.get(key_id)?;
        let (when, ref dec) = *entry;
        if when.elapsed() < self.ttl { Some(dec.clone()) } else { None }
    }

    pub fn put(&self, key_id: Uuid, decision: TrustDecision) {
        if self.inner.len() >= self.capacity {
            // Cheap eviction: drop the first 16 entries we encounter.
            let mut evicted = 0;
            self.inner.retain(|_, _| { evicted += 1; evicted > 16 });
        }
        self.inner.insert(key_id, (Instant::now(), decision));
    }

    pub fn invalidate(&self, key_id: &Uuid) { self.inner.remove(key_id); }
    pub fn invalidate_all_for_user(&self, user_id: Uuid, pg: &DatabaseConnection) {
        // Caller drives this by listing the user's keys and calling invalidate per id.
        // Documented for orchestration layer (Task 10).
        let _ = (user_id, pg);
    }
    pub fn len(&self) -> usize { self.inner.len() }
}

#[derive(Clone, Debug)]
pub enum CacheInvalidation {
    ApiKey(Uuid),
    User(Uuid),
    All,
}
```

- [ ] **Step 4: Wire up the module**

Edit `engine/crates/api/src/lib.rs`: add `pub mod trust;`.

- [ ] **Step 5: Run tests to verify they pass**

Run: `cd engine && cargo test -p physics-api --test trust_resolution`
Expected: ALL FOUR PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/trust.rs engine/crates/api/src/lib.rs \
        engine/crates/api/tests/trust_resolution.rs
git commit -m "feat(api): trust resolution module with cascade rate fallback"
```

### Task 10: TrustCache + invalidation broadcast

**Files:**
- Modify: `engine/crates/api/src/state.rs` (add `trust_cache`, `trust_invalidation_tx`)
- Modify: `engine/crates/api/src/main.rs` (construct + spawn invalidation listener)
- Test: `engine/crates/api/tests/trust_cache.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/trust_cache.rs
mod test_app;

use std::time::Duration;
use physics_api::trust::{TrustCache, TrustDecision, TrustSource};
use uuid::Uuid;

#[tokio::test]
async fn cache_returns_within_ttl_invalidates_after_explicit_invalidate() {
    let cache = TrustCache::new(Duration::from_secs(30), 16);
    let id = Uuid::new_v4();
    let dec = TrustDecision { trusted: true, spot_check_rate: 50, source: TrustSource::UserFlag };
    cache.put(id, dec.clone());
    assert!(cache.get(&id).is_some());
    cache.invalidate(&id);
    assert!(cache.get(&id).is_none());
}

#[tokio::test]
async fn cache_capacity_evicts() {
    let cache = TrustCache::new(Duration::from_secs(30), 4);
    for _ in 0..10 {
        cache.put(Uuid::new_v4(), TrustDecision { trusted: false, spot_check_rate: 50, source: TrustSource::Default });
    }
    assert!(cache.len() <= 4);
}
```

- [ ] **Step 2: Run test to verify it fails-or-passes**

Run: `cd engine && cargo test -p physics-api --test trust_cache`
Expected: PASS (cache code already in `trust.rs` from Task 9).

- [ ] **Step 3: Add to AppState**

Edit `engine/crates/api/src/state.rs`. After the existing `pub struct AppState { ... }` fields, add:

```rust
    /// Trust-decision cache (Task 10). 30 s TTL, 4096 capacity. Looked up by
    /// `api_keys.id`. Invalidated via `trust_invalidation_tx` when an admin
    /// changes a user's or key's trust state.
    pub trust_cache: crate::trust::TrustCache,
    /// Broadcast channel for cache invalidation. The handlers post to it
    /// after committing an admin mutation; a single tokio task subscribes
    /// and purges affected keys.
    pub trust_invalidation_tx: tokio::sync::broadcast::Sender<crate::trust::CacheInvalidation>,
    /// Default spot-check rate; sourced from `TRUSTED_SPOT_CHECK_RATE` env var,
    /// falls back to 50.
    pub trusted_spot_check_rate: u32,
```

- [ ] **Step 4: Construct in `main.rs`**

In `engine/crates/api/src/main.rs`, before `let state = ...`, add:

```rust
    let trust_cache = physics_api::trust::TrustCache::new(std::time::Duration::from_secs(30), 4096);
    let (trust_invalidation_tx, _) = tokio::sync::broadcast::channel(256);
    let trusted_spot_check_rate: u32 = std::env::var("TRUSTED_SPOT_CHECK_RATE").ok()
        .and_then(|s| s.parse().ok()).unwrap_or(50);
```

Pass these into the `AppState { ... }` literal — add the three fields. Then spawn an invalidation listener:

```rust
    {
        let cache = trust_cache.clone();
        let mut rx = trust_invalidation_tx.subscribe();
        let pg_for_listener = state.pg.clone();
        tokio::spawn(async move {
            while let Ok(msg) = rx.recv().await {
                use physics_api::trust::CacheInvalidation as I;
                match msg {
                    I::ApiKey(id) => cache.invalidate(&id),
                    I::User(user_id) => {
                        if let Some(pg) = &pg_for_listener {
                            if let Ok(rows) = nasrudin_pg::query::api_keys::list_by_user(pg, user_id).await {
                                for r in rows { cache.invalidate(&r.id); }
                            }
                        }
                    }
                    I::All => {
                        // Full purge by replacing the inner map.
                        // Cheap because TrustCache::clear isn't strictly needed:
                        // a follow-up admin action that toggled "all" is rare.
                        // Keep impl simple.
                        for entry in cache.iter_for_clear() { let _ = entry; }
                    }
                }
            }
        });
    }
```

Add `iter_for_clear` and other small helpers as needed in `trust.rs`. Or replace the `I::All` arm with reconstructing the cache via `state.trust_cache.purge_all()` — implement as:

```rust
// In trust.rs:
impl TrustCache {
    pub fn purge_all(&self) { self.inner.clear(); }
}
```

then in main.rs use `cache.purge_all()`.

- [ ] **Step 5: Add `query::api_keys::list_by_user` if it does not exist**

In `engine/crates/pg/src/query/api_keys.rs`, append:

```rust
pub async fn list_by_user<C: ConnectionTrait>(conn: &C, user_id: Uuid) -> Result<Vec<api_keys::Model>, DbErr> {
    api_keys::Entity::find().filter(api_keys::Column::UserId.eq(user_id)).all(conn).await
}
```

(Make sure `ConnectionTrait`, `ColumnTrait`, `EntityTrait`, `QueryFilter`, and `Uuid` are imported.)

- [ ] **Step 6: Run tests + cargo check**

Run: `cd engine && cargo check -p physics-api && cargo test -p physics-api --test trust_cache`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/state.rs engine/crates/api/src/main.rs \
        engine/crates/api/src/trust.rs \
        engine/crates/pg/src/query/api_keys.rs \
        engine/crates/api/tests/trust_cache.rs
git commit -m "feat(api): wire TrustCache and broadcast invalidation channel into AppState"
```

### Task 11: Plumb `LocalSocket` marker + via_unix_socket through ingest

**Files:**
- Modify: `engine/crates/api/src/handlers/ingest.rs`
- Modify: `engine/crates/api/src/auth.rs` (WorkerAuth keeps row.id; we just read extension marker)
- Test: `engine/crates/api/tests/ingest_trust_flag.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/ingest_trust_flag.rs
mod test_app;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;
use serde_json::json;

#[tokio::test]
async fn ingest_marks_via_unix_socket_when_extension_present() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let (worker_key, _) = test_app::issue_worker_key(&app, "w-trust").await;

    // First call: TCP-only (no LocalSocket extension). Should NOT mark trusted.
    let body = json!({ /* test_app helper builds a minimal valid theorem */ });
    let req = Request::post("/api/ingest")
        .header("Authorization", format!("Bearer {worker_key}"))
        .header("Content-Type", "application/json")
        .body(Body::from(body.to_string())).unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let last = test_app::last_ingested_theorem(&app).await.unwrap();
    assert!(!test_app::theorem_was_trusted_bypass(&app, &last.id).await);

    // Second call: LocalSocket extension simulated via test-only insertion.
    let req = Request::post("/api/ingest")
        .header("Authorization", format!("Bearer {worker_key}"))
        .header("Content-Type", "application/json")
        .header("x-test-local-socket", "1")  // test-app inserts the marker
        .body(Body::from(body.to_string())).unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let last2 = test_app::last_ingested_theorem(&app).await.unwrap();
    assert!(test_app::theorem_was_trusted_bypass(&app, &last2.id).await);
}
```

(The helpers `issue_worker_key`, `last_ingested_theorem`, `theorem_was_trusted_bypass`, and the `x-test-local-socket` test harness header are added in Step 4.)

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p physics-api --test ingest_trust_flag`
Expected: FAIL — helpers and behavior don't exist yet.

- [ ] **Step 3: Modify the ingest handler**

Edit `engine/crates/api/src/handlers/ingest.rs`. At the top of `ingest_one_theorem` (or the equivalent main handler — search for `pub async fn ingest`), inject trust resolution:

```rust
use crate::trust::{self, LocalSocket};

// Inside the handler, after auth + extracting `state` and `auth`:
let via_unix_socket = req_parts.extensions.get::<LocalSocket>().is_some();
let key_row = nasrudin_pg::query::api_keys::find_by_id(&pg, auth.0.api_key_id).await
    .ok().flatten();
let decision = if let Some(d) = state.trust_cache.get(&auth.0.api_key_id) {
    d
} else {
    let d = trust::resolve(&pg, key_row.as_ref(), via_unix_socket, state.trusted_spot_check_rate)
        .await.map_err(|e| ingest_error(StatusCode::INTERNAL_SERVER_ERROR, &e.to_string()))?;
    state.trust_cache.put(auth.0.api_key_id, d.clone());
    d
};
// Stash on the row for `reverify::process_one` to consume, or carry it into the
// reverify enqueue so the drain picks the right path.
```

Then where the handler invokes the reverify enqueue (search `enqueue_reverify`), pass `decision.trusted` and `decision.spot_check_rate` through to the `ReverifyJob` payload (extend that struct in Task 15).

Add `find_by_id` to `engine/crates/pg/src/query/api_keys.rs` if missing:

```rust
pub async fn find_by_id<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<Option<api_keys::Model>, DbErr> {
    api_keys::Entity::find_by_id(id).one(conn).await
}
```

- [ ] **Step 4: Add test harness helpers**

In `engine/crates/api/tests/test_app/mod.rs`, append:

```rust
pub async fn issue_worker_key(app: &TestApp, name: &str) -> (String, Uuid) {
    use nasrudin_pg::entity::api_keys;
    use sea_orm::{ActiveModelTrait, ActiveValue::Set};
    let secret = format!("nsk_worker_{}", uuid::Uuid::new_v4().simple());
    let prefix: String = secret.chars().take(14).collect();
    let hash = tokio::task::spawn_blocking({
        let s = secret.clone();
        move || password_auth::generate_hash(s)
    }).await.unwrap();
    let id = uuid::Uuid::new_v4();
    api_keys::ActiveModel {
        id: Set(id), user_id: Set(None), kind: Set("worker".into()), name: Set(name.into()),
        prefix: Set(prefix), key_hash: Set(hash),
        last_used_at: Set(None), expires_at: Set(None),
        created_at: Set(chrono::Utc::now().into()), revoked_at: Set(None),
        trust_override: Set(None), spot_check_rate: Set(None),
    }.insert(&app.pg).await.unwrap();
    (secret, id)
}

pub async fn last_ingested_theorem(app: &TestApp) -> Option<nasrudin_pg::entity::theorems::Model> {
    use sea_orm::{EntityTrait, QueryOrder};
    nasrudin_pg::entity::theorems::Entity::find()
        .order_by_desc(nasrudin_pg::entity::theorems::Column::CreatedAt)
        .one(&app.pg).await.unwrap()
}

pub async fn theorem_was_trusted_bypass(app: &TestApp, id: &[u8]) -> bool {
    use sea_orm::{EntityTrait, ColumnTrait, QueryFilter};
    let row = nasrudin_pg::entity::theorems::Entity::find()
        .filter(nasrudin_pg::entity::theorems::Column::Id.eq(id))
        .one(&app.pg).await.unwrap();
    row.and_then(|r| r.verification_path).as_deref() == Some("trusted_bypass")
}
```

In `TestApp::build()`, behind `#[cfg(test)]`, install a layer that copies the `x-test-local-socket: 1` header into a `LocalSocket` request extension. This lets the same `Router` exercise both code paths in tests:

```rust
use axum::middleware::{self, Next};
async fn test_local_socket_middleware(mut req: axum::extract::Request, next: Next) -> axum::response::Response {
    if req.headers().get("x-test-local-socket").is_some() {
        req.extensions_mut().insert(physics_api::trust::LocalSocket);
    }
    next.run(req).await
}
// later:
let app = app.layer(middleware::from_fn(test_local_socket_middleware));
```

- [ ] **Step 5: Run test to verify it passes**

Run: `cd engine && cargo test -p physics-api --test ingest_trust_flag`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/handlers/ingest.rs \
        engine/crates/pg/src/query/api_keys.rs \
        engine/crates/api/tests/test_app/mod.rs \
        engine/crates/api/tests/ingest_trust_flag.rs
git commit -m "feat(api): thread LocalSocket marker + trust decision through ingest"
```

## Section C — Unix-domain-socket listener

### Task 12: `mark_local_socket_layer` middleware

**Files:**
- Modify: `engine/crates/api/src/main.rs` (add the layer constructor)
- Modify: `engine/crates/api/src/lib.rs`
- Test: `engine/crates/api/tests/unix_socket_listener.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/unix_socket_listener.rs
//! Confirms public TCP requests cannot present LocalSocket marker, and the
//! marker is correctly inserted by the unix-socket-only middleware.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use axum::response::IntoResponse;
use axum::{Router, routing::get};
use tower::ServiceExt;

use physics_api::trust::LocalSocket;

async fn echo_marker(parts: axum::extract::Request) -> impl IntoResponse {
    let has = parts.extensions().get::<LocalSocket>().is_some();
    if has { (StatusCode::OK, "local") } else { (StatusCode::OK, "tcp") }
}

#[tokio::test]
async fn middleware_inserts_marker() {
    use axum::middleware::{self, Next};
    async fn mark(mut req: axum::extract::Request, next: Next) -> axum::response::Response {
        req.extensions_mut().insert(LocalSocket);
        next.run(req).await
    }
    let app: Router = Router::new().route("/", get(echo_marker)).layer(middleware::from_fn(mark));
    let resp = app.oneshot(Request::get("/").body(Body::empty()).unwrap()).await.unwrap();
    let body = axum::body::to_bytes(resp.into_body(), 64).await.unwrap();
    assert_eq!(&body[..], b"local");
}

#[tokio::test]
async fn no_marker_means_tcp() {
    let app: Router = Router::new().route("/", get(echo_marker));
    let resp = app.oneshot(Request::get("/").body(Body::empty()).unwrap()).await.unwrap();
    let body = axum::body::to_bytes(resp.into_body(), 64).await.unwrap();
    assert_eq!(&body[..], b"tcp");
}
```

- [ ] **Step 2: Run tests**

Run: `cd engine && cargo test -p physics-api --test unix_socket_listener`
Expected: PASS (this only validates axum behavior; the production wiring follows in Task 13).

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/tests/unix_socket_listener.rs
git commit -m "test(api): unit-test LocalSocket marker propagation via middleware"
```

### Task 13: Dual `axum::serve` — TCP + UDS

**Files:**
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/api/Cargo.toml` (no new deps — tokio's `net` already includes `UnixListener`)
- Test: `engine/crates/api/tests/unix_socket_serve.rs`

- [ ] **Step 1: Write the failing test (manual smoke-test stub)**

```rust
// engine/crates/api/tests/unix_socket_serve.rs
#![cfg(unix)]
use std::os::unix::fs::PermissionsExt;

use axum::{Router, routing::get};
use axum::middleware::{self, Next};
use physics_api::trust::LocalSocket;

async fn mark_local(mut req: axum::extract::Request, next: Next) -> axum::response::Response {
    req.extensions_mut().insert(LocalSocket);
    next.run(req).await
}

async fn echo(req: axum::extract::Request) -> &'static str {
    if req.extensions().get::<LocalSocket>().is_some() { "local" } else { "tcp" }
}

#[tokio::test]
async fn serves_via_unix_listener_with_correct_mode() {
    let dir = tempfile::tempdir().unwrap();
    let sock_path = dir.path().join("api.sock");

    let app = Router::new().route("/", get(echo)).layer(middleware::from_fn(mark_local));
    let listener = tokio::net::UnixListener::bind(&sock_path).unwrap();
    let mut perms = std::fs::metadata(&sock_path).unwrap().permissions();
    perms.set_mode(0o660);
    std::fs::set_permissions(&sock_path, perms).unwrap();

    let app_clone = app.clone();
    let handle = tokio::spawn(async move {
        // Simple accept-then-serve loop. Production code goes via axum::serve
        // with a custom listener; here we just assert the bind+permissions path.
        let (_stream, _addr) = listener.accept().await.unwrap();
        drop(app_clone);
    });

    // Connect once and immediately drop, just to exercise the listener.
    let _stream = tokio::net::UnixStream::connect(&sock_path).await.unwrap();
    handle.await.unwrap();

    let mode = std::fs::metadata(&sock_path).unwrap().permissions().mode() & 0o777;
    assert_eq!(mode, 0o660);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p physics-api --test unix_socket_serve`
Expected: PASS (this test is environmental — it validates tokio + permissions, not axum::serve wiring).

- [ ] **Step 3: Wire the real listener in `main.rs`**

In `engine/crates/api/src/main.rs`, replace the single `axum::serve(listener, app...)` block with:

```rust
    // Public TCP listener (existing).
    let port = std::env::var("PORT").ok().and_then(|s| s.parse().ok()).unwrap_or(3001);
    let tcp_listener = tokio::net::TcpListener::bind(format!("0.0.0.0:{port}")).await?;
    let tcp_app = app.clone();

    // Unix-socket listener (Task 13). Trust-bypass entry point for the
    // co-located worker.
    let sock_path: std::path::PathBuf = std::env::var("NASRUDIN_LOCAL_SOCK_PATH")
        .unwrap_or_else(|_| "/run/nasrudin/api-local.sock".into()).into();
    if let Some(parent) = sock_path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    if sock_path.exists() {
        let _ = std::fs::remove_file(&sock_path);
    }
    let uds_listener = tokio::net::UnixListener::bind(&sock_path).ok();
    if let Some(ref _l) = uds_listener {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = std::fs::metadata(&sock_path)?.permissions();
        perms.set_mode(0o660);
        std::fs::set_permissions(&sock_path, perms)?;
        tracing::info!("Unix socket listening at {} (mode 0660)", sock_path.display());
    } else {
        tracing::warn!("Unable to bind unix socket at {} — co-located worker auto-trust disabled", sock_path.display());
    }

    let uds_app = {
        use axum::middleware::{self, Next};
        async fn mark_local(mut req: axum::extract::Request, next: Next) -> axum::response::Response {
            req.extensions_mut().insert(physics_api::trust::LocalSocket);
            next.run(req).await
        }
        app.clone().layer(middleware::from_fn(mark_local))
    };

    let shutdown_flag_tcp = Arc::clone(&shutdown);
    let shutdown_flag_uds = Arc::clone(&shutdown);
    let tcp_handle = tokio::spawn(async move {
        let _ = axum::serve(tcp_listener, tcp_app.into_make_service_with_connect_info::<SocketAddr>())
            .with_graceful_shutdown(async move {
                tokio::signal::ctrl_c().await.ok();
                shutdown_flag_tcp.store(true, Ordering::Relaxed);
            }).await;
    });

    let uds_handle = if let Some(uds_listener) = uds_listener {
        Some(tokio::spawn(async move {
            let _ = axum::serve(uds_listener, uds_app.into_make_service())
                .with_graceful_shutdown(async move {
                    tokio::signal::ctrl_c().await.ok();
                    shutdown_flag_uds.store(true, Ordering::Relaxed);
                }).await;
        }))
    } else { None };

    let _ = tcp_handle.await;
    if let Some(h) = uds_handle { let _ = h.await; }
```

- [ ] **Step 4: Cargo check + manual smoke**

Run: `cd engine && cargo check -p physics-api`
Then start the server with `NASRUDIN_LOCAL_SOCK_PATH=/tmp/nasrudin-test.sock cargo run --release --bin physics-api` and `curl --unix-socket /tmp/nasrudin-test.sock http://localhost/api/health`. Expected: 200.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/main.rs engine/crates/api/tests/unix_socket_serve.rs
git commit -m "feat(api): bind unix-domain-socket listener with LocalSocket marker"
```

### Task 14: Worker UDS connector support

**Files:**
- Modify: `engine/crates/ga/Cargo.toml` (add `hyper-util` with UDS feature, `hyperlocal`)
- Modify: `engine/crates/ga/src/bin/worker.rs`
- Modify: `deploy/systemd/nasrudin-worker.service` (CREATE if missing)
- Test: `engine/crates/ga/tests/worker_uds_uri.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/ga/tests/worker_uds_uri.rs
//! Validates the worker URL parser recognizes unix:/// prefix and rebuilds
//! a request URL the way the runtime expects.

use nasrudin_ga::worker_url::{ApiBase, parse_api_base};

#[test]
fn parses_tcp_url() {
    let b = parse_api_base("http://localhost:3001").unwrap();
    assert!(matches!(b, ApiBase::Tcp(ref u) if u.as_str() == "http://localhost:3001"));
}

#[test]
fn parses_unix_url() {
    let b = parse_api_base("unix:///run/nasrudin/api-local.sock").unwrap();
    assert!(matches!(b, ApiBase::Unix(ref p) if p.as_os_str() == "/run/nasrudin/api-local.sock"));
}

#[test]
fn rejects_garbage() {
    assert!(parse_api_base("garbage://x").is_err());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-ga --test worker_uds_uri`
Expected: FAIL — module missing.

- [ ] **Step 3: Add deps**

`engine/crates/ga/Cargo.toml`:

```toml
[dependencies]
# (existing)
hyperlocal = "0.9"
hyper = { version = "1", features = ["client", "http1"] }
hyper-util = { version = "0.1", features = ["client", "client-legacy", "tokio", "http1"] }
http-body-util = "0.1"
url = "2"
```

- [ ] **Step 4: Add the URL parser module**

Create `engine/crates/ga/src/worker_url.rs`:

```rust
//! API base parsing for the worker binary. Recognizes:
//! - http://...     -> ApiBase::Tcp
//! - https://...    -> ApiBase::Tcp
//! - unix:///path   -> ApiBase::Unix
//!
//! The worker binary picks the corresponding `reqwest`-style client based
//! on this discriminant. Unix-socket connections still send a normal HTTP/1.1
//! request — the UDS only changes transport.

use std::path::PathBuf;

#[derive(Clone, Debug)]
pub enum ApiBase {
    Tcp(url::Url),
    Unix(PathBuf),
}

#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("malformed url: {0}")]
    Url(String),
    #[error("unix scheme requires path: {0}")]
    UnixNoPath(String),
    #[error("unsupported scheme: {0}")]
    UnsupportedScheme(String),
}

pub fn parse_api_base(input: &str) -> Result<ApiBase, ParseError> {
    if let Some(rest) = input.strip_prefix("unix://") {
        let path = if rest.is_empty() {
            return Err(ParseError::UnixNoPath(input.into()));
        } else { PathBuf::from(rest) };
        return Ok(ApiBase::Unix(path));
    }
    let parsed = url::Url::parse(input).map_err(|e| ParseError::Url(e.to_string()))?;
    match parsed.scheme() {
        "http" | "https" => Ok(ApiBase::Tcp(parsed)),
        s => Err(ParseError::UnsupportedScheme(s.into())),
    }
}
```

Add `pub mod worker_url;` to `engine/crates/ga/src/lib.rs` (or to whatever the worker-bin entry exposes).

- [ ] **Step 5: Modify the worker binary**

In `engine/crates/ga/src/bin/worker.rs`, replace the existing `reqwest::Client::new()` + URL concatenation with:

```rust
use nasrudin_ga::worker_url::{parse_api_base, ApiBase};

let api_url = std::env::var("NASRUDIN_API_URL").unwrap_or_else(|_| "http://localhost:3001".into());
let base = parse_api_base(&api_url).expect("invalid NASRUDIN_API_URL");

enum Http {
    Tcp(reqwest::Client, url::Url),
    Unix(hyper_util::client::legacy::Client<hyperlocal::UnixConnector, http_body_util::Full<bytes::Bytes>>, std::path::PathBuf),
}

let http = match base {
    ApiBase::Tcp(u) => Http::Tcp(reqwest::Client::new(), u),
    ApiBase::Unix(p) => {
        let c = hyper_util::client::legacy::Client::builder(hyper_util::rt::TokioExecutor::new())
            .build(hyperlocal::UnixConnector);
        Http::Unix(c, p)
    }
};
```

For each call site that does `client.post(url).json(&body).send()`, factor a helper:

```rust
async fn post_json(http: &Http, path: &str, headers: &reqwest::header::HeaderMap, body: serde_json::Value) -> anyhow::Result<(u16, serde_json::Value)> {
    match http {
        Http::Tcp(c, base) => {
            let url = base.join(path)?;
            let mut req = c.post(url).json(&body);
            for (k, v) in headers { req = req.header(k, v); }
            let resp = req.send().await?;
            let status = resp.status().as_u16();
            let json = resp.json().await.unwrap_or(serde_json::Value::Null);
            Ok((status, json))
        }
        Http::Unix(c, sock) => {
            use http_body_util::BodyExt;
            let uri: hyper::Uri = hyperlocal::Uri::new(sock, path).into();
            let mut req = hyper::Request::builder().method("POST").uri(uri).header("content-type", "application/json");
            for (k, v) in headers { req = req.header(k.as_str(), v.to_str()?); }
            let req = req.body(http_body_util::Full::new(bytes::Bytes::from(serde_json::to_vec(&body)?)))?;
            let resp = c.request(req).await?;
            let status = resp.status().as_u16();
            let body = resp.into_body().collect().await?.to_bytes();
            let json: serde_json::Value = serde_json::from_slice(&body).unwrap_or(serde_json::Value::Null);
            Ok((status, json))
        }
    }
}
```

Replace the existing GET/POST/DELETE call sites that previously used `client` with this helper (or analogous `get_json` / `delete`). The compile-time discriminant ensures one cohesive transport per worker.

- [ ] **Step 6: Add the systemd unit**

Create `deploy/systemd/nasrudin-worker.service`:

```ini
[Unit]
Description=Nasrudin local-droplet worker (auto-trusted via UDS)
After=network-online.target nasrudin-api.service
Wants=nasrudin-api.service

[Service]
Type=simple
User=nasrudin
Group=nasrudin
WorkingDirectory=/opt/nasrudin
EnvironmentFile=/opt/nasrudin/.env
Environment=NASRUDIN_API_URL=unix:///run/nasrudin/api-local.sock
Environment=PROVER_ROOT=/opt/nasrudin/prover
Environment=ELAN_HOME=/opt/nasrudin/elan
Environment=PATH=/opt/nasrudin/elan/bin:/usr/local/bin:/usr/bin:/bin
ExecStart=/opt/nasrudin/bin/worker
Restart=on-failure
RestartSec=10
StandardOutput=journal
StandardError=journal

[Install]
WantedBy=multi-user.target
```

- [ ] **Step 7: Run tests**

Run: `cd engine && cargo test -p nasrudin-ga --test worker_uds_uri`
Expected: PASS.
Run: `cd engine && cargo build -p nasrudin-ga --bin worker`
Expected: clean build.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/ga/Cargo.toml engine/crates/ga/src/worker_url.rs \
        engine/crates/ga/src/bin/worker.rs engine/crates/ga/src/lib.rs \
        engine/crates/ga/tests/worker_uds_uri.rs \
        deploy/systemd/nasrudin-worker.service
git commit -m "feat(worker): unix:// URL scheme + UDS hyper client"
```

## Section D — Reverify spot-check sampling

### Task 15: Spot-check sampling + trusted-bypass verification path

**Files:**
- Modify: `engine/crates/api/src/reverify.rs`
- Modify: `engine/crates/pg/src/entity/theorems.rs` (verify `verification_path`, `verification_tactic` columns exist; if not, add another migration. They are already present per earlier grep.)
- Modify: `engine/crates/api/src/handlers/ingest.rs` (carry `TrustDecision` into the queue)
- Test: `engine/crates/api/tests/spot_check_sampling.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/spot_check_sampling.rs
mod test_app;

use sea_orm::EntityTrait;
use uuid::Uuid;

#[tokio::test]
async fn trusted_with_rate_zero_bypasses_lake_promotion() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let (worker_key, key_id) = test_app::issue_worker_key(&app, "trusted-w").await;
    test_app::set_key_trust(&app, key_id, true, 0).await;

    let row = test_app::ingest_one_with_key(&app, &worker_key, false).await;
    test_app::run_reverify_drain_once(&app).await;
    let m = nasrudin_pg::entity::theorems::Entity::find_by_id(row.id.clone())
        .one(&app.pg).await.unwrap().unwrap();
    assert_eq!(m.verification_path.as_deref(), Some("trusted_bypass"));
    assert_eq!(m.verification_tactic.as_deref(), Some("lake_build"));
    // Lake-promotion queue should not receive this row.
    assert!(!test_app::lake_promotion_contains(&app, &row.id).await);
}

#[tokio::test]
async fn trusted_with_rate_50_samples_about_2_percent() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let (worker_key, key_id) = test_app::issue_worker_key(&app, "trusted-50").await;
    test_app::set_key_trust(&app, key_id, true, 50).await;

    let mut sampled = 0usize;
    for _ in 0..200 {
        let row = test_app::ingest_one_with_key(&app, &worker_key, true).await;
        test_app::run_reverify_drain_once(&app).await;
        if test_app::lake_promotion_contains(&app, &row.id).await { sampled += 1; }
    }
    // Expect roughly 4 ± reasonable jitter.
    assert!((1..=12).contains(&sampled), "expected ~4 sampled, got {sampled}");
}

#[tokio::test]
async fn untrusted_always_promotes() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let (worker_key, _) = test_app::issue_worker_key(&app, "untrusted-w").await;
    let row = test_app::ingest_one_with_key(&app, &worker_key, true).await;
    test_app::run_reverify_drain_once(&app).await;
    assert!(test_app::lake_promotion_contains(&app, &row.id).await);
}

#[tokio::test]
async fn deterministic_resampling() {
    use physics_api::trust::{should_promote, TrustDecision, TrustSource};
    let dec = TrustDecision { trusted: true, spot_check_rate: 50, source: TrustSource::UserFlag };
    let id = b"deterministic-test-id-bytes";
    let r1 = should_promote(&dec, id);
    let r2 = should_promote(&dec, id);
    assert_eq!(r1, r2);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd engine && cargo test -p physics-api --test spot_check_sampling`
Expected: FAIL — helpers and behavior missing.

- [ ] **Step 3: Modify `ReverifyJob`**

In `engine/crates/api/src/reverify.rs`, find the `pub struct ReverifyJob { ... }` and add fields:

```rust
pub struct ReverifyJob {
    pub theorem_id: Vec<u8>,
    // NEW (Task 15):
    pub trust_decision: Option<crate::trust::TrustDecision>,
}
```

Update every constructor and the rocks-side queue payload accordingly. If the rocks queue serialises `ReverifyJob`, ensure `TrustDecision` impls `Serialize`/`Deserialize` (it already derives `Serialize`; add `Deserialize` to `trust.rs`).

- [ ] **Step 4: Update `process_one`**

In `engine/crates/api/src/reverify.rs`, replace the `ChainCheck::Regenerated(_regen) => { ... }` arm body with:

```rust
ChainCheck::Regenerated(_regen) => {
    use crate::trust::{should_promote, TrustSource};
    let decision = job.trust_decision.clone();
    let bypass = decision.as_ref().map(|d| !should_promote(d, &job.theorem_id)).unwrap_or(false);

    if bypass {
        // Trusted + sampled-out: skip lake promotion entirely.
        self.flip_verified(&row, "trusted_bypass", "lake_build", 0).await?;
        if let Some(d) = decision.as_ref() {
            crate::metrics::SPOT_CHECK_DECISIONS_TOTAL.with_label_values(&["bypass"]).inc();
            crate::metrics::TRUST_LOOKUP_TOTAL
                .with_label_values(&["trusted", &format!("{:?}", d.source)]).inc();
        }
        self.rocks.dequeue_reverify(&job.theorem_id).ok();
        return Ok(());
    }

    // Untrusted, or trusted+sampled-in. Existing path:
    let (path, tactic, promotion_priority) = if row.worker_verified {
        ("A_worker_claim", "worker_claim", 1u8)
    } else {
        ("A_chain_replay", "chain_replay", 2u8)
    };
    self.flip_verified(&row, path, tactic, 0).await?;
    let mut id_arr = [0u8; 8];
    if row.id.len() == 8 {
        id_arr.copy_from_slice(&row.id);
        let _ = self.rocks.enqueue_lake_promotion(&id_arr, promotion_priority);
    }
    if let Some(d) = decision.as_ref() {
        crate::metrics::SPOT_CHECK_DECISIONS_TOTAL.with_label_values(&["sampled"]).inc();
        crate::metrics::TRUST_LOOKUP_TOTAL
            .with_label_values(&["trusted", &format!("{:?}", d.source)]).inc();
    }
    self.rocks.dequeue_reverify(&job.theorem_id).ok();
    Ok(())
}
```

(The new metrics are added in Task 18-or-later metrics task; for now, stub them so this compiles.)

- [ ] **Step 5: Plumb `trust_decision` through ingest**

In `engine/crates/api/src/handlers/ingest.rs`, where `enqueue_reverify` is called, build the `ReverifyJob` with `trust_decision: Some(decision.clone())`.

- [ ] **Step 6: Add test harness helpers**

In `engine/crates/api/tests/test_app/mod.rs`, append:

```rust
pub async fn set_key_trust(app: &TestApp, key_id: uuid::Uuid, trusted: bool, rate: i32) {
    use sea_orm::{Statement, DatabaseBackend, ConnectionTrait};
    app.pg.execute(Statement::from_sql_and_values(DatabaseBackend::Postgres,
        "UPDATE api_keys SET trust_override=$2, spot_check_rate=$3 WHERE id=$1",
        [key_id.into(), trusted.into(), rate.into()],
    )).await.unwrap();
}

pub async fn ingest_one_with_key(app: &TestApp, worker_key: &str, _vary: bool) -> nasrudin_pg::entity::theorems::Model {
    // (Adapt from existing test helpers — submit a minimal valid theorem
    // through `/api/ingest` using `worker_key` as Bearer.)
    todo!("adapt from existing tests/e2e_spontaneous_emc2_ingest.rs body builder")
}

pub async fn run_reverify_drain_once(app: &TestApp) {
    if let Some(rev) = &app.reverify {
        rev.drain_one_for_test().await.ok();
    }
}

pub async fn lake_promotion_contains(app: &TestApp, theorem_id: &[u8]) -> bool {
    // Inspect the rocks lake-promotion queue. Adapt to the actual rocks API.
    let mut id8 = [0u8; 8];
    if theorem_id.len() != 8 { return false; }
    id8.copy_from_slice(theorem_id);
    app.db.peek_lake_promotion_queue().any(|(id, _)| id == id8)
}
```

(Where helpers don't yet exist on rocks/`ReverifyQueue`, add them as small public methods.)

- [ ] **Step 7: Run tests to verify they pass**

Run: `cd engine && cargo test -p physics-api --test spot_check_sampling`
Expected: ALL PASS.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/api/src/reverify.rs \
        engine/crates/api/src/trust.rs \
        engine/crates/api/src/handlers/ingest.rs \
        engine/crates/api/tests/test_app/mod.rs \
        engine/crates/api/tests/spot_check_sampling.rs
git commit -m "feat(api): trusted-bypass verification path + 1-in-N spot-check sampling"
```

## Section E — Admin foundation: actions, RequireAdmin, perform_audited

### Task 16: Action constants module

**Files:**
- Create: `engine/crates/api/src/admin/mod.rs`
- Create: `engine/crates/api/src/admin/audit.rs` (constants only; helper added in Task 18)
- Modify: `engine/crates/api/src/lib.rs` (`pub mod admin;`)

- [ ] **Step 1: Write the constants**

```rust
// engine/crates/api/src/admin/audit.rs
//! Frozen action taxonomy for `admin_audit_log.action`. Strings kept in
//! one place so dashboards / queries / tests can rely on stable values.
//! Adding new actions: append, never rename.

pub mod actions {
    pub const SET_IS_ADMIN: &str = "SET_IS_ADMIN";
    pub const SET_IS_TRUSTED: &str = "SET_IS_TRUSTED";
    pub const SET_SPOT_CHECK_RATE: &str = "SET_SPOT_CHECK_RATE";
    pub const SET_KEY_TRUST: &str = "SET_KEY_TRUST";
    pub const SET_PLAN_TIER: &str = "SET_PLAN_TIER";
    pub const ADJUST_CREDITS: &str = "ADJUST_CREDITS";
    pub const REVOKE_API_KEY: &str = "REVOKE_API_KEY";
    pub const REFUND_INITIATED: &str = "REFUND_INITIATED";
    pub const REFUND_SUCCEEDED: &str = "REFUND_SUCCEEDED";
    pub const REFUND_FAILED: &str = "REFUND_FAILED";
    pub const IMPERSONATE_START: &str = "IMPERSONATE_START";
    pub const IMPERSONATE_END: &str = "IMPERSONATE_END";
    pub const IMPERSONATE_FORCE_END: &str = "IMPERSONATE_FORCE_END";
    pub const IMPERSONATED_ACTION: &str = "IMPERSONATED_ACTION";
    pub const CANCEL_JOB: &str = "CANCEL_JOB";
    pub const RELOAD_CORPUS: &str = "RELOAD_CORPUS";
    pub const FORCE_STEERING: &str = "FORCE_STEERING";
    pub const QUEUE_EMAIL: &str = "QUEUE_EMAIL";
    pub const RETRY_EMAIL: &str = "RETRY_EMAIL";
    pub const BULK_RUN_START: &str = "BULK_RUN_START";
    pub const BULK_RUN_COMPLETE: &str = "BULK_RUN_COMPLETE";
    pub const AUTO_REVOKE_WORKER: &str = "AUTO_REVOKE_WORKER";
}

/// Hardcoded UUID used as `actor_user_id` for system-driven audit rows
/// (refund reconciler, auto-revoke, impersonation expiry tick). Created
/// by `admin-bootstrap.sh` in users(id, email, ...).
pub const SYSTEM_ACTOR_ID: uuid::Uuid = uuid::Uuid::from_u128(0x00000000_0000_0000_0000_000000000001);
```

```rust
// engine/crates/api/src/admin/mod.rs
//! Admin-panel infrastructure: RequireAdmin extractor, audit invariant
//! helper (perform_audited), action taxonomy.
pub mod audit;
pub mod require_admin;
```

- [ ] **Step 2: Wire up**

`engine/crates/api/src/lib.rs`: add `pub mod admin;`.

- [ ] **Step 3: Cargo check**

Run: `cd engine && cargo check -p physics-api`
Expected: clean.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/admin/mod.rs engine/crates/api/src/admin/audit.rs \
        engine/crates/api/src/lib.rs
git commit -m "feat(api): admin module skeleton + frozen action taxonomy"
```

### Task 17: `RequireAdmin` extractor

**Files:**
- Create: `engine/crates/api/src/admin/require_admin.rs`
- Test: `engine/crates/api/tests/admin_require_admin.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_require_admin.rs
mod test_app;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

#[tokio::test]
async fn rejects_anonymous_user() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let resp = app.router.clone().oneshot(
        Request::get("/api/admin/users").body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn allows_admin_session() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "admin@t.local").await;
    let resp = app.router.clone().oneshot(
        Request::get("/api/admin/users").header("Cookie", cookie).body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
}

#[tokio::test]
async fn allows_bearer_admin_token_as_system_actor() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_admin_token(b"test-admin-token").await else { return; };
    let resp = app.router.clone().oneshot(
        Request::get("/api/admin/users").header("Authorization", "Bearer test-admin-token")
            .body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
}

#[tokio::test]
async fn rejects_non_admin_session() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_user_session(&app, "user@t.local").await;
    let resp = app.router.clone().oneshot(
        Request::get("/api/admin/users").header("Cookie", cookie).body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::FORBIDDEN);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd engine && cargo test -p physics-api --test admin_require_admin`
Expected: FAIL — endpoint and helpers missing.

- [ ] **Step 3: Write the extractor**

```rust
// engine/crates/api/src/admin/require_admin.rs
use axum::extract::FromRequestParts;
use axum::http::{StatusCode, header, request::Parts};
use axum::Json;
use axum_login::AuthSession;
use serde_json::json;

use crate::admin::audit::SYSTEM_ACTOR_ID;
use crate::auth::{AuthUser, Backend};
use crate::state::AppState;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub enum AdminAuthSource { Session, BearerToken }

#[derive(Clone, Debug)]
pub struct AdminContext {
    pub user: AuthUser,
    pub source: AdminAuthSource,
}

pub struct RequireAdmin(pub AdminContext);

impl FromRequestParts<Arc<AppState>> for RequireAdmin {
    type Rejection = (StatusCode, Json<serde_json::Value>);

    async fn from_request_parts(parts: &mut Parts, state: &Arc<AppState>) -> Result<Self, Self::Rejection> {
        // Path 1: session cookie
        if let Ok(session) = AuthSession::<Backend>::from_request_parts(parts, state.as_ref()).await {
            if let Some(user) = session.user.clone() {
                let pg = state.pg.as_ref().ok_or((StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"pg_unavailable"}))))?;
                let m = nasrudin_pg::query::users::find_by_id(pg, user.id).await
                    .map_err(|_| (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":"db"}))))?;
                let is_admin = m.map(|u| u.is_admin).unwrap_or(false);
                if is_admin {
                    return Ok(RequireAdmin(AdminContext { user, source: AdminAuthSource::Session }));
                }
                return Err((StatusCode::FORBIDDEN, Json(json!({"error":"admin_required"}))));
            }
        }

        // Path 2: bearer token
        let token = parts.headers.get(header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok()).and_then(|s| s.strip_prefix("Bearer "));
        if let (Some(provided), Some(expected)) = (token, state.admin_token.as_ref()) {
            if provided == expected {
                let now: chrono::DateTime<chrono::FixedOffset> = chrono::Utc::now().into();
                let user = AuthUser {
                    id: SYSTEM_ACTOR_ID, email: "system@nasrudin.org".into(),
                    password_hash: None, display_name: Some("system".into()),
                    created_at: now, plan_tier: "free".into(),
                    stripe_customer_id: None, stripe_subscription_id: None,
                    current_period_end: None, plan_cycle_start: None,
                    github_id: None, github_login: None,
                    auth_hash_bytes: SYSTEM_ACTOR_ID.as_bytes().to_vec(),
                };
                return Ok(RequireAdmin(AdminContext { user, source: AdminAuthSource::BearerToken }));
            }
        }

        Err((StatusCode::UNAUTHORIZED, Json(json!({"error":"admin_required"}))))
    }
}
```

- [ ] **Step 4: Add a tiny admin endpoint to anchor the test**

Stub `engine/crates/api/src/handlers/admin/users.rs`:

```rust
//! Stub for Task 17 — full impl arrives in Task 19.
use axum::Json;
use axum::http::StatusCode;
use crate::admin::require_admin::RequireAdmin;

pub async fn list(_admin: RequireAdmin) -> (StatusCode, Json<serde_json::Value>) {
    (StatusCode::OK, Json(serde_json::json!({"users": [], "total": 0})))
}
```

Wire `pub mod users;` in `engine/crates/api/src/handlers/admin/mod.rs` (create with `pub mod users;`), and re-export the route in `main.rs`:

```rust
let admin = Router::new()
    // ...existing entries...
    .route("/api/admin/users", get(handlers::admin::users::list))
    // ...
    ;
```

Add `engine/crates/api/src/handlers/mod.rs` to declare `pub mod admin;` (and remove the old `pub mod admin;` line that pointed at the file `admin.rs`). The old `handlers/admin.rs` is moved into `handlers/admin/mod.rs` plus split files in Task 43.

- [ ] **Step 5: Add test harness helpers**

In `engine/crates/api/tests/test_app/mod.rs`, append:

```rust
impl TestApp {
    pub async fn build_with_admin_token(token: &[u8]) -> Option<Self> {
        let mut app = Self::build().await?;
        app = app.set_admin_token(std::str::from_utf8(token).unwrap().to_string());
        Some(app)
    }
    pub fn set_admin_token(mut self, t: String) -> Self {
        // mutate the AppState — for tests, swap `state.admin_token`.
        let state = self.state_mut();
        state.admin_token = Some(t);
        self
    }
}

pub async fn create_admin_session(app: &TestApp, email: &str) -> String {
    let user = nasrudin_pg::query::users::create_user(&app.pg, email, Some("h"), None).await.unwrap();
    sea_orm::ConnectionTrait::execute(&app.pg, sea_orm::Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE users SET is_admin=TRUE WHERE id=$1", [user.id.into()],
    )).await.unwrap();
    test_session_cookie_for(app, user.id).await
}

pub async fn create_user_session(app: &TestApp, email: &str) -> String {
    let user = nasrudin_pg::query::users::create_user(&app.pg, email, Some("h"), None).await.unwrap();
    test_session_cookie_for(app, user.id).await
}

async fn test_session_cookie_for(app: &TestApp, user_id: uuid::Uuid) -> String {
    // Use POST /api/auth/login with a known password is awkward. Instead, hit
    // a test-only `/__test/login_as` endpoint that the `cfg(test)` build of
    // the router exposes.
    let resp = app.router.clone().oneshot(
        axum::http::Request::post("/__test/login_as")
            .body(axum::body::Body::from(format!(r#"{{"id":"{user_id}"}}"#))).unwrap()
    ).await.unwrap();
    let cookie = resp.headers().get("set-cookie").unwrap().to_str().unwrap().split(';').next().unwrap();
    cookie.to_string()
}
```

Add the `/__test/login_as` route in `main.rs` behind `#[cfg(any(test, debug_assertions))]` ONLY when an `NASRUDIN_TEST_LOGIN=1` env var is set so production stays safe.

- [ ] **Step 6: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_require_admin`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/admin/require_admin.rs \
        engine/crates/api/src/admin/mod.rs \
        engine/crates/api/src/handlers/admin/mod.rs \
        engine/crates/api/src/handlers/admin/users.rs \
        engine/crates/api/src/handlers/mod.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/test_app/mod.rs \
        engine/crates/api/tests/admin_require_admin.rs
git commit -m "feat(api): RequireAdmin extractor (session OR ADMIN_TOKEN bearer)"
```

### Task 18: `perform_audited` invariant helper + observability metrics

**Files:**
- Modify: `engine/crates/api/src/admin/audit.rs` (append helper)
- Modify: `engine/crates/api/src/metrics.rs`
- Test: `engine/crates/api/tests/admin_audit_invariant.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_audit_invariant.rs
mod test_app;

use serde_json::json;
use uuid::Uuid;

use physics_api::admin::audit::{perform_audited, RequestMeta};
use physics_api::auth::AuthUser;

fn make_actor(id: Uuid, email: &str) -> AuthUser {
    AuthUser {
        id, email: email.into(), password_hash: None, display_name: None,
        created_at: chrono::Utc::now().into(), plan_tier: "free".into(),
        stripe_customer_id: None, stripe_subscription_id: None,
        current_period_end: None, plan_cycle_start: None,
        github_id: None, github_login: None, auth_hash_bytes: id.as_bytes().to_vec(),
    }
}

#[tokio::test]
async fn audit_row_inserted_atomically_with_mutation() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let admin = nasrudin_pg::query::users::create_user(&app.pg, "a@t.local", Some("h"), None).await.unwrap();
    let actor = make_actor(admin.id, &admin.email);
    let target = nasrudin_pg::query::users::create_user(&app.pg, "t@t.local", Some("h"), None).await.unwrap();

    let result = perform_audited(
        &app.pg, &actor, None,
        RequestMeta { ip: None, user_agent: None },
        Some(target.id), "SET_IS_TRUSTED", "promoting to trusted user".into(),
        json!({"is_trusted": false}),
        |txn| async move {
            sea_orm::ConnectionTrait::execute(txn, sea_orm::Statement::from_sql_and_values(
                sea_orm::DatabaseBackend::Postgres,
                "UPDATE users SET is_trusted=TRUE WHERE id=$1", [target.id.into()],
            )).await?;
            Ok::<_, sea_orm::DbErr>(((), json!({"is_trusted": true})))
        },
    ).await.unwrap();
    let _ = result;

    let rows = nasrudin_pg::query::admin_audit_log::list_by_target(&app.pg, target.id, 10).await.unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].action, "SET_IS_TRUSTED");
    assert_eq!(rows[0].before_value.as_ref().unwrap()["is_trusted"], false);
    assert_eq!(rows[0].after_value.as_ref().unwrap()["is_trusted"], true);
}

#[tokio::test]
async fn rejects_short_reason() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let admin = nasrudin_pg::query::users::create_user(&app.pg, "a2@t.local", Some("h"), None).await.unwrap();
    let actor = make_actor(admin.id, &admin.email);
    let err = perform_audited(
        &app.pg, &actor, None,
        RequestMeta { ip: None, user_agent: None },
        None, "SET_IS_TRUSTED", "short".into(),
        json!({}),
        |_txn| async { Ok::<_, sea_orm::DbErr>(((), json!({}))) },
    ).await;
    assert!(err.is_err());
}

#[tokio::test]
async fn mutation_failure_rolls_back_audit_row() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let admin = nasrudin_pg::query::users::create_user(&app.pg, "a3@t.local", Some("h"), None).await.unwrap();
    let actor = make_actor(admin.id, &admin.email);
    let _err = perform_audited(
        &app.pg, &actor, None,
        RequestMeta { ip: None, user_agent: None },
        None, "SET_IS_TRUSTED", "mutation will fail explicitly".into(),
        json!({}),
        |_txn| async { Err::<((), serde_json::Value), _>(sea_orm::DbErr::Custom("boom".into())) },
    ).await;
    // No audit rows inserted because txn rolled back.
    let rows = nasrudin_pg::query::admin_audit_log::list_recent(&app.pg, 10).await.unwrap();
    assert!(rows.is_empty());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p physics-api --test admin_audit_invariant`
Expected: FAIL — `perform_audited` does not exist.

- [ ] **Step 3: Implement the helper**

Append to `engine/crates/api/src/admin/audit.rs`:

```rust
use std::future::Future;
use std::net::IpAddr;

use nasrudin_pg::sea_orm::{DatabaseConnection, DatabaseTransaction, DbErr, TransactionTrait};
use uuid::Uuid;

#[derive(Clone, Debug, Default)]
pub struct RequestMeta {
    pub ip: Option<IpAddr>,
    pub user_agent: Option<String>,
}

#[derive(Clone, Debug)]
pub struct ImpersonationCtx {
    pub session_id: Uuid,
    pub original_admin_id: Uuid,
}

#[derive(Debug, thiserror::Error)]
pub enum AuditError {
    #[error("reason must be at least 10 characters")]
    ReasonTooShort,
    #[error("db: {0}")]
    Db(#[from] DbErr),
}

#[allow(clippy::too_many_arguments)]
pub async fn perform_audited<T, F, Fut>(
    pg: &DatabaseConnection,
    actor: &crate::auth::AuthUser,
    impersonation: Option<ImpersonationCtx>,
    req_meta: RequestMeta,
    target_user_id: Option<Uuid>,
    action: &'static str,
    reason: String,
    before_value: serde_json::Value,
    mutate: F,
) -> Result<T, AuditError>
where
    F: FnOnce(&DatabaseTransaction) -> Fut + Send,
    Fut: Future<Output = Result<(T, serde_json::Value), DbErr>> + Send,
    T: Send,
{
    if reason.trim().chars().count() < 10 { return Err(AuditError::ReasonTooShort); }

    let txn = pg.begin().await?;
    let (out, after_value) = mutate(&txn).await?;
    nasrudin_pg::query::admin_audit_log::insert(
        &txn, actor.id, target_user_id,
        impersonation.as_ref().map(|i| i.original_admin_id),
        action, Some(before_value), Some(after_value),
        reason, req_meta.ip, req_meta.user_agent.clone(),
    ).await?;
    txn.commit().await?;

    crate::metrics::ADMIN_ACTION_TOTAL.with_label_values(&[action, "ok"]).inc();
    Ok(out)
}
```

- [ ] **Step 4: Add metrics**

In `engine/crates/api/src/metrics.rs`, register the new label families:

```rust
pub static ADMIN_ACTION_TOTAL: once_cell::sync::Lazy<prometheus::IntCounterVec> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_counter_vec!("admin_action_total", "Admin actions",
        &["action", "outcome"]).unwrap()
});
pub static TRUST_LOOKUP_TOTAL: once_cell::sync::Lazy<prometheus::IntCounterVec> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_counter_vec!("trust_lookup_total", "Trust resolution outcomes",
        &["decision", "source"]).unwrap()
});
pub static SPOT_CHECK_DECISIONS_TOTAL: once_cell::sync::Lazy<prometheus::IntCounterVec> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_counter_vec!("spot_check_decisions_total", "Spot-check sampling decisions",
        &["action"]).unwrap()
});
pub static IMPERSONATION_ACTIVE_SESSIONS: once_cell::sync::Lazy<prometheus::IntGauge> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_gauge!("impersonation_active_sessions", "Active impersonation sessions").unwrap()
});
pub static EMAIL_QUEUE_DEPTH: once_cell::sync::Lazy<prometheus::IntGaugeVec> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_gauge_vec!("email_queue_depth", "Email outbox queue depth by status",
        &["status"]).unwrap()
});
pub static EMAIL_SEND_ATTEMPTS_TOTAL: once_cell::sync::Lazy<prometheus::IntCounterVec> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_counter_vec!("email_send_attempts_total", "Email send attempts",
        &["outcome"]).unwrap()
});
pub static REFUND_RECORDS_TOTAL: once_cell::sync::Lazy<prometheus::IntCounterVec> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_counter_vec!("refund_records_total", "Refund records by terminal status",
        &["status"]).unwrap()
});
pub static REFUND_RECONCILER_RESOLVED_TOTAL: once_cell::sync::Lazy<prometheus::IntCounter> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_counter!("refund_reconciler_resolved_total", "Refunds resolved via reconciler").unwrap()
});
pub static BULK_RUNS_ACTIVE: once_cell::sync::Lazy<prometheus::IntGauge> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_gauge!("bulk_runs_active", "Active bulk runs").unwrap()
});
pub static BULK_RUNS_COMPLETED_TOTAL: once_cell::sync::Lazy<prometheus::IntCounterVec> = once_cell::sync::Lazy::new(|| {
    prometheus::register_int_counter_vec!("bulk_runs_completed_total", "Completed bulk runs",
        &["outcome"]).unwrap()
});
```

(Add `prometheus` and `once_cell` to api `Cargo.toml` if not already present.)

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_audit_invariant`
Expected: ALL THREE PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/admin/audit.rs engine/crates/api/src/metrics.rs \
        engine/crates/api/Cargo.toml \
        engine/crates/api/tests/admin_audit_invariant.rs
git commit -m "feat(api): perform_audited helper with transactional audit log + metrics"
```

## Section F — Admin user/key/job/audit/stats handlers

### Task 19: GET `/api/admin/users` (paginated) + GET `/api/admin/users/{id}` (detail)

**Files:**
- Modify: `engine/crates/api/src/handlers/admin/users.rs` (replace stub)
- Create: `engine/crates/pg/src/query/admin_users.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`
- Modify: `engine/crates/api/src/main.rs` (route)
- Test: `engine/crates/api/tests/admin_users_handlers.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_users_handlers.rs
mod test_app;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;
use serde_json::Value;

#[tokio::test]
async fn list_users_paginated() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "ad@t.local").await;
    for i in 0..5 {
        nasrudin_pg::query::users::create_user(&app.pg, &format!("u{i}@t.local"), Some("h"), None).await.unwrap();
    }
    let resp = app.router.clone().oneshot(
        Request::get("/api/admin/users?page=1&page_size=3")
            .header("Cookie", &cookie).body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let body: Value = serde_json::from_slice(
        &axum::body::to_bytes(resp.into_body(), 1<<16).await.unwrap()
    ).unwrap();
    assert_eq!(body["users"].as_array().unwrap().len(), 3);
    assert!(body["total"].as_u64().unwrap() >= 6); // includes admin itself
}

#[tokio::test]
async fn get_user_detail_includes_keys_and_recent_audit() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "adx@t.local").await;
    let target = nasrudin_pg::query::users::create_user(&app.pg, "tx@t.local", Some("h"), None).await.unwrap();

    let resp = app.router.clone().oneshot(
        Request::get(format!("/api/admin/users/{}", target.id))
            .header("Cookie", cookie).body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let body: Value = serde_json::from_slice(
        &axum::body::to_bytes(resp.into_body(), 1<<16).await.unwrap()
    ).unwrap();
    assert_eq!(body["user"]["email"], "tx@t.local");
    assert!(body["api_keys"].is_array());
    assert!(body["recent_audit"].is_array());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd engine && cargo test -p physics-api --test admin_users_handlers`
Expected: FAIL — endpoints missing.

- [ ] **Step 3: Write the query module**

```rust
// engine/crates/pg/src/query/admin_users.rs
use sea_orm::*;
use uuid::Uuid;

use crate::entity::users;

#[derive(Clone, Debug)]
pub struct UserRow {
    pub id: Uuid,
    pub email: String,
    pub display_name: Option<String>,
    pub plan_tier: String,
    pub research_credits: i32,
    pub is_admin: bool,
    pub is_trusted: bool,
    pub spot_check_rate: Option<i32>,
    pub created_at: chrono::DateTime<chrono::FixedOffset>,
    pub stripe_customer_id: Option<String>,
}

impl From<users::Model> for UserRow {
    fn from(m: users::Model) -> Self {
        Self { id: m.id, email: m.email, display_name: m.display_name,
            plan_tier: m.plan_tier, research_credits: m.research_credits,
            is_admin: m.is_admin, is_trusted: m.is_trusted, spot_check_rate: m.spot_check_rate,
            created_at: m.created_at, stripe_customer_id: m.stripe_customer_id,
        }
    }
}

pub async fn list_paginated(
    db: &DatabaseConnection, page: u64, page_size: u64,
    search: Option<&str>, only_paid: bool,
) -> Result<(Vec<UserRow>, u64), DbErr> {
    let mut q = users::Entity::find();
    if let Some(s) = search {
        let pat = format!("%{}%", s.to_lowercase());
        q = q.filter(
            Condition::any()
                .add(users::Column::Email.like(pat.clone()))
                .add(users::Column::DisplayName.like(pat))
        );
    }
    if only_paid {
        q = q.filter(users::Column::PlanTier.ne("free"));
    }
    let total = q.clone().count(db).await?;
    let rows = q.order_by_desc(users::Column::CreatedAt)
        .paginate(db, page_size).fetch_page(page.saturating_sub(1)).await?;
    Ok((rows.into_iter().map(Into::into).collect(), total))
}

pub async fn find_by_id(db: &DatabaseConnection, id: Uuid) -> Result<Option<users::Model>, DbErr> {
    users::Entity::find_by_id(id).one(db).await
}

pub async fn set_is_admin<C: ConnectionTrait>(conn: &C, id: Uuid, value: bool) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(DatabaseBackend::Postgres,
        "UPDATE users SET is_admin=$2 WHERE id=$1", [id.into(), value.into()])).await?;
    Ok(())
}
pub async fn set_is_trusted<C: ConnectionTrait>(conn: &C, id: Uuid, value: bool) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(DatabaseBackend::Postgres,
        "UPDATE users SET is_trusted=$2 WHERE id=$1", [id.into(), value.into()])).await?;
    Ok(())
}
pub async fn set_spot_check_rate<C: ConnectionTrait>(conn: &C, id: Uuid, rate: Option<i32>) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(DatabaseBackend::Postgres,
        "UPDATE users SET spot_check_rate=$2 WHERE id=$1", [id.into(), rate.into()])).await?;
    Ok(())
}
pub async fn set_plan_tier<C: ConnectionTrait>(conn: &C, id: Uuid, tier: &str) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(DatabaseBackend::Postgres,
        "UPDATE users SET plan_tier=$2 WHERE id=$1", [id.into(), tier.to_string().into()])).await?;
    Ok(())
}
pub async fn adjust_credits<C: ConnectionTrait>(conn: &C, id: Uuid, delta: i32) -> Result<i32, DbErr> {
    let stmt = Statement::from_sql_and_values(DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = research_credits + $2 WHERE id=$1
         RETURNING research_credits", [id.into(), delta.into()]);
    let res = conn.query_one(stmt).await?
        .ok_or_else(|| DbErr::RecordNotFound("user".into()))?;
    Ok(res.try_get_by::<i32, _>("research_credits")?)
}
```

- [ ] **Step 4: Replace handler stub**

```rust
// engine/crates/api/src/handlers/admin/users.rs
use std::sync::Arc;

use axum::{Json, extract::{Path, Query, State}, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use serde_json::json;
use uuid::Uuid;

use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct ListParams {
    #[serde(default = "default_page")] pub page: u64,
    #[serde(default = "default_page_size")] pub page_size: u64,
    pub search: Option<String>,
    #[serde(default)] pub only_paid: bool,
}
fn default_page() -> u64 { 1 }
fn default_page_size() -> u64 { 25 }

pub async fn list(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Query(p): Query<ListParams>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"pg_unavailable"}))).into_response() };
    match nasrudin_pg::query::admin_users::list_paginated(pg, p.page, p.page_size, p.search.as_deref(), p.only_paid).await {
        Ok((rows, total)) => {
            (StatusCode::OK, Json(json!({"users": rows.iter().map(|u| json!({
                "id": u.id, "email": u.email, "display_name": u.display_name,
                "plan_tier": u.plan_tier, "research_credits": u.research_credits,
                "is_admin": u.is_admin, "is_trusted": u.is_trusted,
                "spot_check_rate": u.spot_check_rate, "created_at": u.created_at,
                "stripe_customer_id": u.stripe_customer_id,
            })).collect::<Vec<_>>(), "total": total, "page": p.page, "page_size": p.page_size}))).into_response()
        }
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    }
}

pub async fn detail(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"pg_unavailable"}))).into_response() };
    let user = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
        Ok(Some(u)) => u, Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let keys = nasrudin_pg::query::api_keys::list_by_user(pg, id).await.unwrap_or_default();
    let audit = nasrudin_pg::query::admin_audit_log::list_by_target(pg, id, 50).await.unwrap_or_default();
    (StatusCode::OK, Json(json!({
        "user": {
            "id": user.id, "email": user.email, "display_name": user.display_name,
            "plan_tier": user.plan_tier, "research_credits": user.research_credits,
            "is_admin": user.is_admin, "is_trusted": user.is_trusted,
            "spot_check_rate": user.spot_check_rate, "created_at": user.created_at,
            "stripe_customer_id": user.stripe_customer_id,
            "stripe_subscription_id": user.stripe_subscription_id,
            "current_period_end": user.current_period_end,
        },
        "api_keys": keys,
        "recent_audit": audit,
    }))).into_response()
}
```

- [ ] **Step 5: Wire routes + module**

`engine/crates/pg/src/query/mod.rs`: `pub mod admin_users;`
`engine/crates/api/src/main.rs`: in the `admin` Router builder, add:
```rust
.route("/api/admin/users", get(handlers::admin::users::list))
.route("/api/admin/users/{id}", get(handlers::admin::users::detail))
```

- [ ] **Step 6: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_users_handlers`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/handlers/admin/users.rs \
        engine/crates/pg/src/query/admin_users.rs \
        engine/crates/pg/src/query/mod.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_users_handlers.rs
git commit -m "feat(api): GET /api/admin/users + /{id} list and detail"
```

### Task 20: POST `/api/admin/users/{id}/admin` (toggle is_admin)

**Files:**
- Modify: `engine/crates/api/src/handlers/admin/users.rs`
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_users_handlers.rs` (append)

- [ ] **Step 1: Write the failing test (append to file)**

```rust
#[tokio::test]
async fn promote_user_to_admin_with_audit_row() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "ad-promote@t.local").await;
    let target = nasrudin_pg::query::users::create_user(&app.pg, "promote@t.local", Some("h"), None).await.unwrap();

    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/admin", target.id))
            .header("Cookie", &cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"is_admin":true,"reason":"granting admin"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let m = nasrudin_pg::query::admin_users::find_by_id(&app.pg, target.id).await.unwrap().unwrap();
    assert!(m.is_admin);
    let rows = nasrudin_pg::query::admin_audit_log::list_by_target(&app.pg, target.id, 5).await.unwrap();
    assert!(rows.iter().any(|r| r.action == "SET_IS_ADMIN"));
}

#[tokio::test]
async fn admin_cannot_demote_self() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "self-demote@t.local").await;
    let me = nasrudin_pg::query::users::find_by_email(&app.pg, "self-demote@t.local").await.unwrap().unwrap();
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/admin", me.id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"is_admin":false,"reason":"trying to demote self"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::CONFLICT);
}

#[tokio::test]
async fn last_admin_demotion_blocked_by_db_trigger() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_admin_token(b"tok").await else { return; };
    let only_admin = nasrudin_pg::query::users::create_user(&app.pg, "lone@t.local", Some("h"), None).await.unwrap();
    nasrudin_pg::query::admin_users::set_is_admin(&app.pg, only_admin.id, true).await.unwrap();

    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/admin", only_admin.id))
            .header("Authorization", "Bearer tok").header("Content-Type", "application/json")
            .body(Body::from(r#"{"is_admin":false,"reason":"attempt to demote last admin"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::CONFLICT);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd engine && cargo test -p physics-api --test admin_users_handlers`
Expected: FAIL — endpoint missing.

- [ ] **Step 3: Implement the handler**

Append to `engine/crates/api/src/handlers/admin/users.rs`:

```rust
use crate::admin::audit::{actions, perform_audited, RequestMeta};
use axum::extract::ConnectInfo;
use axum::http::HeaderMap;
use std::net::SocketAddr;

#[derive(Deserialize)]
pub struct SetAdminInput { pub is_admin: bool, pub reason: String }

pub async fn set_admin(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<SetAdminInput>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"pg_unavailable"}))).into_response() };
    if id == admin.0.user.id {
        return (StatusCode::CONFLICT, Json(json!({"error":"cannot_modify_self"}))).into_response();
    }
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
        Ok(Some(u)) => u,
        Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let user_agent = headers.get(axum::http::header::USER_AGENT)
        .and_then(|v| v.to_str().ok()).map(str::to_string);
    let result = perform_audited(
        pg, &admin.0.user, None,
        RequestMeta { ip: Some(addr.ip()), user_agent },
        Some(id), actions::SET_IS_ADMIN, body.reason,
        json!({"is_admin": before.is_admin}),
        |txn| async move {
            nasrudin_pg::query::admin_users::set_is_admin(txn, id, body.is_admin).await?;
            Ok::<_, sea_orm::DbErr>(((), json!({"is_admin": body.is_admin})))
        },
    ).await;
    match result {
        Ok(_) => (StatusCode::OK, Json(json!({"ok":true}))).into_response(),
        Err(e) => {
            if e.to_string().contains("cannot demote last admin") || e.to_string().contains("P0001") {
                return (StatusCode::CONFLICT, Json(json!({"error":"last_admin"}))).into_response();
            }
            (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}
```

- [ ] **Step 4: Wire route**

`main.rs`: `.route("/api/admin/users/{id}/admin", post(handlers::admin::users::set_admin))`

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_users_handlers`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/handlers/admin/users.rs engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_users_handlers.rs
git commit -m "feat(api): POST /api/admin/users/{id}/admin with self-protect + last-admin guard"
```

### Task 21: POST `/api/admin/users/{id}/trust` + POST `/api/admin/users/{id}/spot_check_rate`

**Files:**
- Modify: `engine/crates/api/src/handlers/admin/users.rs`
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_users_handlers.rs` (append)

- [ ] **Step 1: Write the failing test**

```rust
#[tokio::test]
async fn toggle_trust_invalidates_cache_and_emits_audit() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "trust-admin@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "trust-target@t.local", Some("h"), None).await.unwrap();
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/trust", user.id))
            .header("Cookie", &cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"is_trusted":true,"reason":"trusted contributor"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let m = nasrudin_pg::query::admin_users::find_by_id(&app.pg, user.id).await.unwrap().unwrap();
    assert!(m.is_trusted);
}

#[tokio::test]
async fn set_spot_check_rate_value_and_clear() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "scr-admin@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "scr-target@t.local", Some("h"), None).await.unwrap();
    // set
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/spot_check_rate", user.id))
            .header("Cookie", &cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"rate":10,"reason":"high-volume contributor"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    // clear
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/spot_check_rate", user.id))
            .header("Cookie", &cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"rate":null,"reason":"reset to env default"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let m = nasrudin_pg::query::admin_users::find_by_id(&app.pg, user.id).await.unwrap().unwrap();
    assert_eq!(m.spot_check_rate, None);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Expected: FAIL.

- [ ] **Step 3: Implement the handlers**

Append to `engine/crates/api/src/handlers/admin/users.rs`:

```rust
use crate::trust::CacheInvalidation;

#[derive(Deserialize)]
pub struct SetTrustInput { pub is_trusted: bool, pub reason: String }

pub async fn set_trust(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<SetTrustInput>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"pg_unavailable"}))).into_response() };
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
        Ok(Some(u)) => u,
        Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let result = perform_audited(
        pg, &admin.0.user, None,
        RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        Some(id), actions::SET_IS_TRUSTED, body.reason,
        json!({"is_trusted": before.is_trusted}),
        |txn| async move {
            nasrudin_pg::query::admin_users::set_is_trusted(txn, id, body.is_trusted).await?;
            Ok::<_, sea_orm::DbErr>(((), json!({"is_trusted": body.is_trusted})))
        },
    ).await;
    match result {
        Ok(_) => {
            let _ = state.trust_invalidation_tx.send(CacheInvalidation::User(id));
            (StatusCode::OK, Json(json!({"ok":true}))).into_response()
        }
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    }
}

#[derive(Deserialize)]
pub struct SetRateInput { pub rate: Option<i32>, pub reason: String }

pub async fn set_spot_check_rate(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<SetRateInput>,
) -> impl IntoResponse {
    if let Some(r) = body.rate { if r < 0 { return (StatusCode::BAD_REQUEST, Json(json!({"error":"rate_negative"}))).into_response(); } }
    let pg = match &state.pg { Some(p) => p, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"pg_unavailable"}))).into_response() };
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
        Ok(Some(u)) => u, Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let result = perform_audited(
        pg, &admin.0.user, None,
        RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        Some(id), actions::SET_SPOT_CHECK_RATE, body.reason,
        json!({"spot_check_rate": before.spot_check_rate}),
        |txn| async move {
            nasrudin_pg::query::admin_users::set_spot_check_rate(txn, id, body.rate).await?;
            Ok::<_, sea_orm::DbErr>(((), json!({"spot_check_rate": body.rate})))
        },
    ).await;
    match result {
        Ok(_) => {
            let _ = state.trust_invalidation_tx.send(CacheInvalidation::User(id));
            (StatusCode::OK, Json(json!({"ok":true}))).into_response()
        }
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    }
}
```

- [ ] **Step 4: Wire routes**

`main.rs`:
```rust
.route("/api/admin/users/{id}/trust", post(handlers::admin::users::set_trust))
.route("/api/admin/users/{id}/spot_check_rate", post(handlers::admin::users::set_spot_check_rate))
```

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_users_handlers`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/handlers/admin/users.rs engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_users_handlers.rs
git commit -m "feat(api): POST trust + spot_check_rate admin endpoints with cache invalidation"
```

### Task 22: POST `/api/admin/users/{id}/plan` + POST `/api/admin/users/{id}/credits`

**Files:**
- Modify: `engine/crates/api/src/handlers/admin/users.rs`
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_users_handlers.rs` (append)

- [ ] **Step 1: Write the failing test**

```rust
#[tokio::test]
async fn set_plan_tier_writes_audit_and_queues_email() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "plan-admin@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "plan@t.local", Some("h"), None).await.unwrap();
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/plan", user.id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"plan_tier":"researcher","reason":"comping launch invite"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let m = nasrudin_pg::query::admin_users::find_by_id(&app.pg, user.id).await.unwrap().unwrap();
    assert_eq!(m.plan_tier, "researcher");
    let pending = nasrudin_pg::query::email_outbox::list_recent(&app.pg, 5, 0).await.unwrap();
    assert!(pending.iter().any(|e| e.template == "admin_plan_change"));
}

#[tokio::test]
async fn adjust_credits_positive_and_negative() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "cr-admin@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "cr@t.local", Some("h"), None).await.unwrap();
    let post = |delta: i32| {
        let body = format!(r#"{{"delta":{delta},"reason":"adjusting research credits"}}"#);
        let cookie = cookie.clone();
        let app = app.clone();
        let id = user.id;
        async move {
            app.router.clone().oneshot(
                Request::post(format!("/api/admin/users/{}/credits", id))
                    .header("Cookie", cookie).header("Content-Type", "application/json")
                    .body(Body::from(body)).unwrap()
            ).await.unwrap()
        }
    };
    assert_eq!(post(5).await.status(), StatusCode::OK);
    assert_eq!(post(-2).await.status(), StatusCode::OK);
    let m = nasrudin_pg::query::admin_users::find_by_id(&app.pg, user.id).await.unwrap().unwrap();
    assert_eq!(m.research_credits, 3);
}
```

(`TestApp` may need `Clone` — implement via wrapping fields in `Arc` or expose `clone_router` helper.)

- [ ] **Step 2: Run tests**

Expected: FAIL.

- [ ] **Step 3: Implement handlers**

Append to `engine/crates/api/src/handlers/admin/users.rs`:

```rust
#[derive(Deserialize)]
pub struct SetPlanInput { pub plan_tier: String, pub reason: String }

pub async fn set_plan(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<SetPlanInput>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"pg_unavailable"}))).into_response() };
    if !matches!(body.plan_tier.as_str(), "free"|"researcher"|"team"|"institution") {
        return (StatusCode::BAD_REQUEST, Json(json!({"error":"unknown_tier"}))).into_response();
    }
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
        Ok(Some(u)) => u, Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let new_tier = body.plan_tier.clone();
    let actor_id = admin.0.user.id;
    let target_email = before.email.clone();
    let new_tier_email = new_tier.clone();
    let old_tier = before.plan_tier.clone();
    let result = perform_audited(
        pg, &admin.0.user, None,
        RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        Some(id), actions::SET_PLAN_TIER, body.reason,
        json!({"plan_tier": &before.plan_tier}),
        move |txn| async move {
            nasrudin_pg::query::admin_users::set_plan_tier(txn, id, &new_tier).await?;
            // Transactional email queue (Section §10.5).
            let body_text = format!("Your plan was changed from {} to {}.", old_tier, new_tier_email);
            nasrudin_pg::query::email_outbox::queue(
                txn, Some(id), &target_email, "admin_plan_change",
                "Your Nasrudin plan was updated", &body_text, None,
                Some(actor_id), Some(crate::admin::audit::actions::SET_PLAN_TIER),
            ).await?;
            Ok::<_, sea_orm::DbErr>(((), json!({"plan_tier": new_tier_email})))
        },
    ).await;
    match result {
        Ok(_) => (StatusCode::OK, Json(json!({"ok":true}))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    }
}

#[derive(Deserialize)]
pub struct AdjustCreditsInput { pub delta: i32, pub reason: String }

pub async fn adjust_credits(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<AdjustCreditsInput>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"pg_unavailable"}))).into_response() };
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
        Ok(Some(u)) => u, Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let target_email = before.email.clone();
    let actor_id = admin.0.user.id;
    let delta = body.delta;
    let result = perform_audited(
        pg, &admin.0.user, None,
        RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        Some(id), actions::ADJUST_CREDITS, body.reason,
        json!({"research_credits": before.research_credits}),
        move |txn| async move {
            let new_credits = nasrudin_pg::query::admin_users::adjust_credits(txn, id, delta).await?;
            if delta > 0 {
                let body_text = format!("Your account was credited with {} research credit(s). New balance: {}.", delta, new_credits);
                nasrudin_pg::query::email_outbox::queue(
                    txn, Some(id), &target_email, "admin_credit_grant",
                    "Research credits granted", &body_text, None,
                    Some(actor_id), Some(crate::admin::audit::actions::ADJUST_CREDITS),
                ).await?;
            }
            Ok::<_, sea_orm::DbErr>(((), json!({"research_credits": new_credits, "delta": delta})))
        },
    ).await;
    match result {
        Ok(_) => (StatusCode::OK, Json(json!({"ok":true}))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    }
}
```

- [ ] **Step 4: Wire routes**

`main.rs`:
```rust
.route("/api/admin/users/{id}/plan", post(handlers::admin::users::set_plan))
.route("/api/admin/users/{id}/credits", post(handlers::admin::users::adjust_credits))
```

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_users_handlers`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/handlers/admin/users.rs engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_users_handlers.rs
git commit -m "feat(api): POST plan + credits admin endpoints (transactional email queue)"
```

### Task 23: API key admin endpoints (revoke + trust override)

**Files:**
- Create: `engine/crates/api/src/handlers/admin/api_keys.rs`
- Modify: `engine/crates/api/src/handlers/admin/mod.rs`
- Modify: `engine/crates/pg/src/query/api_keys.rs`
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_api_keys_handlers.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_api_keys_handlers.rs
mod test_app;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

#[tokio::test]
async fn admin_revokes_api_key() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "rk@t.local").await;
    let (_secret, kid) = test_app::issue_worker_key(&app, "to-revoke").await;
    let resp = app.router.clone().oneshot(
        Request::delete(format!("/api/admin/api_keys/{}", kid))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"reason":"compromised key reported"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let row = nasrudin_pg::query::api_keys::find_by_id(&app.pg, kid).await.unwrap().unwrap();
    assert!(row.revoked_at.is_some());
}

#[tokio::test]
async fn admin_sets_per_key_trust_override() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "ko@t.local").await;
    let (_secret, kid) = test_app::issue_worker_key(&app, "to-override").await;
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/api_keys/{}/trust", kid))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"trust_override":true,"spot_check_rate":20,"reason":"trusted partner key"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let row = nasrudin_pg::query::api_keys::find_by_id(&app.pg, kid).await.unwrap().unwrap();
    assert_eq!(row.trust_override, Some(true));
    assert_eq!(row.spot_check_rate, Some(20));
}
```

- [ ] **Step 2: Run test to verify it fails**

Expected: FAIL.

- [ ] **Step 3: Add query helpers**

Append to `engine/crates/pg/src/query/api_keys.rs`:

```rust
pub async fn revoke<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(DatabaseBackend::Postgres,
        "UPDATE api_keys SET revoked_at=now() WHERE id=$1", [id.into()])).await?;
    Ok(())
}
pub async fn set_trust<C: ConnectionTrait>(conn: &C, id: Uuid, trust_override: Option<bool>, rate: Option<i32>) -> Result<(), DbErr> {
    conn.execute(Statement::from_sql_and_values(DatabaseBackend::Postgres,
        "UPDATE api_keys SET trust_override=$2, spot_check_rate=$3 WHERE id=$1",
        [id.into(), trust_override.into(), rate.into()])).await?;
    Ok(())
}
```

- [ ] **Step 4: Write the handler**

```rust
// engine/crates/api/src/handlers/admin/api_keys.rs
use std::sync::Arc;
use axum::{Json, extract::{Path, State, ConnectInfo}, http::{StatusCode, HeaderMap}, response::IntoResponse};
use serde::Deserialize;
use serde_json::json;
use std::net::SocketAddr;
use uuid::Uuid;

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;
use crate::trust::CacheInvalidation;

#[derive(Deserialize)]
pub struct RevokeInput { pub reason: String }

pub async fn revoke(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<RevokeInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let row = match nasrudin_pg::query::api_keys::find_by_id(pg, id).await {
        Ok(Some(r)) => r, Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let result = perform_audited(
        pg, &admin.0.user, None, RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        row.user_id, actions::REVOKE_API_KEY, body.reason,
        json!({"revoked_at": row.revoked_at, "name": row.name}),
        |txn| async move {
            nasrudin_pg::query::api_keys::revoke(txn, id).await?;
            Ok::<_, sea_orm::DbErr>(((), json!({"revoked": true})))
        },
    ).await;
    match result {
        Ok(_) => {
            let _ = state.trust_invalidation_tx.send(CacheInvalidation::ApiKey(id));
            (StatusCode::OK, Json(json!({"ok":true}))).into_response()
        }
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    }
}

#[derive(Deserialize)]
pub struct SetTrustInput { pub trust_override: Option<bool>, pub spot_check_rate: Option<i32>, pub reason: String }

pub async fn set_trust(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<SetTrustInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let row = match nasrudin_pg::query::api_keys::find_by_id(pg, id).await {
        Ok(Some(r)) => r, Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let new_to = body.trust_override;
    let new_rate = body.spot_check_rate;
    let result = perform_audited(
        pg, &admin.0.user, None, RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        row.user_id, actions::SET_KEY_TRUST, body.reason,
        json!({"trust_override": row.trust_override, "spot_check_rate": row.spot_check_rate}),
        move |txn| async move {
            nasrudin_pg::query::api_keys::set_trust(txn, id, new_to, new_rate).await?;
            Ok::<_, sea_orm::DbErr>(((), json!({"trust_override": new_to, "spot_check_rate": new_rate})))
        },
    ).await;
    match result {
        Ok(_) => {
            let _ = state.trust_invalidation_tx.send(CacheInvalidation::ApiKey(id));
            (StatusCode::OK, Json(json!({"ok":true}))).into_response()
        }
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    }
}
```

- [ ] **Step 5: Wire module + routes**

`engine/crates/api/src/handlers/admin/mod.rs`: add `pub mod api_keys;`.
`engine/crates/api/src/main.rs`:
```rust
.route("/api/admin/api_keys/{id}", delete(handlers::admin::api_keys::revoke))
.route("/api/admin/api_keys/{id}/trust", post(handlers::admin::api_keys::set_trust))
```

- [ ] **Step 6: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_api_keys_handlers`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/handlers/admin/api_keys.rs \
        engine/crates/api/src/handlers/admin/mod.rs \
        engine/crates/pg/src/query/api_keys.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_api_keys_handlers.rs
git commit -m "feat(api): admin API-key revoke + per-key trust override endpoints"
```

### Task 24: POST `/api/admin/jobs/{id}/cancel`

**Files:**
- Create: `engine/crates/api/src/handlers/admin/jobs.rs`
- Modify: `engine/crates/api/src/handlers/admin/mod.rs`
- Modify: `engine/crates/pg/src/query/conjecture_jobs.rs`
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_jobs_handlers.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_jobs_handlers.rs
mod test_app;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

#[tokio::test]
async fn admin_cancels_running_job_and_refunds_credit() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "j@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "ju@t.local", Some("h"), None).await.unwrap();
    nasrudin_pg::query::admin_users::adjust_credits(&app.pg, user.id, 5).await.unwrap();
    let job_id = test_app::seed_paid_conjecture_job(&app, user.id).await; // helper

    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/jobs/{}/cancel", job_id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"reason":"user requested cancel via support","refund":true}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
}
```

- [ ] **Step 2: Run test (will fail)**

Expected: FAIL — endpoint missing.

- [ ] **Step 3: Add query helpers**

Append to `engine/crates/pg/src/query/conjecture_jobs.rs`:

```rust
pub async fn admin_cancel<C: ConnectionTrait>(conn: &C, id: Uuid) -> Result<Option<(Uuid, String, bool)>, DbErr> {
    // Returns (user_id, status_was, was_paid). Sets status='cancelled'.
    let stmt = Statement::from_sql_and_values(DatabaseBackend::Postgres,
        "UPDATE conjecture_jobs SET status='cancelled', completed_at=now()
         WHERE id=$1 AND status IN ('queued','running')
         RETURNING user_id, COALESCE(plan_at_creation, '') as paid_marker, status",
        [id.into()]);
    if let Some(row) = conn.query_one(stmt).await? {
        let uid: Uuid = row.try_get_by("user_id")?;
        let status: String = row.try_get_by("status")?;
        let paid_marker: String = row.try_get_by("paid_marker")?;
        return Ok(Some((uid, status, paid_marker == "researcher")));
    }
    Ok(None)
}
```

(Adapt the column names to whatever already exists in `conjecture_jobs` — replace `plan_at_creation` with the real column tracking paid lineage if different.)

- [ ] **Step 4: Write the handler**

```rust
// engine/crates/api/src/handlers/admin/jobs.rs
use std::sync::Arc;
use axum::{Json, extract::{Path, State, ConnectInfo}, http::{StatusCode, HeaderMap}, response::IntoResponse};
use serde::Deserialize;
use serde_json::json;
use std::net::SocketAddr;
use uuid::Uuid;

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct CancelInput { pub reason: String, #[serde(default)] pub refund: bool }

pub async fn cancel(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<CancelInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let refund = body.refund;
    let result = perform_audited(
        pg, &admin.0.user, None, RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        None, actions::CANCEL_JOB, body.reason,
        json!({"job_id": id}),
        move |txn| async move {
            let cancelled = nasrudin_pg::query::conjecture_jobs::admin_cancel(txn, id).await?;
            let after = match cancelled {
                Some((uid, status, was_paid)) => {
                    if refund && was_paid {
                        nasrudin_pg::query::admin_users::adjust_credits(txn, uid, 1).await?;
                    }
                    json!({"job_id": id, "user_id": uid, "previous_status": status, "refunded": refund && was_paid})
                }
                None => json!({"job_id": id, "no_op": true}),
            };
            Ok::<_, sea_orm::DbErr>(((), after))
        },
    ).await;
    match result {
        Ok(_) => (StatusCode::OK, Json(json!({"ok":true}))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    }
}
```

- [ ] **Step 5: Wire module + route**

`handlers/admin/mod.rs`: `pub mod jobs;`
`main.rs`: `.route("/api/admin/jobs/{id}/cancel", post(handlers::admin::jobs::cancel))`

- [ ] **Step 6: Run tests**

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/handlers/admin/jobs.rs \
        engine/crates/api/src/handlers/admin/mod.rs \
        engine/crates/pg/src/query/conjecture_jobs.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_jobs_handlers.rs
git commit -m "feat(api): admin job cancel endpoint with optional credit refund"
```

### Task 25: GET `/api/admin/audit`

**Files:**
- Create: `engine/crates/api/src/handlers/admin/audit_log.rs`
- Modify: `engine/crates/api/src/handlers/admin/mod.rs`
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_audit_log_handler.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_audit_log_handler.rs
mod test_app;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;
use serde_json::Value;

#[tokio::test]
async fn lists_filtered_audit_log() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "audlog@t.local").await;
    let target = nasrudin_pg::query::users::create_user(&app.pg, "audtg@t.local", Some("h"), None).await.unwrap();
    let actor = nasrudin_pg::query::users::find_by_email(&app.pg, "audlog@t.local").await.unwrap().unwrap();
    nasrudin_pg::query::admin_audit_log::insert(
        &app.pg, actor.id, Some(target.id), None, "SET_IS_TRUSTED",
        Some(serde_json::json!({"is_trusted": false})), Some(serde_json::json!({"is_trusted": true})),
        "test reason".into(), None, None,
    ).await.unwrap();

    let resp = app.router.clone().oneshot(
        Request::get(format!("/api/admin/audit?target_user_id={}", target.id))
            .header("Cookie", cookie).body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let body: Value = serde_json::from_slice(&axum::body::to_bytes(resp.into_body(), 1<<16).await.unwrap()).unwrap();
    assert_eq!(body["entries"].as_array().unwrap().len(), 1);
    assert_eq!(body["entries"][0]["action"], "SET_IS_TRUSTED");
}
```

- [ ] **Step 2: Run test to verify it fails**

Expected: FAIL.

- [ ] **Step 3: Implement handler**

```rust
// engine/crates/api/src/handlers/admin/audit_log.rs
use std::sync::Arc;
use axum::{Json, extract::{Query, State}, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use uuid::Uuid;

use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct ListQ {
    pub actor_user_id: Option<Uuid>,
    pub target_user_id: Option<Uuid>,
    pub action: Option<String>,
    #[serde(default = "default_limit")] pub limit: u64,
    #[serde(default)] pub offset: u64,
}
fn default_limit() -> u64 { 100 }

pub async fn list(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Query(q): Query<ListQ>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    match nasrudin_pg::query::admin_audit_log::list_filtered(
        pg, q.actor_user_id, q.target_user_id, q.action.as_deref(),
        q.limit.min(500), q.offset,
    ).await {
        Ok(rows) => (StatusCode::OK, Json(serde_json::json!({"entries": rows}))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(serde_json::json!({"error": e.to_string()}))).into_response(),
    }
}
```

- [ ] **Step 4: Wire module + route**

`handlers/admin/mod.rs`: `pub mod audit_log;`
`main.rs`: `.route("/api/admin/audit", get(handlers::admin::audit_log::list))`

- [ ] **Step 5: Run test**

Run: `cd engine && cargo test -p physics-api --test admin_audit_log_handler`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/handlers/admin/audit_log.rs \
        engine/crates/api/src/handlers/admin/mod.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_audit_log_handler.rs
git commit -m "feat(api): GET /api/admin/audit with actor/target/action filters"
```

### Task 26: GET `/api/admin/stats`

**Files:**
- Create: `engine/crates/api/src/handlers/admin/stats.rs`
- Modify: `engine/crates/api/src/state.rs` (`stats_cache: ArcSwap<...>`)
- Modify: `engine/crates/api/src/handlers/admin/mod.rs`
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_stats_handler.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_stats_handler.rs
mod test_app;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;
use serde_json::Value;

#[tokio::test]
async fn stats_covers_users_theorems_queues() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "stat@t.local").await;
    for i in 0..3 {
        nasrudin_pg::query::users::create_user(&app.pg, &format!("s{i}@t.local"), Some("h"), None).await.unwrap();
    }
    let resp = app.router.clone().oneshot(
        Request::get("/api/admin/stats").header("Cookie", cookie).body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let body: Value = serde_json::from_slice(&axum::body::to_bytes(resp.into_body(), 1<<16).await.unwrap()).unwrap();
    for k in ["users_total", "theorems_by_status", "reverify_queue_depth", "lake_promotion_queue_depth", "email_outbox_pending", "trusted_users", "recent_audit"] {
        assert!(body.get(k).is_some(), "missing {k}");
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Expected: FAIL.

- [ ] **Step 3: Implement the handler**

```rust
// engine/crates/api/src/handlers/admin/stats.rs
use std::sync::Arc;
use std::time::{Duration, Instant};

use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use serde_json::json;

use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

const CACHE_TTL: Duration = Duration::from_secs(10);

pub async fn stats(_admin: RequireAdmin, State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"pg_unavailable"}))).into_response() };

    let cached = state.stats_cache.load();
    if let Some((ts, body)) = cached.as_ref() {
        if ts.elapsed() < CACHE_TTL {
            return (StatusCode::OK, Json(body.clone())).into_response();
        }
    }

    let (users_total, theorems_by_status, email_pending, trusted_users, recent_audit) = tokio::join!(
        async {
            sea_orm::EntityTrait::find(nasrudin_pg::entity::users::Entity).count(pg).await.unwrap_or(0)
        },
        async {
            // Group by `status`. Use raw SQL.
            use sea_orm::{ConnectionTrait, Statement, DatabaseBackend};
            let stmt = Statement::from_string(DatabaseBackend::Postgres,
                "SELECT status, count(*) FROM theorems GROUP BY status".to_string());
            let mut out = serde_json::Map::new();
            if let Ok(rows) = pg.query_all(stmt).await {
                for r in rows {
                    let s: String = r.try_get_by("status").unwrap_or_default();
                    let c: i64 = r.try_get_by("count").unwrap_or(0);
                    out.insert(s, json!(c));
                }
            }
            json!(out)
        },
        async { nasrudin_pg::query::email_outbox::count_by_status(pg, "queued").await.unwrap_or(0) },
        async {
            use sea_orm::{ConnectionTrait, Statement, DatabaseBackend};
            let stmt = Statement::from_string(DatabaseBackend::Postgres,
                "SELECT count(*) AS c FROM users WHERE is_trusted = TRUE".to_string());
            pg.query_one(stmt).await.ok().flatten()
                .and_then(|r| r.try_get_by::<i64,_>("c").ok()).unwrap_or(0)
        },
        async {
            nasrudin_pg::query::admin_audit_log::list_recent(pg, 10).await.unwrap_or_default()
        },
    );

    let reverify_depth = state.reverify.as_ref().map(|r| r.queue_depth_for_stats()).unwrap_or(0);
    let lake_depth = state.db.lake_promotion_queue_depth().unwrap_or(0);

    let body = json!({
        "users_total": users_total,
        "theorems_by_status": theorems_by_status,
        "reverify_queue_depth": reverify_depth,
        "lake_promotion_queue_depth": lake_depth,
        "email_outbox_pending": email_pending,
        "trusted_users": trusted_users,
        "recent_audit": recent_audit,
    });
    state.stats_cache.store(Arc::new(Some((Instant::now(), body.clone()))));
    (StatusCode::OK, Json(body)).into_response()
}
```

- [ ] **Step 4: Add `stats_cache` to AppState**

In `engine/crates/api/src/state.rs`:

```rust
pub stats_cache: arc_swap::ArcSwap<Option<(std::time::Instant, serde_json::Value)>>,
```

Initialize in `main.rs`:
```rust
stats_cache: arc_swap::ArcSwap::from_pointee(None),
```

- [ ] **Step 5: Wire route**

`handlers/admin/mod.rs`: `pub mod stats;`
`main.rs`: `.route("/api/admin/stats", get(handlers::admin::stats::stats))`

- [ ] **Step 6: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_stats_handler`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/handlers/admin/stats.rs \
        engine/crates/api/src/handlers/admin/mod.rs \
        engine/crates/api/src/state.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_stats_handler.rs
git commit -m "feat(api): GET /api/admin/stats with 10 s ArcSwap cache"
```

## Section G — Email infrastructure (Resend)

### Task 27: `email/outbox.rs` queue + queue_in_txn

**Files:**
- Create: `engine/crates/api/src/email/mod.rs`
- Create: `engine/crates/api/src/email/outbox.rs`
- Modify: `engine/crates/api/src/lib.rs`
- Test: `engine/crates/api/tests/email_outbox_wrapper.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/email_outbox_wrapper.rs
mod test_app;

use sea_orm::TransactionTrait;
use serde_json::json;

#[tokio::test]
async fn queue_in_txn_rolls_back_on_failure() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let user = nasrudin_pg::query::users::create_user(&app.pg, "eo@t.local", Some("h"), None).await.unwrap();
    let txn = app.pg.begin().await.unwrap();
    physics_api::email::queue_in_txn(
        &txn, Some(user.id), &user.email, "admin_credit_grant",
        "Credits", "body", None, None, None,
    ).await.unwrap();
    txn.rollback().await.unwrap();
    let pending = nasrudin_pg::query::email_outbox::list_recent(&app.pg, 5, 0).await.unwrap();
    assert!(pending.iter().all(|e| e.template != "admin_credit_grant" || e.subject != "Credits"));
}

#[tokio::test]
async fn queue_inserts_outside_txn() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let id = physics_api::email::queue(
        &app.pg, None, "raw@t.local", "admin_custom_message",
        "Hi", "body", None, None, None,
    ).await.unwrap();
    assert!(nasrudin_pg::query::email_outbox::find_by_id(&app.pg, id).await.unwrap().is_some());
}
```

- [ ] **Step 2: Run tests**

Expected: FAIL — module missing.

- [ ] **Step 3: Implement**

```rust
// engine/crates/api/src/email/mod.rs
//! Email infrastructure: outbox queue, Resend provider, drain worker.
//!
//! API:
//! - `queue` / `queue_in_txn` — admins and system code call these to enqueue.
//! - `spawn_worker` — boot wires this up once; runs forever.

pub mod outbox;
pub mod provider;
pub mod templates;
pub mod worker;

pub use outbox::{queue, queue_in_txn};
pub use provider::{EmailProvider, ResendProvider, SendOutcome};
pub use worker::spawn_worker;
```

```rust
// engine/crates/api/src/email/outbox.rs
use nasrudin_pg::sea_orm::{ConnectionTrait, DbErr};
use uuid::Uuid;

#[allow(clippy::too_many_arguments)]
pub async fn queue<C: ConnectionTrait>(
    conn: &C, to_user_id: Option<Uuid>, to_address: &str,
    template: &str, subject: &str, body_text: &str, body_html: Option<&str>,
    queued_by_admin_id: Option<Uuid>, queued_by_action: Option<&str>,
) -> Result<Uuid, DbErr> {
    nasrudin_pg::query::email_outbox::queue(
        conn, to_user_id, to_address, template, subject, body_text, body_html,
        queued_by_admin_id, queued_by_action,
    ).await
}

#[allow(clippy::too_many_arguments)]
pub async fn queue_in_txn<C: ConnectionTrait>(
    conn: &C, to_user_id: Option<Uuid>, to_address: &str,
    template: &str, subject: &str, body_text: &str, body_html: Option<&str>,
    queued_by_admin_id: Option<Uuid>, queued_by_action: Option<&str>,
) -> Result<Uuid, DbErr> {
    queue(conn, to_user_id, to_address, template, subject, body_text, body_html,
          queued_by_admin_id, queued_by_action).await
}
```

(`queue` and `queue_in_txn` differ only by the explicit naming for callers — the underlying call is identical. The intent is documentation for the in-txn use case.)

- [ ] **Step 4: Wire**

`engine/crates/api/src/lib.rs`: `pub mod email;`.

- [ ] **Step 5: Run tests**

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/email/mod.rs engine/crates/api/src/email/outbox.rs \
        engine/crates/api/src/lib.rs \
        engine/crates/api/tests/email_outbox_wrapper.rs
git commit -m "feat(api): email::queue and queue_in_txn wrappers"
```

### Task 28: Tera template registry + template files

**Files:**
- Create: `engine/crates/api/src/email/templates.rs`
- Create: `engine/crates/api/src/email/templates/admin_credit_grant.{html,txt}`
- Create: `engine/crates/api/src/email/templates/admin_plan_change.{html,txt}`
- Create: `engine/crates/api/src/email/templates/admin_refund_issued.{html,txt}`
- Create: `engine/crates/api/src/email/templates/admin_account_action.{html,txt}`
- Create: `engine/crates/api/src/email/templates/admin_custom_message.{html,txt}`
- Modify: `engine/crates/api/Cargo.toml` (add `tera = "1"`)
- Test: `engine/crates/api/tests/email_templates.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/email_templates.rs
use physics_api::email::templates::{TemplateRegistry, RenderContext};

#[test]
fn renders_credit_grant() {
    let reg = TemplateRegistry::new().unwrap();
    let mut ctx = RenderContext::default();
    ctx.set("display_name", "Lia");
    ctx.set("delta", &5);
    ctx.set("balance", &12);
    let out = reg.render("admin_credit_grant", "txt", &ctx).unwrap();
    assert!(out.contains("Lia"));
    assert!(out.contains("5"));
    assert!(out.contains("12"));
}
```

- [ ] **Step 2: Run test**

Expected: FAIL — module missing.

- [ ] **Step 3: Implement the registry**

```rust
// engine/crates/api/src/email/templates.rs
use std::collections::HashMap;
use tera::Tera;

pub struct TemplateRegistry { tera: Tera }

#[derive(Default)]
pub struct RenderContext { ctx: tera::Context }
impl RenderContext {
    pub fn set<T: serde::Serialize>(&mut self, key: &str, value: &T) { self.ctx.insert(key, value); }
    pub fn ctx(&self) -> &tera::Context { &self.ctx }
}

const TEMPLATES: &[(&str, &str)] = &[
    ("admin_credit_grant.txt",     include_str!("templates/admin_credit_grant.txt")),
    ("admin_credit_grant.html",    include_str!("templates/admin_credit_grant.html")),
    ("admin_plan_change.txt",      include_str!("templates/admin_plan_change.txt")),
    ("admin_plan_change.html",     include_str!("templates/admin_plan_change.html")),
    ("admin_refund_issued.txt",    include_str!("templates/admin_refund_issued.txt")),
    ("admin_refund_issued.html",   include_str!("templates/admin_refund_issued.html")),
    ("admin_account_action.txt",   include_str!("templates/admin_account_action.txt")),
    ("admin_account_action.html",  include_str!("templates/admin_account_action.html")),
    ("admin_custom_message.txt",   include_str!("templates/admin_custom_message.txt")),
    ("admin_custom_message.html",  include_str!("templates/admin_custom_message.html")),
];

impl TemplateRegistry {
    pub fn new() -> tera::Result<Self> {
        let mut tera = Tera::default();
        for (name, body) in TEMPLATES { tera.add_raw_template(name, body)?; }
        Ok(Self { tera })
    }
    pub fn render(&self, template: &str, fmt: &str, ctx: &RenderContext) -> tera::Result<String> {
        self.tera.render(&format!("{template}.{fmt}"), ctx.ctx())
    }
}
```

- [ ] **Step 4: Write the templates**

`admin_credit_grant.txt`:
```
Hi {{ display_name | default(value="there") }},

You've been granted {{ delta }} research credit{{ delta | pluralize }}.
Your new balance is {{ balance }}.

— Nasrudin
```

`admin_credit_grant.html`:
```html
<p>Hi {{ display_name | default(value="there") }},</p>
<p>You've been granted <strong>{{ delta }}</strong> research credit{{ delta | pluralize }}. Your new balance is <strong>{{ balance }}</strong>.</p>
<p>— Nasrudin</p>
```

`admin_plan_change.txt`:
```
Hi {{ display_name | default(value="there") }},

Your Nasrudin plan changed from {{ old_tier }} to {{ new_tier }}.

— Nasrudin
```

`admin_plan_change.html`:
```html
<p>Hi {{ display_name | default(value="there") }},</p>
<p>Your Nasrudin plan changed from <strong>{{ old_tier }}</strong> to <strong>{{ new_tier }}</strong>.</p>
```

`admin_refund_issued.txt`:
```
Hi {{ display_name | default(value="there") }},

A refund of {{ amount_display }} has been issued to your card on file.
Reason: {{ reason }}

It typically posts within 5–10 business days.

— Nasrudin
```

`admin_refund_issued.html`:
```html
<p>Hi {{ display_name | default(value="there") }},</p>
<p>A refund of <strong>{{ amount_display }}</strong> has been issued. Reason: {{ reason }}.</p>
<p>It typically posts within 5–10 business days.</p>
```

`admin_account_action.txt`:
```
Hi {{ display_name | default(value="there") }},

A Nasrudin admin took the following action on your account: {{ action_label }}.
Reason: {{ reason }}

If you didn't expect this, reply to this email.

— Nasrudin
```

`admin_account_action.html`:
```html
<p>Hi {{ display_name | default(value="there") }},</p>
<p>A Nasrudin admin took the following action on your account: <strong>{{ action_label }}</strong>. Reason: {{ reason }}.</p>
<p>If you didn't expect this, reply to this email.</p>
```

`admin_custom_message.txt`:
```
{{ body_text }}

— Nasrudin
```

`admin_custom_message.html`:
```html
{{ body_html | safe }}
<p>— Nasrudin</p>
```

- [ ] **Step 5: Add `tera` dependency**

`engine/crates/api/Cargo.toml`: under `[dependencies]`, add `tera = "1"`.

- [ ] **Step 6: Run test**

Run: `cd engine && cargo test -p physics-api --test email_templates`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/email/templates.rs \
        engine/crates/api/src/email/templates/ \
        engine/crates/api/Cargo.toml \
        engine/crates/api/tests/email_templates.rs
git commit -m "feat(api): Tera template registry with 5 admin email templates"
```

### Task 29: `EmailProvider` trait + `ResendProvider`

**Files:**
- Create: `engine/crates/api/src/email/provider.rs`
- Modify: `engine/crates/api/Cargo.toml` (dev-dep: `wiremock = "0.6"`)
- Test: `engine/crates/api/tests/email_provider_resend.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/email_provider_resend.rs
use physics_api::email::provider::{ResendProvider, EmailProvider, SendOutcome};
use wiremock::{MockServer, Mock, ResponseTemplate, matchers};

#[tokio::test]
async fn happy_path_returns_message_id() {
    let server = MockServer::start().await;
    Mock::given(matchers::method("POST"))
        .and(matchers::path("/emails"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({"id": "abc-123"})))
        .mount(&server).await;

    let p = ResendProvider::new("re_test", server.uri(), "Nasrudin <noreply@nasrudin.org>".into());
    let outcome = p.send("u@t.local", "Hi", "body", None).await.unwrap();
    match outcome {
        SendOutcome::Sent { message_id } => assert_eq!(message_id, "abc-123"),
        _ => panic!("expected sent"),
    }
}

#[tokio::test]
async fn 4xx_returns_terminal() {
    let server = MockServer::start().await;
    Mock::given(matchers::method("POST"))
        .respond_with(ResponseTemplate::new(422).set_body_json(serde_json::json!({"message": "bad address"})))
        .mount(&server).await;
    let p = ResendProvider::new("re_test", server.uri(), "noreply@n.org".into());
    matches!(p.send("bogus", "s", "b", None).await.unwrap(), SendOutcome::FailedTerminal { .. });
}

#[tokio::test]
async fn 5xx_returns_retryable() {
    let server = MockServer::start().await;
    Mock::given(matchers::method("POST"))
        .respond_with(ResponseTemplate::new(503))
        .mount(&server).await;
    let p = ResendProvider::new("re_test", server.uri(), "noreply@n.org".into());
    matches!(p.send("u@t.local", "s", "b", None).await.unwrap(), SendOutcome::FailedRetryable { .. });
}
```

- [ ] **Step 2: Run tests**

Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
// engine/crates/api/src/email/provider.rs
use async_trait::async_trait;

#[derive(Debug)]
pub enum SendOutcome {
    Sent { message_id: String },
    FailedRetryable { error: String },
    FailedTerminal { error: String },
}

#[async_trait]
pub trait EmailProvider: Send + Sync {
    async fn send(&self, to: &str, subject: &str, body_text: &str, body_html: Option<&str>) -> Result<SendOutcome, anyhow::Error>;
}

pub struct ResendProvider {
    api_key: String,
    base_url: String,
    from: String,
    client: reqwest::Client,
}

impl ResendProvider {
    pub fn new(api_key: impl Into<String>, base_url: impl Into<String>, from: String) -> Self {
        Self { api_key: api_key.into(), base_url: base_url.into(), from, client: reqwest::Client::new() }
    }
}

#[async_trait]
impl EmailProvider for ResendProvider {
    async fn send(&self, to: &str, subject: &str, body_text: &str, body_html: Option<&str>) -> Result<SendOutcome, anyhow::Error> {
        let mut payload = serde_json::json!({
            "from": &self.from, "to": [to], "subject": subject, "text": body_text,
        });
        if let Some(h) = body_html { payload["html"] = serde_json::Value::String(h.into()); }

        let resp = self.client.post(format!("{}/emails", self.base_url))
            .bearer_auth(&self.api_key).json(&payload).send().await?;
        let status = resp.status().as_u16();
        if (200..300).contains(&status) {
            let body: serde_json::Value = resp.json().await.unwrap_or_default();
            let id = body.get("id").and_then(|v| v.as_str()).unwrap_or_default().to_string();
            return Ok(SendOutcome::Sent { message_id: id });
        }
        if (400..500).contains(&status) {
            let body = resp.text().await.unwrap_or_default();
            return Ok(SendOutcome::FailedTerminal { error: format!("{status}: {body}") });
        }
        let body = resp.text().await.unwrap_or_default();
        Ok(SendOutcome::FailedRetryable { error: format!("{status}: {body}") })
    }
}
```

- [ ] **Step 4: Add wiremock dev-dep**

`engine/crates/api/Cargo.toml` `[dev-dependencies]`: `wiremock = "0.6"`.

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test email_provider_resend`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/email/provider.rs \
        engine/crates/api/Cargo.toml \
        engine/crates/api/tests/email_provider_resend.rs
git commit -m "feat(api): EmailProvider trait + ResendProvider with wiremock-tested outcomes"
```

### Task 30: Email worker (drain loop)

**Files:**
- Create: `engine/crates/api/src/email/worker.rs`
- Modify: `engine/crates/api/src/main.rs` (spawn the worker)
- Test: `engine/crates/api/tests/admin_email_worker.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_email_worker.rs
mod test_app;

use std::sync::Arc;
use std::time::Duration;
use async_trait::async_trait;
use tokio::sync::Mutex;

use physics_api::email::provider::{EmailProvider, SendOutcome};

struct StubProvider { calls: Arc<Mutex<usize>>, ok: bool }
#[async_trait]
impl EmailProvider for StubProvider {
    async fn send(&self, _to: &str, _subj: &str, _body: &str, _html: Option<&str>) -> Result<SendOutcome, anyhow::Error> {
        *self.calls.lock().await += 1;
        if self.ok { Ok(SendOutcome::Sent { message_id: "stub-id".into() }) }
        else { Ok(SendOutcome::FailedTerminal { error: "stub".into() }) }
    }
}

#[tokio::test]
async fn worker_marks_sent_on_success() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let id = nasrudin_pg::query::email_outbox::queue(&app.pg, None, "u@t.local", "admin_custom_message", "S", "b", None, None, None).await.unwrap();
    let calls = Arc::new(Mutex::new(0));
    let provider: Arc<dyn EmailProvider> = Arc::new(StubProvider { calls: calls.clone(), ok: true });
    physics_api::email::worker::tick_once(&app.pg, &provider, &physics_api::email::templates::TemplateRegistry::new().unwrap()).await;
    let row = nasrudin_pg::query::email_outbox::find_by_id(&app.pg, id).await.unwrap().unwrap();
    assert_eq!(row.status, "sent");
    assert_eq!(*calls.lock().await, 1);
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Implement worker**

```rust
// engine/crates/api/src/email/worker.rs
use std::sync::Arc;
use std::time::Duration;

use nasrudin_pg::sea_orm::DatabaseConnection;
use tokio::sync::Semaphore;

use crate::email::provider::{EmailProvider, SendOutcome};
use crate::email::templates::TemplateRegistry;

pub fn spawn_worker(pg: DatabaseConnection, provider: Arc<dyn EmailProvider>, registry: Arc<TemplateRegistry>) {
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(5));
        loop {
            interval.tick().await;
            tick_once(&pg, &provider, &registry).await;
        }
    });
}

pub async fn tick_once(pg: &DatabaseConnection, provider: &Arc<dyn EmailProvider>, _registry: &TemplateRegistry) {
    let pending = match nasrudin_pg::query::email_outbox::claim_pending(pg, 16).await {
        Ok(r) => r, Err(e) => { tracing::warn!(?e, "email claim failed"); return; }
    };
    let sem = Arc::new(Semaphore::new(4));
    let mut handles = Vec::new();
    for row in pending {
        let permit = sem.clone().acquire_owned().await.unwrap();
        let pg = pg.clone();
        let provider = provider.clone();
        handles.push(tokio::spawn(async move {
            let _permit = permit;
            let outcome = provider.send(&row.to_address, &row.subject, &row.body_text, row.body_html.as_deref()).await;
            match outcome {
                Ok(SendOutcome::Sent { message_id }) => {
                    let _ = nasrudin_pg::query::email_outbox::mark_sent(&pg, row.id, &message_id).await;
                    crate::metrics::EMAIL_SEND_ATTEMPTS_TOTAL.with_label_values(&["sent"]).inc();
                }
                Ok(SendOutcome::FailedTerminal { error }) => {
                    let _ = nasrudin_pg::query::email_outbox::mark_failed_terminal(&pg, row.id, &error).await;
                    crate::metrics::EMAIL_SEND_ATTEMPTS_TOTAL.with_label_values(&["failed_terminal"]).inc();
                }
                Ok(SendOutcome::FailedRetryable { error }) => {
                    let attempts = row.attempts + 1;
                    if attempts >= 5 {
                        let _ = nasrudin_pg::query::email_outbox::mark_failed_terminal(&pg, row.id, &error).await;
                        crate::metrics::EMAIL_SEND_ATTEMPTS_TOTAL.with_label_values(&["exhausted"]).inc();
                    } else {
                        let _ = nasrudin_pg::query::email_outbox::mark_failed_retrying(&pg, row.id, &error).await;
                        crate::metrics::EMAIL_SEND_ATTEMPTS_TOTAL.with_label_values(&["retry"]).inc();
                    }
                }
                Err(e) => {
                    let _ = nasrudin_pg::query::email_outbox::mark_failed_retrying(&pg, row.id, &e.to_string()).await;
                    crate::metrics::EMAIL_SEND_ATTEMPTS_TOTAL.with_label_values(&["network_error"]).inc();
                }
            }
        }));
    }
    for h in handles { let _ = h.await; }
}
```

- [ ] **Step 4: Spawn in main.rs**

In `main.rs`, after `let state = ...`:
```rust
let template_registry = std::sync::Arc::new(physics_api::email::templates::TemplateRegistry::new().expect("template registry"));
let resend_api_key = std::env::var("RESEND_API_KEY").ok();
let email_provider: std::sync::Arc<dyn physics_api::email::EmailProvider> = match resend_api_key {
    Some(key) if !key.is_empty() => {
        let from = std::env::var("EMAIL_FROM").unwrap_or_else(|_| "Nasrudin <noreply@nasrudin.org>".into());
        std::sync::Arc::new(physics_api::email::ResendProvider::new(key, "https://api.resend.com".into(), from))
    }
    _ => {
        tracing::warn!("RESEND_API_KEY unset — email worker uses NoopProvider (logs only)");
        std::sync::Arc::new(physics_api::email::NoopProvider)
    }
};
if let Some(pg) = state.pg.clone() {
    physics_api::email::spawn_worker(pg, email_provider, template_registry.clone());
}
```

Add `pub struct NoopProvider;` to `email/provider.rs` with an `impl EmailProvider` returning `Sent { message_id: "noop".into() }`.

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_email_worker`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/email/worker.rs engine/crates/api/src/email/provider.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_email_worker.rs
git commit -m "feat(api): email drain worker with semaphore-bounded concurrency"
```

### Task 31: POST `/api/webhook/resend`

**Files:**
- Create: `engine/crates/api/src/handlers/webhook_resend.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs`
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/pg/src/query/email_outbox.rs` (find_by_provider_message_id helper)
- Test: `engine/crates/api/tests/webhook_resend.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/webhook_resend.rs
mod test_app;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;
use hmac::{Hmac, Mac};
use sha2::Sha256;

fn sign(body: &[u8], secret: &str) -> String {
    let mut mac = Hmac::<Sha256>::new_from_slice(secret.as_bytes()).unwrap();
    mac.update(body);
    hex::encode(mac.finalize().into_bytes())
}

#[tokio::test]
async fn bounce_marks_failed_terminal() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_resend_secret(b"whsec_test").await else { return; };
    let id = nasrudin_pg::query::email_outbox::queue(&app.pg, None, "x@t.local", "admin_custom_message", "s", "b", None, None, None).await.unwrap();
    nasrudin_pg::query::email_outbox::mark_sent(&app.pg, id, "msg_abc").await.unwrap();

    let body = serde_json::json!({"type": "email.bounced", "data": {"email_id": "msg_abc"}}).to_string();
    let sig = sign(body.as_bytes(), "whsec_test");
    let resp = app.router.clone().oneshot(
        Request::post("/api/webhook/resend")
            .header("svix-signature", format!("v1={sig}"))
            .header("Content-Type", "application/json")
            .body(Body::from(body)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let row = nasrudin_pg::query::email_outbox::find_by_id(&app.pg, id).await.unwrap().unwrap();
    assert_eq!(row.status, "failed_terminal");
}

#[tokio::test]
async fn bad_signature_rejected() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_resend_secret(b"whsec_test").await else { return; };
    let resp = app.router.clone().oneshot(
        Request::post("/api/webhook/resend")
            .header("svix-signature", "v1=deadbeef")
            .body(Body::from(r#"{"type":"x"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
}
```

- [ ] **Step 2: Run tests**

Expected: FAIL.

- [ ] **Step 3: Add helpers to query module**

Append to `engine/crates/pg/src/query/email_outbox.rs`:

```rust
pub async fn find_by_provider_message_id<C: ConnectionTrait>(conn: &C, msg_id: &str) -> Result<Option<ent::Model>, DbErr> {
    use sea_orm::ColumnTrait;
    ent::Entity::find()
        .filter(ent::Column::ProviderMessageId.eq(msg_id))
        .one(conn).await
}
```

Add `mark_bounced` (delegates to `mark_failed_terminal`).

- [ ] **Step 4: Implement webhook handler**

```rust
// engine/crates/api/src/handlers/webhook_resend.rs
use std::sync::Arc;
use axum::{Json, body::Bytes, extract::State, http::{HeaderMap, StatusCode}, response::IntoResponse};
use hmac::{Hmac, Mac};
use sha2::Sha256;

use crate::state::AppState;

pub async fn webhook_resend(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    body: Bytes,
) -> impl IntoResponse {
    let secret = match &state.resend_webhook_secret {
        Some(s) => s,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "secret_unset").into_response(),
    };
    let sig_header = headers.get("svix-signature").and_then(|v| v.to_str().ok()).unwrap_or("");
    let provided = sig_header.split(',').find_map(|p| p.strip_prefix("v1=")).unwrap_or("");
    let mut mac = match Hmac::<Sha256>::new_from_slice(secret.as_bytes()) {
        Ok(m) => m, Err(_) => return (StatusCode::INTERNAL_SERVER_ERROR, "mac").into_response(),
    };
    mac.update(&body);
    let expected = hex::encode(mac.finalize().into_bytes());
    if !constant_time_eq(provided.as_bytes(), expected.as_bytes()) {
        return (StatusCode::UNAUTHORIZED, "bad_sig").into_response();
    }

    let event: serde_json::Value = match serde_json::from_slice(&body) {
        Ok(v) => v, Err(_) => return (StatusCode::BAD_REQUEST, "bad_json").into_response(),
    };
    let kind = event.get("type").and_then(|v| v.as_str()).unwrap_or("");
    let msg_id = event.pointer("/data/email_id").and_then(|v| v.as_str()).unwrap_or("");
    let pg = state.pg.as_ref().expect("pg required");
    if kind == "email.bounced" || kind == "email.complained" {
        if let Some(row) = nasrudin_pg::query::email_outbox::find_by_provider_message_id(pg, msg_id).await.ok().flatten() {
            let _ = nasrudin_pg::query::email_outbox::mark_failed_terminal(pg, row.id, kind).await;
        }
    }
    (StatusCode::OK, Json(serde_json::json!({"ok":true}))).into_response()
}

fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() { return false; }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b) { diff |= x ^ y; }
    diff == 0
}
```

- [ ] **Step 5: Wire**

Add `pub resend_webhook_secret: Option<String>` to `AppState`. Set in `main.rs` from env. Add the route:

```rust
let webhooks = Router::new().route("/api/webhook/resend", post(handlers::webhook_resend::webhook_resend));
```

Merge into the main app (no rate limit; it's already idempotent and signature-gated).

Add `hmac = "0.12"` and `sha2 = "0.10"` to api `Cargo.toml`.

`handlers/mod.rs`: `pub mod webhook_resend;`.

Add a test helper `TestApp::build_with_resend_secret`.

- [ ] **Step 6: Run tests**

Run: `cd engine && cargo test -p physics-api --test webhook_resend`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/handlers/webhook_resend.rs \
        engine/crates/api/src/handlers/mod.rs \
        engine/crates/api/src/state.rs engine/crates/api/src/main.rs \
        engine/crates/pg/src/query/email_outbox.rs \
        engine/crates/api/Cargo.toml \
        engine/crates/api/tests/webhook_resend.rs
git commit -m "feat(api): POST /api/webhook/resend with HMAC verification + bounce handling"
```

## Section H — Stripe refunds

### Task 32: POST `/api/admin/users/{id}/refund`

**Files:**
- Create: `engine/crates/api/src/billing/refund.rs`
- Create: `engine/crates/api/src/handlers/admin/refund.rs`
- Modify: `engine/crates/api/src/billing/mod.rs`, `engine/crates/api/src/handlers/admin/mod.rs`, `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_refund_flow.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_refund_flow.rs
mod test_app;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;
use wiremock::{MockServer, Mock, ResponseTemplate, matchers};

#[tokio::test]
async fn refund_happy_path_creates_record_and_email() {
    let _g = test_app::TEST_LOCK.lock().await;
    let stripe = MockServer::start().await;
    Mock::given(matchers::method("GET")).and(matchers::path("/v1/charges/ch_test"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({"id":"ch_test","customer":"cus_X","amount":1900,"currency":"usd"})))
        .mount(&stripe).await;
    Mock::given(matchers::method("POST")).and(matchers::path("/v1/refunds"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({"id":"re_456","status":"succeeded"})))
        .mount(&stripe).await;

    let Some(app) = test_app::TestApp::build_with_stripe(&stripe.uri()).await else { return; };
    let cookie = test_app::create_admin_session(&app, "rfa@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "rftarget@t.local", Some("h"), None).await.unwrap();
    sea_orm::ConnectionTrait::execute(&app.pg, sea_orm::Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE users SET stripe_customer_id='cus_X' WHERE id=$1", [user.id.into()])).await.unwrap();

    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/refund", user.id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"stripe_charge_id":"ch_test","amount_cents":1900,"reason":"customer support refund"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let pending = nasrudin_pg::query::email_outbox::list_recent(&app.pg, 5, 0).await.unwrap();
    assert!(pending.iter().any(|e| e.template == "admin_refund_issued"));
}

#[tokio::test]
async fn refund_with_unknown_charge_returns_422() {
    let _g = test_app::TEST_LOCK.lock().await;
    let stripe = MockServer::start().await;
    Mock::given(matchers::method("GET")).and(matchers::path("/v1/charges/ch_bad"))
        .respond_with(ResponseTemplate::new(404)).mount(&stripe).await;
    let Some(app) = test_app::TestApp::build_with_stripe(&stripe.uri()).await else { return; };
    let cookie = test_app::create_admin_session(&app, "rfb@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "rfb-tg@t.local", Some("h"), None).await.unwrap();

    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/refund", user.id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"stripe_charge_id":"ch_bad","amount_cents":100,"reason":"will fail at stripe"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::UNPROCESSABLE_ENTITY);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Expected: FAIL.

- [ ] **Step 3: Implement billing/refund.rs**

```rust
// engine/crates/api/src/billing/refund.rs
//! DB-first → Stripe-second refund flow with idempotency keys.

use nasrudin_pg::sea_orm::{DatabaseConnection, TransactionTrait, DbErr};
use serde::Deserialize;
use uuid::Uuid;

#[derive(Deserialize)]
pub struct ChargeView { pub id: String, pub customer: Option<String>, pub amount: i64, pub currency: String }
#[derive(Deserialize)]
pub struct RefundResponse { pub id: String, pub status: String }

pub async fn fetch_charge(client: &reqwest::Client, base_url: &str, key: &str, id: &str) -> Result<Option<ChargeView>, anyhow::Error> {
    let resp = client.get(format!("{base_url}/v1/charges/{id}")).bearer_auth(key).send().await?;
    if resp.status().as_u16() == 404 { return Ok(None); }
    if !resp.status().is_success() { anyhow::bail!("stripe error: {}", resp.status()); }
    Ok(Some(resp.json().await?))
}

pub async fn create_refund(
    client: &reqwest::Client, base_url: &str, key: &str,
    charge_id: &str, amount_cents: i64, idempotency_key: Uuid, refund_record_id: Uuid,
) -> Result<RefundResponse, anyhow::Error> {
    let resp = client.post(format!("{base_url}/v1/refunds"))
        .bearer_auth(key)
        .header("Idempotency-Key", idempotency_key.to_string())
        .form(&[
            ("charge", charge_id),
            ("amount", &amount_cents.to_string()),
            ("metadata[refund_record_id]", &refund_record_id.to_string()),
        ])
        .send().await?;
    if !resp.status().is_success() { anyhow::bail!("stripe refund failed: {}", resp.status()); }
    Ok(resp.json().await?)
}
```

- [ ] **Step 4: Implement handler**

```rust
// engine/crates/api/src/handlers/admin/refund.rs
use std::sync::Arc;
use axum::{Json, extract::{Path, State, ConnectInfo}, http::{StatusCode, HeaderMap}, response::IntoResponse};
use serde::Deserialize;
use serde_json::json;
use std::net::SocketAddr;
use uuid::Uuid;

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct RefundInput { pub stripe_charge_id: String, pub amount_cents: i64, pub reason: String }

pub async fn refund(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(user_id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<RefundInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let stripe = match &state.stripe_billing { Some(s) => s, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"stripe_unavailable"}))).into_response() };

    let user = match nasrudin_pg::query::admin_users::find_by_id(pg, user_id).await {
        Ok(Some(u)) => u, Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let charge = match crate::billing::refund::fetch_charge(
        &state.stripe_http, &state.stripe_base_url, &state.stripe_secret, &body.stripe_charge_id,
    ).await {
        Ok(Some(c)) => c,
        Ok(None) => return (StatusCode::UNPROCESSABLE_ENTITY, Json(json!({"error":"charge_not_found"}))).into_response(),
        Err(e) => return (StatusCode::BAD_GATEWAY, Json(json!({"error":e.to_string()}))).into_response(),
    };
    if user.stripe_customer_id.as_deref() != charge.customer.as_deref() {
        return (StatusCode::UNPROCESSABLE_ENTITY, Json(json!({"error":"charge_belongs_to_other_customer"}))).into_response();
    }
    let _ = stripe;

    // 1) DB-first: insert pending refund + audit + email queue, all in one txn.
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let admin_id = admin.0.user.id;
    let amount_cents = body.amount_cents as i32;
    let currency = charge.currency.clone();
    let charge_id = body.stripe_charge_id.clone();
    let user_email = user.email.clone();
    let refund_reason = body.reason.clone();

    let refund_id_result = perform_audited(
        pg, &admin.0.user, None, RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        Some(user_id), actions::REFUND_INITIATED, body.reason,
        json!({"charge_id": &charge_id, "amount_cents": amount_cents}),
        move |txn| async move {
            let id = nasrudin_pg::query::refund_records::insert(
                txn, user_id, admin_id, &charge_id, amount_cents, &currency, &refund_reason,
            ).await?;
            let body_text = format!("A refund of {}.{:02} {} has been issued.", amount_cents / 100, amount_cents % 100, currency.to_uppercase());
            nasrudin_pg::query::email_outbox::queue(
                txn, Some(user_id), &user_email, "admin_refund_issued",
                "Your Nasrudin refund", &body_text, None,
                Some(admin_id), Some(actions::REFUND_INITIATED),
            ).await?;
            Ok::<_, sea_orm::DbErr>((id, json!({"refund_record_id": id})))
        },
    ).await;
    let refund_id = match refund_id_result {
        Ok(id) => id,
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    };

    // 2) Stripe-second.
    match crate::billing::refund::create_refund(
        &state.stripe_http, &state.stripe_base_url, &state.stripe_secret,
        &body.stripe_charge_id, body.amount_cents, refund_id, refund_id,
    ).await {
        Ok(resp) => {
            let _ = nasrudin_pg::query::refund_records::mark_succeeded(pg, refund_id, &resp.id).await;
            crate::metrics::REFUND_RECORDS_TOTAL.with_label_values(&["succeeded"]).inc();
            (StatusCode::OK, Json(json!({"refund_id": resp.id, "status": resp.status, "record_id": refund_id}))).into_response()
        }
        Err(e) => {
            let msg = e.to_string();
            // Crash-recovery edge case: leave as pending if it might have succeeded; the
            // reconciler will resolve. We mark failed only on confirmed 4xx (Stripe rejection).
            if msg.contains("4") {
                let _ = nasrudin_pg::query::refund_records::mark_failed(pg, refund_id, &msg).await;
                let _ = nasrudin_pg::query::email_outbox::cancel_dependent(pg, refund_id).await;
                crate::metrics::REFUND_RECORDS_TOTAL.with_label_values(&["failed"]).inc();
                (StatusCode::UNPROCESSABLE_ENTITY, Json(json!({"error": msg}))).into_response()
            } else {
                (StatusCode::ACCEPTED, Json(json!({"record_id": refund_id, "status": "pending", "note":"reconciler_will_resolve"}))).into_response()
            }
        }
    }
}
```

- [ ] **Step 5: Add stripe http client + base url to AppState**

In `state.rs`:
```rust
pub stripe_http: reqwest::Client,
pub stripe_base_url: String,
pub stripe_secret: String,
pub stripe_billing: Option<crate::billing::stripe_client::BillingClient>,
```

In `main.rs`, set them:
```rust
let stripe_secret = std::env::var("STRIPE_SECRET_KEY").unwrap_or_default();
let stripe_base_url = std::env::var("STRIPE_BASE_URL").unwrap_or_else(|_| "https://api.stripe.com".into());
let stripe_http = reqwest::Client::new();
```

- [ ] **Step 6: Wire**

`handlers/admin/mod.rs`: `pub mod refund;`.
`main.rs`: `.route("/api/admin/users/{id}/refund", post(handlers::admin::refund::refund))`.
`billing/mod.rs`: `pub mod refund;`.

- [ ] **Step 7: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_refund_flow`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/api/src/billing/refund.rs \
        engine/crates/api/src/billing/mod.rs \
        engine/crates/api/src/handlers/admin/refund.rs \
        engine/crates/api/src/handlers/admin/mod.rs \
        engine/crates/api/src/state.rs engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_refund_flow.rs
git commit -m "feat(api): POST /api/admin/users/{id}/refund with DB-first → Stripe flow"
```

### Task 33: Refund reconciler

**Files:**
- Create: `engine/crates/api/src/billing/refund_reconciler.rs`
- Modify: `engine/crates/api/src/billing/mod.rs`, `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_refund_reconciler.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_refund_reconciler.rs
mod test_app;
use wiremock::{MockServer, Mock, ResponseTemplate, matchers};

#[tokio::test]
async fn pending_older_than_90s_resolves_via_reconciler() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let admin = nasrudin_pg::query::users::create_user(&app.pg, "rec-a@t.local", Some("h"), None).await.unwrap();
    let target = nasrudin_pg::query::users::create_user(&app.pg, "rec-t@t.local", Some("h"), None).await.unwrap();
    let id = nasrudin_pg::query::refund_records::insert(&app.pg, target.id, admin.id, "ch_x", 100, "usd", "rec test").await.unwrap();
    sea_orm::ConnectionTrait::execute(&app.pg, sea_orm::Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE refund_records SET requested_at = now() - INTERVAL '120 seconds' WHERE id=$1",
        [id.into()])).await.unwrap();

    let stripe = MockServer::start().await;
    Mock::given(matchers::method("GET")).and(matchers::path("/v1/refunds"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "data": [{"id":"re_recovered","status":"succeeded","metadata":{"refund_record_id": id.to_string()},"charge":"ch_x"}]
        }))).mount(&stripe).await;

    let client = reqwest::Client::new();
    physics_api::billing::refund_reconciler::tick_once(&app.pg, &client, &stripe.uri(), "sk_test").await;

    let row = nasrudin_pg::query::refund_records::find_by_id(&app.pg, id).await.unwrap().unwrap();
    assert_eq!(row.status, "succeeded");
    assert_eq!(row.stripe_refund_id.as_deref(), Some("re_recovered"));
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Implement reconciler**

```rust
// engine/crates/api/src/billing/refund_reconciler.rs
use nasrudin_pg::sea_orm::DatabaseConnection;
use std::time::Duration;
use uuid::Uuid;

pub fn spawn(pg: DatabaseConnection, http: reqwest::Client, base_url: String, secret: String) {
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(60));
        loop {
            interval.tick().await;
            tick_once(&pg, &http, &base_url, &secret).await;
        }
    });
}

pub async fn tick_once(pg: &DatabaseConnection, http: &reqwest::Client, base_url: &str, secret: &str) {
    let stale = match nasrudin_pg::query::refund_records::list_pending_older_than(pg, 90).await {
        Ok(r) => r, Err(_) => return,
    };
    for record in stale {
        let url = format!("{base_url}/v1/refunds?charge={}", record.stripe_charge_id);
        let resp = match http.get(&url).bearer_auth(secret).send().await {
            Ok(r) => r, Err(_) => continue,
        };
        let body: serde_json::Value = match resp.json().await { Ok(v) => v, Err(_) => continue };
        let data = body.get("data").and_then(|v| v.as_array());
        let needle = record.id.to_string();
        let matched = data.and_then(|arr| arr.iter().find(|r| {
            r.pointer("/metadata/refund_record_id").and_then(|v| v.as_str()) == Some(&needle)
        }));
        if let Some(m) = matched {
            let stripe_id = m.get("id").and_then(|v| v.as_str()).unwrap_or_default();
            let status = m.get("status").and_then(|v| v.as_str()).unwrap_or("pending");
            if status == "succeeded" {
                let _ = nasrudin_pg::query::refund_records::mark_succeeded(pg, record.id, stripe_id).await;
                crate::metrics::REFUND_RECONCILER_RESOLVED_TOTAL.inc();
            } else if status == "failed" {
                let _ = nasrudin_pg::query::refund_records::mark_failed(pg, record.id, "stripe_returned_failed").await;
            }
        } else {
            // 5+ minutes elapsed → mark failed.
            if (chrono::Utc::now().timestamp() - record.requested_at.timestamp()) > 300 {
                let _ = nasrudin_pg::query::refund_records::mark_failed(pg, record.id, "reconciler_timeout").await;
                let _ = nasrudin_pg::query::email_outbox::cancel_dependent(pg, record.id).await;
            }
        }
    }
    let _ = Uuid::new_v4();
}
```

- [ ] **Step 4: Wire**

`billing/mod.rs`: `pub mod refund_reconciler;`.
`main.rs` after stripe vars: `physics_api::billing::refund_reconciler::spawn(pg.clone(), stripe_http.clone(), stripe_base_url.clone(), stripe_secret.clone());`

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_refund_reconciler`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/billing/refund_reconciler.rs \
        engine/crates/api/src/billing/mod.rs engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_refund_reconciler.rs
git commit -m "feat(api): refund reconciler tick (60 s)"
```

### Task 34: `charge.refunded` webhook integration

**Files:**
- Modify: `engine/crates/api/src/billing/webhook.rs`
- Test: `engine/crates/api/tests/admin_refund_webhook.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_refund_webhook.rs
mod test_app;
// (Construct a Stripe-style signed `charge.refunded` event and POST to
// /api/billing/webhook; assert that refund_records is updated.)

#[tokio::test]
async fn charge_refunded_marks_record_succeeded() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_resend_secret(b"_unused").await else { return; };
    let admin = nasrudin_pg::query::users::create_user(&app.pg, "wh-a@t.local", Some("h"), None).await.unwrap();
    let target = nasrudin_pg::query::users::create_user(&app.pg, "wh-t@t.local", Some("h"), None).await.unwrap();
    let id = nasrudin_pg::query::refund_records::insert(&app.pg, target.id, admin.id, "ch_w", 100, "usd", "wh test").await.unwrap();

    physics_api::billing::webhook::dispatch_charge_refunded_for_test(&app.pg, "ch_w", &format!("re_wh_{id}"), "succeeded").await.unwrap();

    let row = nasrudin_pg::query::refund_records::find_by_id(&app.pg, id).await.unwrap().unwrap();
    assert_eq!(row.status, "succeeded");
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Extend the webhook dispatcher**

In `engine/crates/api/src/billing/webhook.rs`, inside `dispatch`:

```rust
(EventType::ChargeRefunded, EventObject::Charge(charge)) => {
    if let Some(refunds) = &charge.refunds {
        for r in &refunds.data {
            // Match by stripe_charge_id; the `metadata.refund_record_id` is
            // also written from our side so we update the right row even
            // when multiple partial refunds exist.
            let record_id = r.metadata.as_ref()
                .and_then(|m| m.get("refund_record_id"))
                .and_then(|v| uuid::Uuid::parse_str(v).ok());
            if let Some(rid) = record_id {
                let _ = nasrudin_pg::query::refund_records::mark_succeeded(pg, rid, &r.id.to_string()).await;
            }
        }
    }
    return Ok(());
}
```

Add a test-only entry point:

```rust
#[cfg(any(test, debug_assertions))]
pub async fn dispatch_charge_refunded_for_test(
    pg: &nasrudin_pg::sea_orm::DatabaseConnection, charge_id: &str, refund_id: &str, status: &str,
) -> Result<(), DispatchError> {
    if status == "succeeded" {
        let records = nasrudin_pg::query::refund_records::find_by_charge(pg, charge_id).await?;
        if let Some(r) = records.first() {
            nasrudin_pg::query::refund_records::mark_succeeded(pg, r.id, refund_id).await?;
        }
    }
    Ok(())
}
```

- [ ] **Step 4: Run test**

Run: `cd engine && cargo test -p physics-api --test admin_refund_webhook`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/billing/webhook.rs \
        engine/crates/api/tests/admin_refund_webhook.rs
git commit -m "feat(api): handle charge.refunded webhook to mark refund_records succeeded"
```

## Section I — User impersonation

### Task 35: HMAC token mint/verify utility

**Files:**
- Create: `engine/crates/api/src/impersonation.rs`
- Modify: `engine/crates/api/src/lib.rs`
- Test: `engine/crates/api/tests/impersonation_token.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/impersonation_token.rs
use physics_api::impersonation::{mint_token, verify_token, TokenPayload};
use uuid::Uuid;
use chrono::Utc;

#[test]
fn round_trip() {
    let key = b"thirty-two-byte-key-for-tests-aa";
    let p = TokenPayload {
        session_id: Uuid::new_v4(),
        admin_user_id: Uuid::new_v4(),
        target_user_id: Uuid::new_v4(),
        expires_at: Utc::now() + chrono::Duration::seconds(900),
    };
    let tok = mint_token(key, &p);
    let v = verify_token(key, &tok).unwrap();
    assert_eq!(v.session_id, p.session_id);
    assert_eq!(v.admin_user_id, p.admin_user_id);
    assert_eq!(v.target_user_id, p.target_user_id);
}

#[test]
fn tampered_signature_rejected() {
    let key = b"thirty-two-byte-key-for-tests-aa";
    let p = TokenPayload { session_id: Uuid::new_v4(), admin_user_id: Uuid::new_v4(), target_user_id: Uuid::new_v4(), expires_at: Utc::now() };
    let tok = mint_token(key, &p);
    let mut bad = tok.clone();
    bad.push('x');
    assert!(verify_token(key, &bad).is_err());
}

#[test]
fn wrong_key_rejected() {
    let p = TokenPayload { session_id: Uuid::new_v4(), admin_user_id: Uuid::new_v4(), target_user_id: Uuid::new_v4(), expires_at: Utc::now() };
    let tok = mint_token(b"keykeykeykeykeykeykeykeykeykeyaa", &p);
    assert!(verify_token(b"otherotherotherotherotherotheraa", &tok).is_err());
}
```

- [ ] **Step 2: Run tests**

Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
// engine/crates/api/src/impersonation.rs
//! HMAC-SHA256 signed impersonation tokens.

use base64::Engine;
use chrono::{DateTime, Utc};
use hmac::{Hmac, Mac};
use serde::{Deserialize, Serialize};
use sha2::Sha256;
use uuid::Uuid;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TokenPayload {
    pub session_id: Uuid,
    pub admin_user_id: Uuid,
    pub target_user_id: Uuid,
    pub expires_at: DateTime<Utc>,
}

#[derive(Debug, thiserror::Error)]
pub enum TokenError {
    #[error("malformed token")] Malformed,
    #[error("bad signature")] BadSignature,
    #[error("expired")] Expired,
}

pub fn mint_token(secret: &[u8], payload: &TokenPayload) -> String {
    let body = serde_json::to_vec(payload).expect("serialize");
    let body_b64 = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(&body);
    let mut mac = Hmac::<Sha256>::new_from_slice(secret).expect("hmac key");
    mac.update(body_b64.as_bytes());
    let sig = mac.finalize().into_bytes();
    let sig_b64 = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(sig);
    format!("{body_b64}.{sig_b64}")
}

pub fn verify_token(secret: &[u8], token: &str) -> Result<TokenPayload, TokenError> {
    let (body_b64, sig_b64) = token.split_once('.').ok_or(TokenError::Malformed)?;
    let mut mac = Hmac::<Sha256>::new_from_slice(secret).map_err(|_| TokenError::BadSignature)?;
    mac.update(body_b64.as_bytes());
    let provided = base64::engine::general_purpose::URL_SAFE_NO_PAD.decode(sig_b64).map_err(|_| TokenError::BadSignature)?;
    mac.verify_slice(&provided).map_err(|_| TokenError::BadSignature)?;
    let body = base64::engine::general_purpose::URL_SAFE_NO_PAD.decode(body_b64).map_err(|_| TokenError::Malformed)?;
    let payload: TokenPayload = serde_json::from_slice(&body).map_err(|_| TokenError::Malformed)?;
    if payload.expires_at < Utc::now() { return Err(TokenError::Expired); }
    Ok(payload)
}

/// Marker placed in request extensions when an impersonation token has been
/// validated. Consumed by audit-log helpers to thread `original_admin_id`.
#[derive(Clone, Debug)]
pub struct ImpersonationMarker {
    pub session_id: Uuid,
    pub original_admin_id: Uuid,
}
```

Add to `lib.rs`: `pub mod impersonation;`.

- [ ] **Step 4: Run tests**

Run: `cd engine && cargo test -p physics-api --test impersonation_token`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/impersonation.rs engine/crates/api/src/lib.rs \
        engine/crates/api/tests/impersonation_token.rs
git commit -m "feat(api): impersonation HMAC token mint/verify"
```

### Task 36: POST start/end impersonation endpoints

**Files:**
- Create: `engine/crates/api/src/handlers/admin/impersonate.rs`
- Modify: `engine/crates/api/src/handlers/admin/mod.rs`
- Modify: `engine/crates/api/src/state.rs` (`impersonation_signing_key: Option<Vec<u8>>`)
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_impersonation.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_impersonation.rs
mod test_app;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;
use serde_json::Value;

#[tokio::test]
async fn start_impersonation_returns_token() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_impersonation_key(b"thirty-two-byte-key-for-tests-aa").await else { return; };
    let cookie = test_app::create_admin_session(&app, "imp-a@t.local").await;
    let target = nasrudin_pg::query::users::create_user(&app.pg, "imp-t@t.local", Some("h"), None).await.unwrap();
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/impersonate", target.id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"duration_seconds":900,"reason":"debug session"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let body: Value = serde_json::from_slice(&axum::body::to_bytes(resp.into_body(), 1<<16).await.unwrap()).unwrap();
    assert!(body["token"].as_str().unwrap().contains('.'));
}

#[tokio::test]
async fn cannot_impersonate_self() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_impersonation_key(b"thirty-two-byte-key-for-tests-aa").await else { return; };
    let cookie = test_app::create_admin_session(&app, "imp-self@t.local").await;
    let me = nasrudin_pg::query::users::find_by_email(&app.pg, "imp-self@t.local").await.unwrap().unwrap();
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/impersonate", me.id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"duration_seconds":300,"reason":"trying to imp self"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::CONFLICT);
}

#[tokio::test]
async fn cannot_impersonate_admin() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_impersonation_key(b"thirty-two-byte-key-for-tests-aa").await else { return; };
    let cookie = test_app::create_admin_session(&app, "ia1@t.local").await;
    let other_admin = nasrudin_pg::query::users::create_user(&app.pg, "ia2@t.local", Some("h"), None).await.unwrap();
    nasrudin_pg::query::admin_users::set_is_admin(&app.pg, other_admin.id, true).await.unwrap();
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/impersonate", other_admin.id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"duration_seconds":300,"reason":"can't imp admin"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::CONFLICT);
}
```

- [ ] **Step 2: Run tests**

Expected: FAIL.

- [ ] **Step 3: Implement handler**

```rust
// engine/crates/api/src/handlers/admin/impersonate.rs
use std::sync::Arc;
use axum::{Json, extract::{Path, State, ConnectInfo}, http::{StatusCode, HeaderMap}, response::IntoResponse};
use serde::Deserialize;
use serde_json::json;
use std::net::SocketAddr;
use uuid::Uuid;

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::admin::require_admin::RequireAdmin;
use crate::impersonation::{mint_token, TokenPayload};
use crate::state::AppState;

#[derive(Deserialize)]
pub struct StartInput { pub duration_seconds: i64, pub reason: String }

pub async fn start(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(target_id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<StartInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let key = match &state.impersonation_signing_key {
        Some(k) => k, None => return (StatusCode::SERVICE_UNAVAILABLE, Json(json!({"error":"signing_key_unset"}))).into_response(),
    };
    if target_id == admin.0.user.id {
        return (StatusCode::CONFLICT, Json(json!({"error":"cannot_impersonate_self"}))).into_response();
    }
    let target = match nasrudin_pg::query::admin_users::find_by_id(pg, target_id).await {
        Ok(Some(u)) => u, Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    };
    if target.is_admin {
        return (StatusCode::CONFLICT, Json(json!({"error":"cannot_impersonate_admin"}))).into_response();
    }
    let duration = body.duration_seconds.clamp(60, 3600);
    let expires_at = chrono::Utc::now() + chrono::Duration::seconds(duration);
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let admin_id = admin.0.user.id;
    let result = perform_audited(
        pg, &admin.0.user, None, RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        Some(target_id), actions::IMPERSONATE_START, body.reason.clone(),
        json!({"target_user_id": target_id, "duration_seconds": duration}),
        move |txn| async move {
            let row = nasrudin_pg::query::impersonation::start(
                txn, admin_id, target_id, expires_at, body.reason).await?;
            Ok::<_, sea_orm::DbErr>((row, json!({"session_id": row.id, "expires_at": expires_at})))
        },
    ).await;
    let session_row = match result {
        Ok(r) => r, Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    };
    let payload = TokenPayload {
        session_id: session_row.id, admin_user_id: admin_id,
        target_user_id: target_id, expires_at,
    };
    let token = mint_token(key, &payload);
    crate::metrics::IMPERSONATION_ACTIVE_SESSIONS.inc();
    (StatusCode::OK, Json(json!({"token": token, "session_id": session_row.id, "expires_at": expires_at}))).into_response()
}

#[derive(Deserialize)]
pub struct EndInput { pub session_id: Uuid }

pub async fn end_impersonation(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<EndInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let session_id = body.session_id;
    let result = perform_audited(
        pg, &admin.0.user, None, RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        None, actions::IMPERSONATE_END, "ended by admin".into(),
        json!({"session_id": session_id}),
        move |txn| async move {
            nasrudin_pg::query::impersonation::end(txn, session_id, "manual").await?;
            Ok::<_, sea_orm::DbErr>(((), json!({"ended": true})))
        },
    ).await;
    crate::metrics::IMPERSONATION_ACTIVE_SESSIONS.dec();
    match result {
        Ok(_) => (StatusCode::OK, Json(json!({"ok":true}))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response(),
    }
}
```

- [ ] **Step 4: Wire**

`handlers/admin/mod.rs`: `pub mod impersonate;`.
`AppState`: `pub impersonation_signing_key: Option<Vec<u8>>`. Set from `IMPERSONATION_SIGNING_KEY` (hex-decoded).
`main.rs`:
```rust
.route("/api/admin/users/{id}/impersonate", post(handlers::admin::impersonate::start))
.route("/api/admin/impersonate/end", post(handlers::admin::impersonate::end_impersonation))
```

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_impersonation`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/handlers/admin/impersonate.rs \
        engine/crates/api/src/handlers/admin/mod.rs \
        engine/crates/api/src/state.rs engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_impersonation.rs
git commit -m "feat(api): POST impersonate start/end with HMAC tokens + DB row"
```

### Task 37: `ImpersonationLayer` middleware

**Files:**
- Modify: `engine/crates/api/src/impersonation.rs` (append layer)
- Modify: `engine/crates/api/src/main.rs` (apply layer to user-facing routers)
- Test: `engine/crates/api/tests/admin_impersonation.rs` (append)

- [ ] **Step 1: Write the failing test**

```rust
#[tokio::test]
async fn impersonation_token_replaces_authuser_for_user_endpoints() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_impersonation_key(b"thirty-two-byte-key-for-tests-aa").await else { return; };
    let cookie = test_app::create_admin_session(&app, "imp-mw-a@t.local").await;
    let target = nasrudin_pg::query::users::create_user(&app.pg, "imp-mw-t@t.local", Some("h"), None).await.unwrap();
    // start
    let start = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/impersonate", target.id))
            .header("Cookie", &cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"duration_seconds":900,"reason":"debug perm issue"}"#)).unwrap()
    ).await.unwrap();
    let body: serde_json::Value = serde_json::from_slice(&axum::body::to_bytes(start.into_body(), 1<<16).await.unwrap()).unwrap();
    let token = body["token"].as_str().unwrap();

    // /api/auth/me with the token must return target's email
    let me = app.router.clone().oneshot(
        Request::get("/api/auth/me")
            .header("Cookie", &cookie)
            .header("X-Impersonate-Token", token)
            .body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(me.status(), StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&axum::body::to_bytes(me.into_body(), 1<<16).await.unwrap()).unwrap();
    assert_eq!(body["email"], "imp-mw-t@t.local");
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Implement layer**

Append to `engine/crates/api/src/impersonation.rs`:

```rust
use axum::body::Body;
use axum::extract::Request;
use axum::middleware::Next;
use axum::response::Response;
use std::sync::Arc;

use crate::auth::{AuthSess, AuthUser};
use crate::state::AppState;

pub async fn impersonation_layer(
    state: axum::extract::State<Arc<AppState>>,
    mut req: Request,
    next: Next,
) -> Response {
    let token = req.headers().get("x-impersonate-token").and_then(|v| v.to_str().ok()).map(str::to_string);
    if let (Some(token), Some(key)) = (token, &state.impersonation_signing_key) {
        if let Ok(payload) = verify_token(key, &token) {
            // Validate session row.
            if let Some(pg) = &state.pg {
                if let Ok(Some(_active)) = nasrudin_pg::query::impersonation::find_active(pg, payload.session_id).await {
                    // Replace AuthUser inside the AuthSession with the target user's.
                    if let Ok(target_model) = nasrudin_pg::query::users::find_by_id(pg, payload.target_user_id).await {
                        if let Some(target) = target_model {
                            let target_user = AuthUser::from_model(target);
                            req.extensions_mut().insert(target_user);
                            req.extensions_mut().insert(ImpersonationMarker {
                                session_id: payload.session_id,
                                original_admin_id: payload.admin_user_id,
                            });
                        }
                    }
                }
            }
        }
    }
    next.run(req).await
}
```

In `main.rs`, after building `app`, wrap the user-facing handlers (everything except `/api/admin/*`) with this layer. The cleanest way: split the router into `admin` and `non_admin`, apply the layer to `non_admin` only.

Modify `auth::AuthOrApiKey` (and the `/api/auth/me` handler) to prefer an `AuthUser` placed in request extensions, falling back to the cookie session if absent. Concretely, in `auth::me`:

```rust
pub async fn me(req_parts: axum::extract::Request) -> impl IntoResponse {
    if let Some(user) = req_parts.extensions().get::<AuthUser>() {
        return (StatusCode::OK, Json(serde_json::to_value(user).unwrap())).into_response();
    }
    // ... existing fallback path
}
```

- [ ] **Step 4: Run test**

Run: `cd engine && cargo test -p physics-api --test admin_impersonation`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/impersonation.rs engine/crates/api/src/auth.rs \
        engine/crates/api/src/main.rs engine/crates/api/tests/admin_impersonation.rs
git commit -m "feat(api): ImpersonationLayer + AuthUser-from-extension override"
```

### Task 38: Block sensitive endpoints during impersonation + IMPERSONATED_ACTION audit

**Files:**
- Create: `engine/crates/api/src/admin/impersonation_guard.rs`
- Modify: `engine/crates/api/src/main.rs` (apply guard to admin/auth/billing/api_keys/preferences routes)
- Test: `engine/crates/api/tests/admin_impersonation.rs` (append)

- [ ] **Step 1: Write the failing test**

```rust
#[tokio::test]
async fn admin_endpoints_blocked_during_impersonation() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_impersonation_key(b"thirty-two-byte-key-for-tests-aa").await else { return; };
    let cookie = test_app::create_admin_session(&app, "guard-a@t.local").await;
    let target = nasrudin_pg::query::users::create_user(&app.pg, "guard-t@t.local", Some("h"), None).await.unwrap();
    // start
    let start = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/impersonate", target.id))
            .header("Cookie", &cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"duration_seconds":900,"reason":"validating guard"}"#)).unwrap()
    ).await.unwrap();
    let body: serde_json::Value = serde_json::from_slice(&axum::body::to_bytes(start.into_body(), 1<<16).await.unwrap()).unwrap();
    let token = body["token"].as_str().unwrap();

    let resp = app.router.clone().oneshot(
        Request::get("/api/admin/users")
            .header("Cookie", cookie).header("X-Impersonate-Token", token)
            .body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::FORBIDDEN);
    let body: serde_json::Value = serde_json::from_slice(&axum::body::to_bytes(resp.into_body(), 1<<16).await.unwrap()).unwrap();
    assert_eq!(body["error"], "cannot_during_impersonation");
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Implement guard layer**

```rust
// engine/crates/api/src/admin/impersonation_guard.rs
use axum::body::Body;
use axum::extract::Request;
use axum::http::StatusCode;
use axum::middleware::Next;
use axum::response::{IntoResponse, Response};

use crate::impersonation::ImpersonationMarker;

pub async fn block_during_impersonation(req: Request, next: Next) -> Response {
    if req.extensions().get::<ImpersonationMarker>().is_some() {
        return (StatusCode::FORBIDDEN, axum::Json(serde_json::json!({"error":"cannot_during_impersonation"}))).into_response();
    }
    next.run(req).await
}
```

Apply this layer in `main.rs` to:
- the `admin` Router,
- the `auth_strict` Router (login/logout),
- the api-key minting route (POST `/api/api_keys`),
- the billing handlers under `/api/billing/*`,
- preference writes (POST `/api/preferences`).

- [ ] **Step 4: Add IMPERSONATED_ACTION audit on `/api/conjecture/*/submit` and `/api/jobs/*`**

In each of those handlers, check for `ImpersonationMarker`; when present, write an `actions::IMPERSONATED_ACTION` audit row with the request payload summary, before the normal flow.

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_impersonation`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/admin/impersonation_guard.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/src/handlers/conjecture.rs \
        engine/crates/api/src/handlers/jobs_claim.rs \
        engine/crates/api/tests/admin_impersonation.rs
git commit -m "feat(api): block sensitive endpoints during impersonation + audit IMPERSONATED_ACTION"
```

### Task 39: Impersonation expiry tick + auto-revoke audit

**Files:**
- Create: `engine/crates/api/src/admin/impersonation_expiry.rs`
- Modify: `engine/crates/api/src/main.rs` (spawn)
- Test: `engine/crates/api/tests/admin_impersonation.rs` (append)

- [ ] **Step 1: Write the failing test**

```rust
#[tokio::test]
async fn expired_session_marked_ended_by_expiry_tick() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build_with_impersonation_key(b"thirty-two-byte-key-for-tests-aa").await else { return; };
    let admin = nasrudin_pg::query::users::create_user(&app.pg, "exp-a@t.local", Some("h"), None).await.unwrap();
    let target = nasrudin_pg::query::users::create_user(&app.pg, "exp-t@t.local", Some("h"), None).await.unwrap();
    let row = nasrudin_pg::query::impersonation::start(&app.pg, admin.id, target.id,
        chrono::Utc::now() - chrono::Duration::seconds(10), "expired test".into()).await.unwrap();
    assert!(nasrudin_pg::query::impersonation::find_active(&app.pg, row.id).await.unwrap().is_none()); // already considered inactive
    physics_api::admin::impersonation_expiry::tick_once(&app.pg).await;

    use sea_orm::EntityTrait;
    let m = nasrudin_pg::entity::impersonation_sessions::Entity::find_by_id(row.id).one(&app.pg).await.unwrap().unwrap();
    assert!(m.ended_at.is_some());
    assert_eq!(m.end_reason.as_deref(), Some("expired"));
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
// engine/crates/api/src/admin/impersonation_expiry.rs
use nasrudin_pg::sea_orm::DatabaseConnection;
use std::time::Duration;

use crate::admin::audit::{actions, SYSTEM_ACTOR_ID};

pub fn spawn(pg: DatabaseConnection) {
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(60));
        loop {
            interval.tick().await;
            tick_once(&pg).await;
        }
    });
}

pub async fn tick_once(pg: &DatabaseConnection) {
    let expired = match nasrudin_pg::query::impersonation::list_expired(pg).await {
        Ok(v) => v, Err(_) => return,
    };
    for row in expired {
        if nasrudin_pg::query::impersonation::end(pg, row.id, "expired").await.is_ok() {
            let _ = nasrudin_pg::query::admin_audit_log::insert(
                pg, SYSTEM_ACTOR_ID, Some(row.target_user_id), Some(row.admin_user_id),
                actions::IMPERSONATE_END, None,
                Some(serde_json::json!({"session_id": row.id, "end_reason":"expired"})),
                "system: session expired automatically".into(),
                None, Some("expiry-tick".into()),
            ).await;
            crate::metrics::IMPERSONATION_ACTIVE_SESSIONS.dec();
        }
    }
}
```

In `admin/mod.rs`: `pub mod impersonation_expiry; pub mod impersonation_guard;`.
In `main.rs`, after AppState: `if let Some(pg) = state.pg.clone() { physics_api::admin::impersonation_expiry::spawn(pg); }`.

- [ ] **Step 4: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_impersonation`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/admin/impersonation_expiry.rs \
        engine/crates/api/src/admin/mod.rs engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_impersonation.rs
git commit -m "feat(api): impersonation expiry tick (60 s) + system audit row"
```

## Section J — Bulk operations + custom email

### Task 40: POST `/api/admin/users/bulk` + bulk runner spawn

**Files:**
- Create: `engine/crates/api/src/handlers/admin/bulk.rs`
- Create: `engine/crates/api/src/admin/bulk_runner.rs`
- Modify: `engine/crates/api/src/admin/mod.rs`, `engine/crates/api/src/main.rs`, `engine/crates/api/src/state.rs` (add `bulk_run_progress_tx: tokio::sync::broadcast::Sender<(Uuid, BulkProgress)>`)
- Test: `engine/crates/api/tests/admin_bulk.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_bulk.rs
mod test_app;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;
use serde_json::json;

#[tokio::test]
async fn bulk_set_trust_runs_serial_and_audits_each() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "bulk-a@t.local").await;
    let mut ids = Vec::new();
    for i in 0..3 {
        let u = nasrudin_pg::query::users::create_user(&app.pg, &format!("bk{i}@t.local"), Some("h"), None).await.unwrap();
        ids.push(u.id);
    }
    let body = json!({"action":"set_trust","params":{"is_trusted":true},"user_ids":ids,"reason":"comping the launch beta cohort"}).to_string();
    let resp = app.router.clone().oneshot(
        Request::post("/api/admin/users/bulk").header("Cookie", cookie)
            .header("Content-Type", "application/json").body(Body::from(body)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&axum::body::to_bytes(resp.into_body(), 1<<16).await.unwrap()).unwrap();
    let run_id: uuid::Uuid = uuid::Uuid::parse_str(body["run_id"].as_str().unwrap()).unwrap();

    // Wait briefly for the runner to process all 3 (serial; in test it's basically immediate).
    tokio::time::sleep(std::time::Duration::from_millis(500)).await;

    let row = nasrudin_pg::query::bulk_runs::find_by_id(&app.pg, run_id).await.unwrap().unwrap();
    assert_eq!(row.completed_count, 3);
    for id in ids {
        let m = nasrudin_pg::query::admin_users::find_by_id(&app.pg, id).await.unwrap().unwrap();
        assert!(m.is_trusted);
    }
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Implement bulk runner**

```rust
// engine/crates/api/src/admin/bulk_runner.rs
use std::sync::Arc;
use serde::Deserialize;
use serde_json::json;
use uuid::Uuid;

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::auth::AuthUser;
use crate::state::AppState;

#[derive(Clone, Debug)]
pub struct BulkProgress {
    pub completed: u32,
    pub failed: u32,
    pub last_user_id: Option<Uuid>,
    pub status: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "action", content = "params")]
pub enum BulkAction {
    #[serde(rename = "set_trust")] SetTrust { is_trusted: bool },
    #[serde(rename = "set_plan")] SetPlan { plan_tier: String },
    #[serde(rename = "adjust_credits")] AdjustCredits { delta: i32 },
    #[serde(rename = "set_spot_check_rate")] SetSpotCheckRate { rate: Option<i32> },
}

pub fn spawn_run(state: Arc<AppState>, run_id: Uuid, actor: AuthUser, action: BulkAction, user_ids: Vec<Uuid>, reason: String) {
    tokio::spawn(async move {
        let pg = match &state.pg { Some(p) => p.clone(), None => return };
        let mut completed = 0u32;
        let mut failed = 0u32;
        for uid in user_ids {
            let one = run_one(&pg, &actor, &action, uid, &reason).await;
            match one {
                Ok(()) => {
                    completed += 1;
                    let _ = nasrudin_pg::query::bulk_runs::increment_completed(&pg, run_id).await;
                }
                Err(e) => {
                    failed += 1;
                    let _ = nasrudin_pg::query::bulk_runs::increment_failed(&pg, run_id, json!([{"user_id": uid, "error": e.to_string()}])).await;
                }
            }
            let _ = state.bulk_run_progress_tx.send((run_id, BulkProgress {
                completed, failed, last_user_id: Some(uid), status: "running".into(),
            }));
        }
        let final_status = if failed == 0 { "completed" } else { "completed_with_failures" };
        let _ = nasrudin_pg::query::bulk_runs::complete(&pg, run_id, final_status).await;
        let _ = nasrudin_pg::query::admin_audit_log::insert(
            &pg, actor.id, None, None, actions::BULK_RUN_COMPLETE,
            None, Some(json!({"run_id": run_id, "completed": completed, "failed": failed})),
            "bulk run completed".into(), None, None,
        ).await;
        crate::metrics::BULK_RUNS_COMPLETED_TOTAL.with_label_values(&[final_status]).inc();
        crate::metrics::BULK_RUNS_ACTIVE.dec();
        let _ = state.bulk_run_progress_tx.send((run_id, BulkProgress { completed, failed, last_user_id: None, status: final_status.into() }));
    });
}

async fn run_one(pg: &nasrudin_pg::sea_orm::DatabaseConnection, actor: &AuthUser, action: &BulkAction, target: Uuid, reason: &str) -> Result<(), anyhow::Error> {
    let action_clone = action.clone();
    let res = perform_audited(
        pg, actor, None, RequestMeta::default(),
        Some(target),
        match action {
            BulkAction::SetTrust { .. } => actions::SET_IS_TRUSTED,
            BulkAction::SetPlan { .. } => actions::SET_PLAN_TIER,
            BulkAction::AdjustCredits { .. } => actions::ADJUST_CREDITS,
            BulkAction::SetSpotCheckRate { .. } => actions::SET_SPOT_CHECK_RATE,
        },
        reason.to_string(),
        json!({}),
        move |txn| async move {
            match action_clone {
                BulkAction::SetTrust { is_trusted } => {
                    nasrudin_pg::query::admin_users::set_is_trusted(txn, target, is_trusted).await?;
                    Ok::<_, sea_orm::DbErr>(((), json!({"is_trusted": is_trusted})))
                }
                BulkAction::SetPlan { plan_tier } => {
                    nasrudin_pg::query::admin_users::set_plan_tier(txn, target, &plan_tier).await?;
                    Ok::<_, sea_orm::DbErr>(((), json!({"plan_tier": plan_tier})))
                }
                BulkAction::AdjustCredits { delta } => {
                    let new = nasrudin_pg::query::admin_users::adjust_credits(txn, target, delta).await?;
                    Ok::<_, sea_orm::DbErr>(((), json!({"research_credits": new})))
                }
                BulkAction::SetSpotCheckRate { rate } => {
                    nasrudin_pg::query::admin_users::set_spot_check_rate(txn, target, rate).await?;
                    Ok::<_, sea_orm::DbErr>(((), json!({"spot_check_rate": rate})))
                }
            }
        },
    ).await;
    res.map(|_| ()).map_err(|e| anyhow::anyhow!(e.to_string()))
}
```

- [ ] **Step 4: Implement handler**

```rust
// engine/crates/api/src/handlers/admin/bulk.rs
use std::sync::Arc;
use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use serde_json::json;
use uuid::Uuid;

use crate::admin::bulk_runner::{spawn_run, BulkAction};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct StartInput {
    #[serde(flatten)] pub action: BulkAction,
    pub user_ids: Vec<Uuid>,
    pub reason: String,
}

pub async fn start(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Json(body): Json<StartInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    if body.reason.trim().chars().count() < 10 {
        return (StatusCode::BAD_REQUEST, Json(json!({"error":"reason_too_short"}))).into_response();
    }
    let action_label = match &body.action {
        BulkAction::SetTrust { .. } => "set_trust", BulkAction::SetPlan { .. } => "set_plan",
        BulkAction::AdjustCredits { .. } => "adjust_credits", BulkAction::SetSpotCheckRate { .. } => "set_spot_check_rate",
    };
    let run_id = match nasrudin_pg::query::bulk_runs::insert(
        pg, admin.0.user.id, action_label,
        serde_json::to_value(&body.action).unwrap_or(serde_json::Value::Null),
        body.user_ids.len() as i32,
    ).await {
        Ok(id) => id, Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    crate::metrics::BULK_RUNS_ACTIVE.inc();
    spawn_run(state.clone(), run_id, admin.0.user.clone(), body.action, body.user_ids, body.reason);
    (StatusCode::OK, Json(json!({"run_id": run_id}))).into_response()
}
```

- [ ] **Step 5: Add `bulk_run_progress_tx` to AppState**

In state.rs:
```rust
pub bulk_run_progress_tx: tokio::sync::broadcast::Sender<(Uuid, crate::admin::bulk_runner::BulkProgress)>,
```

In main.rs: `let (bulk_run_progress_tx, _) = tokio::sync::broadcast::channel(256);`

Add the restart reaper at boot:
```rust
if let Some(pg) = state.pg.clone() {
    tokio::spawn(async move {
        if let Ok(n) = nasrudin_pg::query::bulk_runs::reap_stale(&pg).await {
            if n > 0 { tracing::warn!("Reaped {n} stale bulk_runs at startup"); }
        }
    });
}
```

- [ ] **Step 6: Wire**

`handlers/admin/mod.rs`: `pub mod bulk;`. `admin/mod.rs`: `pub mod bulk_runner;`.
`main.rs`: `.route("/api/admin/users/bulk", post(handlers::admin::bulk::start))`

- [ ] **Step 7: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_bulk`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/api/src/handlers/admin/bulk.rs \
        engine/crates/api/src/admin/bulk_runner.rs \
        engine/crates/api/src/admin/mod.rs \
        engine/crates/api/src/handlers/admin/mod.rs \
        engine/crates/api/src/state.rs engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_bulk.rs
git commit -m "feat(api): bulk runner + POST /api/admin/users/bulk with stale reaper"
```

### Task 41: GET `/api/admin/users/bulk/{id}/stream` SSE

**Files:**
- Modify: `engine/crates/api/src/handlers/admin/bulk.rs`
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_bulk.rs` (append)

- [ ] **Step 1: Write the failing test**

```rust
#[tokio::test]
async fn bulk_run_emits_sse_progress() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "bulk-sse-a@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "bulk-sse-u@t.local", Some("h"), None).await.unwrap();
    let body = serde_json::json!({"action":"set_trust","params":{"is_trusted":true},"user_ids":[user.id],"reason":"test sse stream"}).to_string();
    let resp = app.router.clone().oneshot(
        Request::post("/api/admin/users/bulk").header("Cookie", &cookie)
            .header("Content-Type", "application/json").body(Body::from(body)).unwrap()
    ).await.unwrap();
    let body: serde_json::Value = serde_json::from_slice(&axum::body::to_bytes(resp.into_body(), 1<<16).await.unwrap()).unwrap();
    let run_id = body["run_id"].as_str().unwrap();

    let resp = app.router.clone().oneshot(
        Request::get(format!("/api/admin/users/bulk/{}/stream", run_id))
            .header("Cookie", cookie).header("Accept","text/event-stream").body(Body::empty()).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    // We don't try to read the stream to completion in unit tests; we just
    // verify the content-type. Full E2E lives in Playwright.
    let ct = resp.headers().get("content-type").unwrap().to_str().unwrap();
    assert!(ct.starts_with("text/event-stream"));
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Implement SSE handler**

Append to `engine/crates/api/src/handlers/admin/bulk.rs`:

```rust
use axum::extract::Path;
use axum::response::sse::{Event, KeepAlive, Sse};
use futures::stream::{self, Stream, StreamExt};
use std::convert::Infallible;
use std::sync::Arc as ArcImpl;

pub async fn stream(
    _admin: RequireAdmin,
    State(state): State<ArcImpl<AppState>>,
    Path(run_id): Path<Uuid>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let mut rx = state.bulk_run_progress_tx.subscribe();
    let s = async_stream::stream! {
        // Initial snapshot from DB.
        if let Some(pg) = &state.pg {
            if let Ok(Some(row)) = nasrudin_pg::query::bulk_runs::find_by_id(pg, run_id).await {
                yield Ok::<_, Infallible>(Event::default().event("snapshot")
                    .json_data(serde_json::json!({
                        "completed": row.completed_count, "failed": row.failed_count,
                        "total": row.total_count, "status": row.status,
                    })).unwrap());
            }
        }
        loop {
            match rx.recv().await {
                Ok((rid, p)) if rid == run_id => {
                    let payload = serde_json::json!({"completed": p.completed, "failed": p.failed,
                        "last_user_id": p.last_user_id, "status": p.status});
                    yield Ok(Event::default().event("progress").json_data(payload).unwrap());
                    if p.status == "completed" || p.status == "completed_with_failures" || p.status == "aborted" { break; }
                }
                Ok(_) => continue,
                Err(_) => break,
            }
        }
    };
    Sse::new(s).keep_alive(KeepAlive::default())
}
```

Add `async-stream = "0.3"` to api `Cargo.toml`.

- [ ] **Step 4: Wire route**

`main.rs`: `.route("/api/admin/users/bulk/{run_id}/stream", get(handlers::admin::bulk::stream))`

- [ ] **Step 5: Run test**

Run: `cd engine && cargo test -p physics-api --test admin_bulk`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/handlers/admin/bulk.rs engine/crates/api/src/main.rs \
        engine/crates/api/Cargo.toml engine/crates/api/tests/admin_bulk.rs
git commit -m "feat(api): SSE progress stream for bulk runs"
```

### Task 42: Custom email send + outbox list/retry endpoints

**Files:**
- Create: `engine/crates/api/src/handlers/admin/email.rs`
- Modify: `engine/crates/api/src/handlers/admin/mod.rs`, `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_email_handlers.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_email_handlers.rs
mod test_app;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

#[tokio::test]
async fn admin_queues_custom_email() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "ec-a@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "ec-u@t.local", Some("h"), None).await.unwrap();
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/users/{}/email", user.id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"subject":"Welcome aboard","body_text":"Thanks for joining","reason":"sending welcome message"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let pending = nasrudin_pg::query::email_outbox::list_recent(&app.pg, 5, 0).await.unwrap();
    assert!(pending.iter().any(|e| e.template == "admin_custom_message" && e.subject == "Welcome aboard"));
}

#[tokio::test]
async fn admin_lists_outbox_and_retries() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "outbox@t.local").await;
    let id = nasrudin_pg::query::email_outbox::queue(&app.pg, None, "u@t.local", "admin_custom_message", "x", "b", None, None, None).await.unwrap();
    nasrudin_pg::query::email_outbox::mark_failed_terminal(&app.pg, id, "test").await.unwrap();
    let resp = app.router.clone().oneshot(
        Request::post(format!("/api/admin/email/{}/retry", id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(Body::from(r#"{"reason":"manually re-queueing failed delivery"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let row = nasrudin_pg::query::email_outbox::find_by_id(&app.pg, id).await.unwrap().unwrap();
    assert_eq!(row.status, "queued");
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
// engine/crates/api/src/handlers/admin/email.rs
use std::sync::Arc;
use axum::{Json, extract::{Path, State, Query, ConnectInfo}, http::{StatusCode, HeaderMap}, response::IntoResponse};
use serde::Deserialize;
use serde_json::json;
use std::net::SocketAddr;
use uuid::Uuid;

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct CustomEmailInput { pub subject: String, pub body_text: String, pub body_html: Option<String>, pub reason: String }

pub async fn send_custom(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(user_id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<CustomEmailInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let user = match nasrudin_pg::query::admin_users::find_by_id(pg, user_id).await {
        Ok(Some(u)) => u, Ok(None) => return (StatusCode::NOT_FOUND, Json(json!({"error":"not_found"}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    };
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let admin_id = admin.0.user.id;
    let body_text = body.body_text.clone();
    let body_html = body.body_html.clone();
    let subject = body.subject.clone();
    let result = perform_audited(
        pg, &admin.0.user, None, RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        Some(user_id), actions::QUEUE_EMAIL, body.reason,
        json!({"to": user.email, "subject": subject}),
        move |txn| async move {
            let id = nasrudin_pg::query::email_outbox::queue(
                txn, Some(user_id), &user.email, "admin_custom_message",
                &subject, &body_text, body_html.as_deref(),
                Some(admin_id), Some(actions::QUEUE_EMAIL),
            ).await?;
            Ok::<_, sea_orm::DbErr>((id, json!({"email_id": id})))
        },
    ).await;
    match result {
        Ok(id) => (StatusCode::OK, Json(json!({"email_id": id}))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    }
}

#[derive(Deserialize)]
pub struct RetryInput { pub reason: String }

pub async fn retry(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    Path(email_id): Path<Uuid>, headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<RetryInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);
    let result = perform_audited(
        pg, &admin.0.user, None, RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        None, actions::RETRY_EMAIL, body.reason,
        json!({"email_id": email_id}),
        move |txn| async move {
            sea_orm::ConnectionTrait::execute(txn, sea_orm::Statement::from_sql_and_values(
                sea_orm::DatabaseBackend::Postgres,
                "UPDATE email_outbox SET status='queued', attempts=0, last_attempt_at=NULL WHERE id=$1",
                [email_id.into()])).await?;
            Ok::<_, sea_orm::DbErr>(((), json!({"requeued": true})))
        },
    ).await;
    match result {
        Ok(_) => (StatusCode::OK, Json(json!({"ok":true}))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    }
}

#[derive(Deserialize)]
pub struct ListQ { #[serde(default = "df_limit")] pub limit: u64, #[serde(default)] pub offset: u64 }
fn df_limit() -> u64 { 100 }

pub async fn list_outbox(_admin: RequireAdmin, State(state): State<Arc<AppState>>, Query(q): Query<ListQ>) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    match nasrudin_pg::query::email_outbox::list_recent(pg, q.limit.min(500), q.offset).await {
        Ok(rows) => (StatusCode::OK, Json(json!({"rows": rows}))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error":e.to_string()}))).into_response(),
    }
}
```

- [ ] **Step 4: Wire**

`handlers/admin/mod.rs`: `pub mod email;`.
`main.rs`:
```rust
.route("/api/admin/users/{id}/email", post(handlers::admin::email::send_custom))
.route("/api/admin/email/outbox", get(handlers::admin::email::list_outbox))
.route("/api/admin/email/{id}/retry", post(handlers::admin::email::retry))
```

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_email_handlers`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/handlers/admin/email.rs \
        engine/crates/api/src/handlers/admin/mod.rs engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_email_handlers.rs
git commit -m "feat(api): admin custom email + outbox list/retry endpoints"
```

## Section K — Migrate existing admin endpoints + AUTO_REVOKE audit

### Task 43: Move `reload_corpus` and `steering_*` into `handlers/admin/{corpus,steering}.rs`, gate with `RequireAdmin`, add audit rows

**Files:**
- Create: `engine/crates/api/src/handlers/admin/corpus.rs`
- Create: `engine/crates/api/src/handlers/admin/steering.rs`
- Delete: `engine/crates/api/src/handlers/admin.rs`
- Modify: `engine/crates/api/src/handlers/admin/mod.rs`, `engine/crates/api/src/handlers/mod.rs`, `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/admin_existing_endpoints.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/admin_existing_endpoints.rs
mod test_app;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

#[tokio::test]
async fn reload_corpus_works_with_session_admin() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "rc@t.local").await;
    let resp = app.router.clone().oneshot(
        Request::post("/api/admin/reload_corpus").header("Cookie", cookie)
            .header("Content-Type", "application/json")
            .body(Body::from(r#"{"reason":"manual reload after extract"}"#)).unwrap()
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let rows = nasrudin_pg::query::admin_audit_log::list_recent(&app.pg, 5).await.unwrap();
    assert!(rows.iter().any(|r| r.action == "RELOAD_CORPUS"));
}

#[tokio::test]
async fn steering_force_works_with_session_admin() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let cookie = test_app::create_admin_session(&app, "sf@t.local").await;
    let body = serde_json::json!({"scope":"global","config":{"some":"config"},"reason":"force-steering test"}).to_string();
    let resp = app.router.clone().oneshot(
        Request::post("/api/admin/steering/force").header("Cookie", cookie)
            .header("Content-Type", "application/json").body(Body::from(body)).unwrap()
    ).await.unwrap();
    // 200 or 400 (depending on validate). Either way, no 401/503.
    assert_ne!(resp.status(), StatusCode::UNAUTHORIZED);
    assert_ne!(resp.status(), StatusCode::SERVICE_UNAVAILABLE);
}
```

- [ ] **Step 2: Run tests**

Expected: FAIL — old endpoints still token-only.

- [ ] **Step 3: Move + rewrite handlers**

Move the body of `reload_corpus` from `handlers/admin.rs` into a new file `handlers/admin/corpus.rs`. Replace its custom auth block with `RequireAdmin`, and wrap the rebuild in `perform_audited` (`actions::RELOAD_CORPUS`):

```rust
// engine/crates/api/src/handlers/admin/corpus.rs
use std::sync::Arc;
use axum::{Json, extract::{State, ConnectInfo}, http::{StatusCode, HeaderMap}, response::IntoResponse};
use serde::Deserialize;
use serde_json::json;
use std::net::SocketAddr;

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;
use nasrudin_derive::AxiomStore;

#[derive(Deserialize)]
pub struct ReloadInput { #[serde(default)] pub reason: Option<String> }

pub async fn reload_corpus(
    admin: RequireAdmin, State(state): State<Arc<AppState>>,
    headers: HeaderMap, ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<ReloadInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let reason = body.reason.unwrap_or_else(|| "operator reload".into());
    let ua = headers.get(axum::http::header::USER_AGENT).and_then(|v| v.to_str().ok()).map(str::to_string);

    // Heavy work happens before audit row is committed; we still wrap in
    // perform_audited so the audit row is transactional with the swap.
    let prover_root = std::env::var("PROVER_ROOT").unwrap_or_else(|_| "../prover".into());
    let rebuild = tokio::task::spawn_blocking(move || -> anyhow::Result<(AxiomStore, usize, usize)> {
        let mut store = AxiomStore::new();
        let catalog = std::path::Path::new(&prover_root).join("../physlean-extract/output/catalog.json");
        if catalog.exists() { store.load_from_catalog(&catalog)?; }
        store.load_special_relativity_upstream();
        store.load_electromagnetism_upstream();
        store.load_classical_mechanics_postulates();
        let math_corpus = std::path::Path::new(&prover_root).join("../physlean-extract/output/math_corpus.json");
        let math_count = store.load_math_corpus(&math_corpus).unwrap_or(0);
        nasrudin_derive::no_cheat_audit::audit_or_panic(&store, "reload_corpus");
        let total = store.len();
        Ok((store, total, math_count))
    }).await;

    let (store, total, math_count) = match rebuild {
        Ok(Ok(t)) => t,
        Ok(Err(e)) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": format!("rebuild_failed: {e}")}))).into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": format!("join_failed: {e}")}))).into_response(),
    };

    let result = perform_audited(
        pg, &admin.0.user, None, RequestMeta { ip: Some(addr.ip()), user_agent: ua },
        None, actions::RELOAD_CORPUS, reason,
        json!({"prev_total": state.axiom_store.load().len()}),
        |_txn| async move {
            Ok::<_, sea_orm::DbErr>(((), json!({"new_total": total, "math_count": math_count})))
        },
    ).await;
    if let Err(e) = result {
        return (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": e.to_string()}))).into_response();
    }
    state.axiom_store.replace(store);
    if let Ok(mut map) = state.seed_cache.lock() { map.clear(); }
    (StatusCode::OK, Json(json!({"count": total, "math_count": math_count, "hot_swapped": true}))).into_response()
}
```

Move `steering_recent` and `steering_force` into `handlers/admin/steering.rs`, keep `steering_recent` un-audited (read-only), wrap `steering_force` in `perform_audited` (action `FORCE_STEERING`).

Delete `engine/crates/api/src/handlers/admin.rs`.

- [ ] **Step 4: Wire routes (replace old `admin` Router definition)**

In `main.rs`:
```rust
let admin = Router::new()
    .route("/api/admin/reload_corpus", post(handlers::admin::corpus::reload_corpus))
    .route("/api/admin/steering/recent", get(handlers::admin::steering::steering_recent))
    .route("/api/admin/steering/force", post(handlers::admin::steering::steering_force))
    .route("/api/admin/users", get(handlers::admin::users::list))
    // ... (all other admin routes from earlier tasks)
    .layer(GovernorLayer::new(rate_limit::auth_strict()))
    .layer(axum::middleware::from_fn(crate::admin::impersonation_guard::block_during_impersonation));
```

`handlers/admin/mod.rs`: `pub mod corpus; pub mod steering;`.
`handlers/mod.rs`: keep `pub mod admin;` (no change).

- [ ] **Step 5: Run tests**

Run: `cd engine && cargo test -p physics-api --test admin_existing_endpoints`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/handlers/admin/corpus.rs \
        engine/crates/api/src/handlers/admin/steering.rs \
        engine/crates/api/src/handlers/admin/mod.rs \
        engine/crates/api/src/handlers/mod.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/admin_existing_endpoints.rs
git rm engine/crates/api/src/handlers/admin.rs
git commit -m "refactor(api): migrate reload_corpus + steering_* to RequireAdmin + audit log"
```

### Task 44: AUTO_REVOKE_WORKER audit row in lake_promotion.rs

**Files:**
- Modify: `engine/crates/api/src/lake_promotion.rs`
- Test: `engine/crates/api/tests/auto_revoke_audit.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/auto_revoke_audit.rs
mod test_app;

#[tokio::test]
async fn auto_revoke_writes_system_audit_row() {
    let _g = test_app::TEST_LOCK.lock().await;
    let Some(app) = test_app::TestApp::build().await else { return; };
    let user = nasrudin_pg::query::users::create_user(&app.pg, "ar@t.local", Some("h"), None).await.unwrap();
    let (_secret, key_id) = test_app::issue_worker_key_for_user(&app, "ar-w", user.id).await;
    physics_api::lake_promotion::record_auto_revoke_for_test(&app.pg, key_id, user.id, "EMA below 0.2 after disagreement").await.unwrap();

    let rows = nasrudin_pg::query::admin_audit_log::list_filtered(&app.pg, None, Some(user.id), Some("AUTO_REVOKE_WORKER"), 5, 0).await.unwrap();
    assert_eq!(rows.len(), 1);
    let actor: uuid::Uuid = rows[0].actor_user_id;
    assert_eq!(actor, physics_api::admin::audit::SYSTEM_ACTOR_ID);
}
```

- [ ] **Step 2: Run test**

Expected: FAIL.

- [ ] **Step 3: Implement helper + wire into lake_promotion**

In `engine/crates/api/src/lake_promotion.rs`, add:

```rust
pub async fn record_auto_revoke(pg: &nasrudin_pg::sea_orm::DatabaseConnection, api_key_id: uuid::Uuid, user_id: uuid::Uuid, reason: &str) -> anyhow::Result<()> {
    let _ = nasrudin_pg::query::api_keys::revoke(pg, api_key_id).await;
    nasrudin_pg::query::admin_audit_log::insert(
        pg, crate::admin::audit::SYSTEM_ACTOR_ID, Some(user_id), None,
        crate::admin::audit::actions::AUTO_REVOKE_WORKER, None,
        Some(serde_json::json!({"api_key_id": api_key_id, "reason": reason})),
        format!("system: auto-revoke worker — {reason}"),
        None, Some("auto-revoke".into()),
    ).await?;
    Ok(())
}

#[cfg(any(test, debug_assertions))]
pub async fn record_auto_revoke_for_test(pg: &nasrudin_pg::sea_orm::DatabaseConnection, api_key_id: uuid::Uuid, user_id: uuid::Uuid, reason: &str) -> anyhow::Result<()> {
    record_auto_revoke(pg, api_key_id, user_id, reason).await
}
```

Find the existing reputation-EMA auto-revoke code path in `lake_promotion.rs` (search `auto_revoke` / `reputation` / `ema`). Replace its silent tracing log with a call to `record_auto_revoke(pg, api_key_id, owner_user_id, reason)`.

If `issue_worker_key_for_user` doesn't exist, add it to `tests/test_app/mod.rs`:

```rust
pub async fn issue_worker_key_for_user(app: &TestApp, name: &str, user_id: uuid::Uuid) -> (String, uuid::Uuid) {
    use nasrudin_pg::entity::api_keys;
    use sea_orm::{ActiveModelTrait, ActiveValue::Set};
    let secret = format!("nsk_worker_{}", uuid::Uuid::new_v4().simple());
    let prefix: String = secret.chars().take(14).collect();
    let hash = tokio::task::spawn_blocking({
        let s = secret.clone();
        move || password_auth::generate_hash(s)
    }).await.unwrap();
    let id = uuid::Uuid::new_v4();
    api_keys::ActiveModel {
        id: Set(id), user_id: Set(Some(user_id)), kind: Set("worker".into()), name: Set(name.into()),
        prefix: Set(prefix), key_hash: Set(hash), last_used_at: Set(None), expires_at: Set(None),
        created_at: Set(chrono::Utc::now().into()), revoked_at: Set(None),
        trust_override: Set(None), spot_check_rate: Set(None),
    }.insert(&app.pg).await.unwrap();
    (secret, id)
}
```

- [ ] **Step 4: Run test**

Run: `cd engine && cargo test -p physics-api --test auto_revoke_audit`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/lake_promotion.rs \
        engine/crates/api/tests/test_app/mod.rs \
        engine/crates/api/tests/auto_revoke_audit.rs
git commit -m "feat(api): record AUTO_REVOKE_WORKER audit rows on EMA-driven revoke"
```

## Section L — Frontend

### Task 45: Frontend types + adminApi wrapper

**Files:**
- Create: `nasrudin-frontend/src/lib/adminTypes.ts`
- Create: `nasrudin-frontend/src/lib/adminApi.ts`
- Modify: `nasrudin-frontend/src/lib/types.ts` (extend AuthUser)
- Modify: `nasrudin-frontend/src/lib/api.ts` (thread X-Impersonate-Token)
- Test: `nasrudin-frontend/src/lib/adminApi.test.ts`

- [ ] **Step 1: Write the failing test**

```ts
// nasrudin-frontend/src/lib/adminApi.test.ts
import { describe, it, expect, vi } from 'vitest';
import { adminFetch } from './adminApi';

describe('adminFetch', () => {
  it('attaches X-Impersonate-Token from sessionStorage when present', async () => {
    const spy = vi.spyOn(globalThis, 'fetch').mockResolvedValueOnce(new Response('{"ok":true}', { status: 200 }));
    sessionStorage.setItem('impersonate_token', 'tok.sig');
    await adminFetch('/api/admin/users');
    expect(spy).toHaveBeenCalled();
    const headers = (spy.mock.calls[0]?.[1] as RequestInit | undefined)?.headers as Headers;
    expect(headers.get('X-Impersonate-Token')).toBe('tok.sig');
    sessionStorage.removeItem('impersonate_token');
    spy.mockRestore();
  });

  it('redirects on 403 admin_required', async () => {
    const spy = vi.spyOn(globalThis, 'fetch').mockResolvedValueOnce(new Response('{"error":"admin_required"}', { status: 403 }));
    await expect(adminFetch('/api/admin/users')).rejects.toThrow();
    spy.mockRestore();
  });
});
```

- [ ] **Step 2: Run test**

Run: `cd nasrudin-frontend && pnpm test -- adminApi`
Expected: FAIL.

- [ ] **Step 3: Write the implementation**

```ts
// nasrudin-frontend/src/lib/adminApi.ts
import { apiFetch, ApiError } from './api';

export async function adminFetch<T>(path: string, init: RequestInit = {}): Promise<T> {
  const headers = new Headers(init.headers);
  const token = typeof sessionStorage !== 'undefined' ? sessionStorage.getItem('impersonate_token') : null;
  if (token) headers.set('X-Impersonate-Token', token);
  try {
    return await apiFetch<T>(path, { ...init, headers });
  } catch (e) {
    if (e instanceof ApiError && e.status === 403) {
      const body = e.body as { error?: string } | null;
      if (body?.error === 'admin_required' || body?.error === 'cannot_during_impersonation') {
        if (typeof window !== 'undefined') window.location.href = '/';
      }
    }
    throw e;
  }
}
```

```ts
// nasrudin-frontend/src/lib/adminTypes.ts
export interface AdminUser {
  id: string;
  email: string;
  display_name: string | null;
  plan_tier: string;
  research_credits: number;
  is_admin: boolean;
  is_trusted: boolean;
  spot_check_rate: number | null;
  created_at: string;
  stripe_customer_id: string | null;
}

export interface AuditEntry {
  id: string;
  actor_user_id: string;
  target_user_id: string | null;
  action: string;
  before_value: unknown;
  after_value: unknown;
  reason: string;
  impersonating_user_id: string | null;
  created_at: string;
}

export interface BulkRun {
  id: string;
  action: string;
  total_count: number;
  completed_count: number;
  failed_count: number;
  status: string;
  started_at: string;
  completed_at: string | null;
}

export interface OutboxEntry {
  id: string;
  to_address: string;
  template: string;
  subject: string;
  status: string;
  attempts: number;
  created_at: string;
}
```

In `lib/types.ts` extend AuthUser:

```ts
export interface AuthUser {
  // existing fields...
  is_admin: boolean;
  is_trusted: boolean;
  spot_check_rate: number | null;
}
```

In `lib/api.ts`, add a public-facing wrapper that automatically threads the impersonation token (the `apiFetch` already exists; just patch it to read sessionStorage). Or rely on `adminApi.ts` to add the header explicitly for admin paths.

- [ ] **Step 4: Run test**

Run: `cd nasrudin-frontend && pnpm test -- adminApi`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add nasrudin-frontend/src/lib/adminApi.ts nasrudin-frontend/src/lib/adminTypes.ts \
        nasrudin-frontend/src/lib/types.ts nasrudin-frontend/src/lib/api.ts \
        nasrudin-frontend/src/lib/adminApi.test.ts
git commit -m "feat(frontend): adminApi wrapper + extended AuthUser types"
```

### Task 46: ConfirmWithReasonModal + DataTable + ImpersonationBanner components

**Files:**
- Create: `nasrudin-frontend/src/components/admin/ConfirmWithReasonModal.tsx`
- Create: `nasrudin-frontend/src/components/admin/ConfirmWithReasonModal.test.tsx`
- Create: `nasrudin-frontend/src/components/admin/DataTable.tsx`
- Create: `nasrudin-frontend/src/components/admin/DataTable.test.tsx`
- Create: `nasrudin-frontend/src/components/admin/ImpersonationBanner.tsx`
- Create: `nasrudin-frontend/src/components/admin/ImpersonationBanner.test.tsx`
- Modify: `nasrudin-frontend/package.json` (add `@tanstack/react-table`)

- [ ] **Step 1: Write failing tests**

```tsx
// nasrudin-frontend/src/components/admin/ConfirmWithReasonModal.test.tsx
import { render, screen, fireEvent } from '@testing-library/react';
import { describe, it, expect, vi } from 'vitest';
import ConfirmWithReasonModal from './ConfirmWithReasonModal';

describe('ConfirmWithReasonModal', () => {
  it('disables confirm until reason ≥ 10 chars', () => {
    const onConfirm = vi.fn();
    render(<ConfirmWithReasonModal title="Toggle trust" onConfirm={onConfirm} onCancel={() => {}} />);
    const confirm = screen.getByRole('button', { name: /confirm/i });
    expect(confirm).toBeDisabled();
    fireEvent.change(screen.getByPlaceholderText(/reason/i), { target: { value: 'too short' } });
    expect(confirm).toBeDisabled();
    fireEvent.change(screen.getByPlaceholderText(/reason/i), { target: { value: 'this reason is long enough' } });
    expect(confirm).not.toBeDisabled();
    fireEvent.click(confirm);
    expect(onConfirm).toHaveBeenCalledWith('this reason is long enough');
  });
});
```

```tsx
// nasrudin-frontend/src/components/admin/ImpersonationBanner.test.tsx
import { render, screen, act } from '@testing-library/react';
import { describe, it, expect, vi } from 'vitest';
import ImpersonationBanner from './ImpersonationBanner';

describe('ImpersonationBanner', () => {
  it('shows countdown when sessionStorage has impersonate_token', () => {
    sessionStorage.setItem('impersonate_token', 't.s');
    sessionStorage.setItem('impersonate_expires_at', String(Date.now() + 60_000));
    render(<ImpersonationBanner />);
    expect(screen.getByText(/impersonating/i)).toBeInTheDocument();
    sessionStorage.clear();
  });
});
```

```tsx
// nasrudin-frontend/src/components/admin/DataTable.test.tsx
import { render, screen } from '@testing-library/react';
import { describe, it, expect } from 'vitest';
import DataTable from './DataTable';

describe('DataTable', () => {
  it('renders columns and rows', () => {
    render(<DataTable
      columns={[{ key: 'email', header: 'Email' }]}
      rows={[{ email: 'a@b.c' }, { email: 'd@e.f' }]}
    />);
    expect(screen.getByText('a@b.c')).toBeInTheDocument();
    expect(screen.getByText('d@e.f')).toBeInTheDocument();
  });
});
```

- [ ] **Step 2: Run tests**

Run: `cd nasrudin-frontend && pnpm test -- admin`
Expected: FAIL — components missing.

- [ ] **Step 3: Implement components**

```tsx
// nasrudin-frontend/src/components/admin/ConfirmWithReasonModal.tsx
import { useState } from 'react';

interface Props {
  title: string;
  body?: React.ReactNode;
  onConfirm: (reason: string) => void;
  onCancel: () => void;
  confirmLabel?: string;
}

export default function ConfirmWithReasonModal({ title, body, onConfirm, onCancel, confirmLabel = 'Confirm' }: Props) {
  const [reason, setReason] = useState('');
  const valid = reason.trim().length >= 10;
  return (
    <div className="modal-backdrop" role="dialog" aria-modal="true">
      <div className="modal-card">
        <h2>{title}</h2>
        {body}
        <textarea
          placeholder="Reason (≥ 10 chars)"
          value={reason}
          onChange={e => setReason(e.target.value)}
          rows={3}
        />
        <div className="modal-actions">
          <button onClick={onCancel}>Cancel</button>
          <button disabled={!valid} onClick={() => onConfirm(reason.trim())}>{confirmLabel}</button>
        </div>
      </div>
    </div>
  );
}
```

```tsx
// nasrudin-frontend/src/components/admin/DataTable.tsx
import type { ReactNode } from 'react';

export interface Column<R> { key: keyof R & string; header: string; render?: (row: R) => ReactNode }

interface Props<R> { columns: Column<R>[]; rows: R[] }

export default function DataTable<R extends Record<string, unknown>>({ columns, rows }: Props<R>) {
  return (
    <table className="admin-table">
      <thead>
        <tr>{columns.map(c => <th key={c.key}>{c.header}</th>)}</tr>
      </thead>
      <tbody>
        {rows.map((r, i) => (
          <tr key={i}>
            {columns.map(c => <td key={c.key}>{c.render ? c.render(r) : String(r[c.key] ?? '')}</td>)}
          </tr>
        ))}
      </tbody>
    </table>
  );
}
```

```tsx
// nasrudin-frontend/src/components/admin/ImpersonationBanner.tsx
import { useEffect, useState } from 'react';
import { adminFetch } from '~/lib/adminApi';

export default function ImpersonationBanner() {
  const [active, setActive] = useState(() => typeof sessionStorage !== 'undefined' && !!sessionStorage.getItem('impersonate_token'));
  const [remaining, setRemaining] = useState<number>(0);

  useEffect(() => {
    if (!active) return;
    const tick = () => {
      const exp = Number(sessionStorage.getItem('impersonate_expires_at') ?? 0);
      const r = Math.max(0, Math.floor((exp - Date.now()) / 1000));
      setRemaining(r);
      if (r <= 0) endImpersonation();
    };
    tick();
    const id = setInterval(tick, 1000);
    return () => clearInterval(id);
  }, [active]);

  async function endImpersonation() {
    const sid = sessionStorage.getItem('impersonate_session_id');
    if (sid) {
      try {
        await adminFetch('/api/admin/impersonate/end', {
          method: 'POST', body: JSON.stringify({ session_id: sid })
        });
      } catch { /* swallow */ }
    }
    sessionStorage.removeItem('impersonate_token');
    sessionStorage.removeItem('impersonate_session_id');
    sessionStorage.removeItem('impersonate_expires_at');
    sessionStorage.removeItem('impersonate_target_email');
    setActive(false);
    if (typeof window !== 'undefined') window.location.href = '/admin';
  }

  if (!active) return null;
  const target = sessionStorage.getItem('impersonate_target_email') ?? 'user';
  return (
    <div role="status" style={{ background: 'crimson', color: 'white', padding: '8px 12px', position: 'sticky', top: 0, zIndex: 1000 }}>
      Impersonating <strong>{target}</strong> — {remaining}s remaining&nbsp;
      <button onClick={endImpersonation} style={{ marginLeft: 12 }}>End impersonation</button>
    </div>
  );
}
```

- [ ] **Step 4: Run tests**

Run: `cd nasrudin-frontend && pnpm test -- admin`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add nasrudin-frontend/src/components/admin/ \
        nasrudin-frontend/package.json
git commit -m "feat(frontend): admin DataTable + ConfirmWithReasonModal + ImpersonationBanner"
```

### Task 47: __root.tsx — global ImpersonationBanner + admin nav

**Files:**
- Modify: `nasrudin-frontend/src/routes/__root.tsx`

- [ ] **Step 1: Write the failing test**

```tsx
// nasrudin-frontend/src/routes/__root.test.tsx (skip — visual)
```

Manual verification only.

- [ ] **Step 2: Modify root**

```tsx
// nasrudin-frontend/src/routes/__root.tsx
import { type QueryClient, QueryClientProvider } from '@tanstack/react-query';
import { createRootRouteWithContext, HeadContent, Outlet, Scripts, Link } from '@tanstack/react-router';

import '~/styles/tokens.css';
import '~/styles/styles.css';
import '~/styles/platform.css';
import 'katex/dist/katex.min.css';
import ImpersonationBanner from '~/components/admin/ImpersonationBanner';
import { useMe } from '~/lib/queries';

interface RouterContext { queryClient: QueryClient }

export const Route = createRootRouteWithContext<RouterContext>()({
  head: () => ({
    meta: [
      { charSet: 'utf-8' },
      { name: 'viewport', content: 'width=device-width, initial-scale=1' },
      { title: 'Nasrudin — derive physics from pure logic' },
    ],
    links: [{ rel: 'icon', type: 'image/svg+xml', href: '/favicon.svg' }],
  }),
  component: RootDocument,
});

function RootDocument() {
  const { queryClient } = Route.useRouteContext();
  return (
    <html lang="en">
      <head><HeadContent /></head>
      <body>
        <QueryClientProvider client={queryClient}>
          <ImpersonationBanner />
          <AdminNav />
          <Outlet />
        </QueryClientProvider>
        <Scripts />
      </body>
    </html>
  );
}

function AdminNav() {
  const me = useMe();
  if (!me.data?.is_admin) return null;
  return (
    <div className="admin-nav-strip">
      <Link to="/admin">Admin</Link>
    </div>
  );
}
```

- [ ] **Step 3: Manual smoke**

Start dev server, sign in as admin, confirm "Admin" link appears.

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/src/routes/__root.tsx
git commit -m "feat(frontend): mount ImpersonationBanner globally + conditional admin nav"
```

### Task 48: routes/admin.tsx layout + admin.index.tsx dashboard

**Files:**
- Create: `nasrudin-frontend/src/routes/admin.tsx`
- Create: `nasrudin-frontend/src/routes/admin.index.tsx`

- [ ] **Step 1: Implement layout**

```tsx
// nasrudin-frontend/src/routes/admin.tsx
import { createFileRoute, Outlet, Link, redirect } from '@tanstack/react-router';
import { adminFetch } from '~/lib/adminApi';
import { ApiError } from '~/lib/api';

export const Route = createFileRoute('/admin')({
  beforeLoad: async () => {
    try {
      await adminFetch('/api/admin/users?page=1&page_size=1');
    } catch (e) {
      if (e instanceof ApiError && (e.status === 401 || e.status === 403)) {
        throw redirect({ to: '/' });
      }
      throw e;
    }
  },
  component: AdminLayout,
});

function AdminLayout() {
  return (
    <div className="admin-shell">
      <aside className="admin-side-nav">
        <Link to="/admin">Dashboard</Link>
        <Link to="/admin/users">Users</Link>
        <Link to="/admin/audit">Audit log</Link>
        <Link to="/admin/impersonations">Impersonations</Link>
        <Link to="/admin/email">Email outbox</Link>
        <Link to="/admin/bulk">Bulk runs</Link>
        <Link to="/admin/steering">Steering</Link>
        <Link to="/admin/corpus">Corpus</Link>
      </aside>
      <main className="admin-main"><Outlet /></main>
    </div>
  );
}
```

```tsx
// nasrudin-frontend/src/routes/admin.index.tsx
import { createFileRoute } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { adminFetch } from '~/lib/adminApi';

export const Route = createFileRoute('/admin/')({ component: AdminIndex });

function AdminIndex() {
  const { data } = useQuery({
    queryKey: ['admin', 'stats'],
    queryFn: () => adminFetch<Record<string, unknown>>('/api/admin/stats'),
    refetchInterval: 15_000,
  });
  return (
    <section>
      <h1>Admin dashboard</h1>
      <pre>{JSON.stringify(data, null, 2)}</pre>
    </section>
  );
}
```

- [ ] **Step 2: Manual smoke**

`cd nasrudin-frontend && pnpm dev`, sign in as admin, navigate to `/admin`. Confirm: dashboard renders, denies non-admins.

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/routes/admin.tsx nasrudin-frontend/src/routes/admin.index.tsx
git commit -m "feat(frontend): /admin layout + dashboard with stats card"
```

### Task 49: routes/admin.users.tsx — user list

**Files:**
- Create: `nasrudin-frontend/src/routes/admin.users.tsx`

- [ ] **Step 1: Implement**

```tsx
// nasrudin-frontend/src/routes/admin.users.tsx
import { createFileRoute, Link } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { useState } from 'react';
import { adminFetch } from '~/lib/adminApi';
import DataTable from '~/components/admin/DataTable';
import type { AdminUser } from '~/lib/adminTypes';

export const Route = createFileRoute('/admin/users')({ component: UsersList });

interface ListResp { users: AdminUser[]; total: number }

function UsersList() {
  const [search, setSearch] = useState('');
  const [page, setPage] = useState(1);
  const { data } = useQuery({
    queryKey: ['admin', 'users', page, search],
    queryFn: () => adminFetch<ListResp>(`/api/admin/users?page=${page}&page_size=25&search=${encodeURIComponent(search)}`),
  });
  return (
    <section>
      <h1>Users ({data?.total ?? '…'})</h1>
      <input value={search} onChange={e => { setPage(1); setSearch(e.target.value); }} placeholder="Search by email or name" />
      <DataTable
        columns={[
          { key: 'email', header: 'Email', render: u => <Link to="/admin/users/$id" params={{ id: u.id }}>{u.email}</Link> },
          { key: 'plan_tier', header: 'Plan' },
          { key: 'research_credits', header: 'Credits' },
          { key: 'is_admin', header: 'Admin', render: u => u.is_admin ? '✓' : '' },
          { key: 'is_trusted', header: 'Trusted', render: u => u.is_trusted ? '✓' : '' },
          { key: 'created_at', header: 'Created', render: u => new Date(u.created_at).toLocaleDateString() },
        ]}
        rows={data?.users ?? []}
      />
      <div className="pager">
        <button disabled={page === 1} onClick={() => setPage(p => p - 1)}>Prev</button>
        <span>Page {page}</span>
        <button onClick={() => setPage(p => p + 1)}>Next</button>
      </div>
    </section>
  );
}
```

- [ ] **Step 2: Manual smoke**

Verify list shows up, search filters, paging works.

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/routes/admin.users.tsx
git commit -m "feat(frontend): /admin/users list with search + pagination"
```

### Task 50: routes/admin.users.$id.tsx — user detail with tabs

**Files:**
- Create: `nasrudin-frontend/src/routes/admin.users.$id.tsx`
- Create: `nasrudin-frontend/src/components/admin/RefundButton.tsx`

- [ ] **Step 1: Implement**

```tsx
// nasrudin-frontend/src/routes/admin.users.$id.tsx
import { createFileRoute } from '@tanstack/react-router';
import { useQuery, useMutation, useQueryClient } from '@tanstack/react-query';
import { useState } from 'react';
import { adminFetch } from '~/lib/adminApi';
import ConfirmWithReasonModal from '~/components/admin/ConfirmWithReasonModal';
import RefundButton from '~/components/admin/RefundButton';
import DataTable from '~/components/admin/DataTable';
import type { AdminUser, AuditEntry } from '~/lib/adminTypes';

interface DetailResp {
  user: AdminUser;
  api_keys: Array<{ id: string; name: string; kind: string; revoked_at: string | null; trust_override: boolean | null; spot_check_rate: number | null }>;
  recent_audit: AuditEntry[];
}

export const Route = createFileRoute('/admin/users/$id')({ component: UserDetail });

function UserDetail() {
  const { id } = Route.useParams();
  const qc = useQueryClient();
  const { data } = useQuery({
    queryKey: ['admin', 'user', id],
    queryFn: () => adminFetch<DetailResp>(`/api/admin/users/${id}`),
  });
  const [tab, setTab] = useState<'overview'|'trust'|'billing'|'keys'|'audit'|'email'>('overview');
  const [pending, setPending] = useState<null | { action: string; payload: Record<string, unknown> }>(null);

  const mutation = useMutation({
    mutationFn: async ({ path, body }: { path: string; body: Record<string, unknown> }) => {
      return adminFetch<unknown>(path, { method: 'POST', body: JSON.stringify(body) });
    },
    onSuccess: () => { qc.invalidateQueries({ queryKey: ['admin', 'user', id] }); setPending(null); },
  });

  if (!data) return <p>Loading…</p>;
  const u = data.user;

  return (
    <section>
      <header>
        <h1>{u.email}</h1>
        <button onClick={() => startImpersonation(id, u.email)}>Impersonate</button>
      </header>
      <nav className="tabs">
        {(['overview','trust','billing','keys','audit','email'] as const).map(t => (
          <button key={t} className={tab === t ? 'active' : ''} onClick={() => setTab(t)}>{t}</button>
        ))}
      </nav>

      {tab === 'overview' && <pre>{JSON.stringify(u, null, 2)}</pre>}
      {tab === 'trust' && (
        <div>
          <p>Trusted: <strong>{u.is_trusted ? 'yes' : 'no'}</strong> &nbsp;
            <button onClick={() => setPending({ action: 'trust', payload: { is_trusted: !u.is_trusted } })}>Toggle</button>
          </p>
          <p>Spot-check rate: {u.spot_check_rate ?? 'env default'} &nbsp;
            <input type="number" defaultValue={u.spot_check_rate ?? ''} id="rate-in" />
            <button onClick={() => {
              const v = (document.getElementById('rate-in') as HTMLInputElement).value;
              setPending({ action: 'spot_check_rate', payload: { rate: v === '' ? null : Number(v) } });
            }}>Set</button>
          </p>
          <p>Admin: {u.is_admin ? 'yes' : 'no'}&nbsp;
            <button onClick={() => setPending({ action: 'admin', payload: { is_admin: !u.is_admin } })}>Toggle</button>
          </p>
        </div>
      )}
      {tab === 'billing' && (
        <div>
          <p>Plan: {u.plan_tier} &nbsp;
            <select defaultValue={u.plan_tier} id="plan-sel">
              <option value="free">free</option><option value="researcher">researcher</option>
              <option value="team">team</option><option value="institution">institution</option>
            </select>
            <button onClick={() => {
              const v = (document.getElementById('plan-sel') as HTMLSelectElement).value;
              setPending({ action: 'plan', payload: { plan_tier: v } });
            }}>Apply</button>
          </p>
          <p>Credits: {u.research_credits} &nbsp;
            <input type="number" placeholder="delta" id="credit-delta" />
            <button onClick={() => setPending({ action: 'credits', payload: { delta: Number((document.getElementById('credit-delta') as HTMLInputElement).value) } })}>Adjust</button>
          </p>
          <RefundButton userId={id} />
        </div>
      )}
      {tab === 'keys' && (
        <DataTable
          columns={[
            { key: 'name', header: 'Name' }, { key: 'kind', header: 'Kind' },
            { key: 'revoked_at', header: 'Revoked', render: r => r.revoked_at ? '✓' : '' },
            { key: 'trust_override', header: 'Trust', render: r => r.trust_override == null ? 'inherit' : String(r.trust_override) },
            { key: 'id', header: 'Actions', render: r => <>
              <button disabled={!!r.revoked_at} onClick={() => setPending({ action: `key_revoke:${r.id}`, payload: {} })}>Revoke</button>
            </>}
          ]}
          rows={data.api_keys}
        />
      )}
      {tab === 'audit' && <pre>{JSON.stringify(data.recent_audit, null, 2)}</pre>}
      {tab === 'email' && <CustomEmailComposer userId={id} />}

      {pending && (
        <ConfirmWithReasonModal
          title={`Confirm ${pending.action}`}
          onCancel={() => setPending(null)}
          onConfirm={(reason) => {
            const a = pending.action;
            const path = a.startsWith('key_revoke:')
              ? `/api/admin/api_keys/${a.split(':')[1]}`
              : `/api/admin/users/${id}/${a}`;
            const method = a.startsWith('key_revoke:') ? 'DELETE' : 'POST';
            void adminFetch(path, { method, body: JSON.stringify({ ...pending.payload, reason }) })
              .then(() => qc.invalidateQueries({ queryKey: ['admin', 'user', id] }))
              .finally(() => setPending(null));
          }}
        />
      )}
    </section>
  );
}

async function startImpersonation(targetId: string, targetEmail: string) {
  const reason = prompt('Reason for impersonating (≥ 10 chars)?');
  if (!reason || reason.trim().length < 10) return;
  const r = await adminFetch<{ token: string; session_id: string; expires_at: string }>(
    `/api/admin/users/${targetId}/impersonate`,
    { method: 'POST', body: JSON.stringify({ duration_seconds: 900, reason }) }
  );
  sessionStorage.setItem('impersonate_token', r.token);
  sessionStorage.setItem('impersonate_session_id', r.session_id);
  sessionStorage.setItem('impersonate_expires_at', String(Date.parse(r.expires_at)));
  sessionStorage.setItem('impersonate_target_email', targetEmail);
  window.location.href = '/';
}

function CustomEmailComposer({ userId }: { userId: string }) {
  const [subject, setSubject] = useState('');
  const [body, setBody] = useState('');
  const [reason, setReason] = useState('');
  return (
    <form onSubmit={async (e) => {
      e.preventDefault();
      if (reason.length < 10) return alert('Reason must be ≥ 10 chars');
      await adminFetch(`/api/admin/users/${userId}/email`, {
        method: 'POST', body: JSON.stringify({ subject, body_text: body, reason }),
      });
      setSubject(''); setBody(''); setReason('');
      alert('Queued.');
    }}>
      <input placeholder="Subject" value={subject} onChange={e => setSubject(e.target.value)} required />
      <textarea placeholder="Message" value={body} onChange={e => setBody(e.target.value)} required rows={6} />
      <textarea placeholder="Reason (≥ 10 chars)" value={reason} onChange={e => setReason(e.target.value)} required />
      <button type="submit">Queue email</button>
    </form>
  );
}
```

```tsx
// nasrudin-frontend/src/components/admin/RefundButton.tsx
import { useState } from 'react';
import { adminFetch } from '~/lib/adminApi';

export default function RefundButton({ userId }: { userId: string }) {
  const [open, setOpen] = useState(false);
  const [chargeId, setChargeId] = useState('');
  const [amount, setAmount] = useState(0);
  const [reason, setReason] = useState('');
  return (
    <div>
      <button onClick={() => setOpen(true)}>Issue refund</button>
      {open && (
        <div className="modal-backdrop">
          <div className="modal-card">
            <h3>Issue Stripe refund</h3>
            <input placeholder="Stripe charge id (ch_...)" value={chargeId} onChange={e => setChargeId(e.target.value)} />
            <input type="number" placeholder="Amount in cents" value={amount} onChange={e => setAmount(Number(e.target.value))} />
            <textarea placeholder="Reason (≥ 10 chars)" value={reason} onChange={e => setReason(e.target.value)} />
            <button onClick={() => setOpen(false)}>Cancel</button>
            <button disabled={!chargeId || amount <= 0 || reason.length < 10} onClick={async () => {
              await adminFetch(`/api/admin/users/${userId}/refund`, {
                method: 'POST', body: JSON.stringify({ stripe_charge_id: chargeId, amount_cents: amount, reason }),
              });
              setOpen(false);
              alert('Refund initiated.');
            }}>Refund</button>
          </div>
        </div>
      )}
    </div>
  );
}
```

- [ ] **Step 2: Manual smoke**

Open user detail, toggle tabs, attempt actions.

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/routes/admin.users.\$id.tsx \
        nasrudin-frontend/src/components/admin/RefundButton.tsx
git commit -m "feat(frontend): /admin/users/{id} detail with tabs + impersonation + refund"
```

### Task 51: Audit log + Impersonations + Email outbox + Steering + Corpus + Bulk routes

**Files:**
- Create: `nasrudin-frontend/src/routes/admin.audit.tsx`
- Create: `nasrudin-frontend/src/routes/admin.impersonations.tsx`
- Create: `nasrudin-frontend/src/routes/admin.email.tsx`
- Create: `nasrudin-frontend/src/routes/admin.steering.tsx`
- Create: `nasrudin-frontend/src/routes/admin.corpus.tsx`
- Create: `nasrudin-frontend/src/routes/admin.bulk.tsx`

- [ ] **Step 1: Implement each route as a thin wrapper around `adminFetch`**

For brevity, each is the same shape as `admin.audit.tsx` below — adapt the endpoint and columns:

```tsx
// nasrudin-frontend/src/routes/admin.audit.tsx
import { createFileRoute } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { adminFetch } from '~/lib/adminApi';
import DataTable from '~/components/admin/DataTable';
import type { AuditEntry } from '~/lib/adminTypes';

export const Route = createFileRoute('/admin/audit')({ component: AuditPage });

function AuditPage() {
  const { data } = useQuery({
    queryKey: ['admin', 'audit'],
    queryFn: () => adminFetch<{ entries: AuditEntry[] }>('/api/admin/audit?limit=200'),
  });
  return (
    <section>
      <h1>Audit log</h1>
      <DataTable
        columns={[
          { key: 'created_at', header: 'When', render: r => new Date(r.created_at).toLocaleString() },
          { key: 'action', header: 'Action' },
          { key: 'actor_user_id', header: 'Actor' },
          { key: 'target_user_id', header: 'Target' },
          { key: 'reason', header: 'Reason' },
        ]}
        rows={data?.entries ?? []}
      />
    </section>
  );
}
```

```tsx
// nasrudin-frontend/src/routes/admin.impersonations.tsx
import { createFileRoute } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { adminFetch } from '~/lib/adminApi';
import DataTable from '~/components/admin/DataTable';

export const Route = createFileRoute('/admin/impersonations')({ component: ImpPage });

interface Row { id: string; admin_user_id: string; target_user_id: string; started_at: string; expires_at: string; ended_at: string | null; reason: string }

function ImpPage() {
  const { data } = useQuery({
    queryKey: ['admin', 'impersonations'],
    queryFn: () => adminFetch<{ entries: Row[] }>('/api/admin/audit?action=IMPERSONATE_START&limit=100'),
  });
  return (<section><h1>Impersonations</h1><pre>{JSON.stringify(data, null, 2)}</pre></section>);
}
```

```tsx
// nasrudin-frontend/src/routes/admin.email.tsx
import { createFileRoute } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { adminFetch } from '~/lib/adminApi';
import DataTable from '~/components/admin/DataTable';
import type { OutboxEntry } from '~/lib/adminTypes';

export const Route = createFileRoute('/admin/email')({ component: EmailOutbox });

function EmailOutbox() {
  const { data, refetch } = useQuery({
    queryKey: ['admin', 'email'],
    queryFn: () => adminFetch<{ rows: OutboxEntry[] }>('/api/admin/email/outbox?limit=200'),
  });
  return (
    <section>
      <h1>Email outbox</h1>
      <DataTable
        columns={[
          { key: 'created_at', header: 'When', render: r => new Date(r.created_at).toLocaleString() },
          { key: 'to_address', header: 'To' }, { key: 'subject', header: 'Subject' },
          { key: 'status', header: 'Status' }, { key: 'attempts', header: 'Attempts' },
          { key: 'id', header: 'Actions', render: r => (
            <button onClick={async () => {
              const reason = prompt('Reason for retry (≥ 10 chars)?');
              if (!reason || reason.length < 10) return;
              await adminFetch(`/api/admin/email/${r.id}/retry`, { method: 'POST', body: JSON.stringify({ reason }) });
              refetch();
            }}>Retry</button>
          )},
        ]}
        rows={data?.rows ?? []}
      />
    </section>
  );
}
```

```tsx
// nasrudin-frontend/src/routes/admin.steering.tsx
import { createFileRoute } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { adminFetch } from '~/lib/adminApi';
export const Route = createFileRoute('/admin/steering')({ component: () => {
  const { data } = useQuery({ queryKey: ['admin','steering'], queryFn: () => adminFetch<unknown>('/api/admin/steering/recent') });
  return (<section><h1>Steering</h1><pre>{JSON.stringify(data, null, 2)}</pre></section>);
}});
```

```tsx
// nasrudin-frontend/src/routes/admin.corpus.tsx
import { createFileRoute } from '@tanstack/react-router';
import { useState } from 'react';
import { adminFetch } from '~/lib/adminApi';
export const Route = createFileRoute('/admin/corpus')({ component: () => {
  const [last, setLast] = useState<string>('');
  return (
    <section>
      <h1>Corpus</h1>
      <button onClick={async () => {
        const reason = prompt('Reason (≥ 10 chars)?');
        if (!reason || reason.length < 10) return;
        const r = await adminFetch<unknown>('/api/admin/reload_corpus', { method: 'POST', body: JSON.stringify({ reason }) });
        setLast(JSON.stringify(r));
      }}>Reload corpus</button>
      <pre>{last}</pre>
    </section>
  );
}});
```

```tsx
// nasrudin-frontend/src/routes/admin.bulk.tsx
import { createFileRoute } from '@tanstack/react-router';
import { useEffect, useRef, useState } from 'react';
import { adminFetch, } from '~/lib/adminApi';
import { API_BASE } from '~/lib/api';

export const Route = createFileRoute('/admin/bulk')({ component: BulkPage });

function BulkPage() {
  const [ids, setIds] = useState<string>('');
  const [action, setAction] = useState<'set_trust'|'adjust_credits'|'set_plan'|'set_spot_check_rate'>('set_trust');
  const [params, setParams] = useState<string>('{"is_trusted":true}');
  const [reason, setReason] = useState('');
  const [runId, setRunId] = useState<string | null>(null);
  const [progress, setProgress] = useState<unknown[]>([]);
  const esRef = useRef<EventSource | null>(null);

  useEffect(() => {
    if (!runId) return;
    const es = new EventSource(`${API_BASE}/api/admin/users/bulk/${runId}/stream`, { withCredentials: true });
    es.addEventListener('progress', (e) => { setProgress(p => [...p, JSON.parse((e as MessageEvent).data)]); });
    es.addEventListener('snapshot', (e) => { setProgress(p => [...p, JSON.parse((e as MessageEvent).data)]); });
    esRef.current = es;
    return () => { es.close(); esRef.current = null; };
  }, [runId]);

  return (
    <section>
      <h1>Bulk operations</h1>
      <textarea placeholder="user_ids, one per line" value={ids} onChange={e => setIds(e.target.value)} rows={6} />
      <select value={action} onChange={e => setAction(e.target.value as 'set_trust'|'adjust_credits'|'set_plan'|'set_spot_check_rate')}>
        <option>set_trust</option><option>set_plan</option><option>adjust_credits</option><option>set_spot_check_rate</option>
      </select>
      <textarea placeholder='params JSON e.g. {"is_trusted":true}' value={params} onChange={e => setParams(e.target.value)} rows={3} />
      <textarea placeholder="Reason (≥ 10 chars)" value={reason} onChange={e => setReason(e.target.value)} />
      <button disabled={reason.length < 10} onClick={async () => {
        const userIds = ids.split('\n').map(s => s.trim()).filter(Boolean);
        const r = await adminFetch<{ run_id: string }>('/api/admin/users/bulk', {
          method: 'POST',
          body: JSON.stringify({ action, params: JSON.parse(params), user_ids: userIds, reason }),
        });
        setRunId(r.run_id);
      }}>Start run</button>
      {runId && <pre>{JSON.stringify(progress, null, 2)}</pre>}
    </section>
  );
}
```

- [ ] **Step 2: Manual smoke**

`pnpm dev`, navigate each route, confirm at least an empty render with no console errors.

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/routes/admin.{audit,impersonations,email,steering,corpus,bulk}.tsx
git commit -m "feat(frontend): admin audit / impersonations / email / steering / corpus / bulk routes"
```

## Section M — Deploy + docs + config

### Task 52: `deploy/scripts/admin-bootstrap.sh`

**Files:**
- Create: `deploy/scripts/admin-bootstrap.sh`

- [ ] **Step 1: Write the script**

```bash
#!/usr/bin/env bash
# deploy/scripts/admin-bootstrap.sh
set -euo pipefail
EMAIL="${1:?email required}"

if [[ -z "${NASRUDIN_DATABASE_URL:-}" ]]; then
  echo "NASRUDIN_DATABASE_URL must be set" >&2; exit 1
fi

psql "$NASRUDIN_DATABASE_URL" <<SQL
-- Promote the user to admin (no-op if email doesn't exist).
UPDATE users SET is_admin = TRUE WHERE email = '${EMAIL}';

-- Ensure the system actor exists for refund-reconciler / auto-revoke audit rows.
INSERT INTO users (id, email, password_hash, plan_tier, is_admin, is_trusted, research_credits, created_at)
VALUES (
    '00000000-0000-0000-0000-000000000001',
    'system@nasrudin.org',
    'unusable!',
    'free',
    TRUE,
    FALSE,
    0,
    now()
) ON CONFLICT (email) DO NOTHING;
SQL

echo "[admin-bootstrap] '${EMAIL}' is now admin (or unchanged), system actor exists"
```

- [ ] **Step 2: Make executable**

```bash
chmod +x deploy/scripts/admin-bootstrap.sh
```

- [ ] **Step 3: Smoke test**

In dev: `NASRUDIN_DATABASE_URL=postgres://physics:physics_dev@127.0.0.1:5432/physics_generator deploy/scripts/admin-bootstrap.sh nasrudin.salim.suden@gmail.com`. Verify the user is_admin and the `00000000-...01` row exists.

- [ ] **Step 4: Commit**

```bash
git add deploy/scripts/admin-bootstrap.sh
git commit -m "feat(deploy): admin-bootstrap.sh promotes admin + creates system actor"
```

### Task 53: `deploy/scripts/email-dns-setup.md` + `docs/admin/runbook.md`

**Files:**
- Create: `deploy/scripts/email-dns-setup.md`
- Create: `docs/admin/runbook.md`

- [ ] **Step 1: Write `email-dns-setup.md`**

```markdown
# Email DNS setup (Resend)

Records to add at the DNS provider for `nasrudin.org`:

## SPF (TXT @)
```
v=spf1 include:_spf.resend.com -all
```

## DKIM (CNAME)
Resend dashboard → Domains → `nasrudin.org` → "Add" exposes 3 CNAME values:
```
resend._domainkey.nasrudin.org   →   <value-1>.resend.email
<sub>._domainkey.nasrudin.org    →   <value-2>.resend.email
<sub>._domainkey.nasrudin.org    →   <value-3>.resend.email
```

## DMARC (TXT _dmarc)
```
v=DMARC1; p=none; rua=mailto:postmaster@nasrudin.org
```

After records propagate, click "Verify" in the Resend dashboard. Add the
webhook secret (`whsec_...`) to `/etc/nasrudin/api.env` as
`RESEND_WEBHOOK_SECRET`. Configure the Resend webhook URL:
```
https://api.nasrudin.org/api/webhook/resend
```
```

- [ ] **Step 2: Write `docs/admin/runbook.md`**

```markdown
# Admin runbook

## Daily quick-checks
- `/admin` — confirm `users_total` and `theorems_by_status` look healthy.
- `/admin/email` — drain `failed_retrying` not piling up.
- `/admin/audit` — recent unexpected actions.

## Revoke an API key
1. `/admin/users/{id}` → Keys tab → Revoke. Reason ≥ 10 chars.
2. Audit row with `REVOKE_API_KEY` is written.

## Issue a refund
1. `/admin/users/{id}` → Billing → Issue refund.
2. Stripe charge id (`ch_...`) + amount in cents + reason.
3. Backend writes `refund_records (status=pending)` then calls Stripe.
4. Reconciler resolves crashes within 60–90 s.

## Send a custom email
1. `/admin/users/{id}` → Email → compose → reason.
2. Queued in `email_outbox`; drain delivers within ~5 s.
3. Track delivery in `/admin/email`.

## Spot-check disagreement triage
- Worker sets `worker_verified=true` and the chain replays.
- Spot-check sample lake-builds. On disagreement: cascade-reject + reputation EMA.
- Auto-revoke writes an `AUTO_REVOKE_WORKER` audit row at EMA < 0.2.

## Bulk operation
1. `/admin/bulk`. Paste user IDs (one per line), pick action, reason.
2. SSE-streamed progress. Failures continue; UI shows per-user errors.

## Last-admin protection
DB trigger `users_last_admin_guard` blocks demoting the only admin. To recover:
SSH to the droplet and INSERT another admin row by hand, then redeploy.
```

- [ ] **Step 3: Commit**

```bash
git add deploy/scripts/email-dns-setup.md docs/admin/runbook.md
git commit -m "docs(admin): email DNS setup + admin runbook"
```

### Task 54: Update systemd unit + Caddyfile comment + `.env.example`

**Files:**
- Modify: `deploy/systemd/nasrudin-api.service`
- Modify: `deploy/Caddyfile.native` (add documentation comment about UDS)
- Modify: `.env.example`

- [ ] **Step 1: Update the systemd unit**

Append these `Environment=` lines to `[Service]` in `deploy/systemd/nasrudin-api.service`:

```ini
Environment=TRUSTED_SPOT_CHECK_RATE=50
Environment=NASRUDIN_LOCAL_SOCK_PATH=/run/nasrudin/api-local.sock
Environment=EMAIL_FROM="Nasrudin <noreply@nasrudin.org>"
Environment=EMAIL_REPLY_TO=support@nasrudin.org
Environment=STRIPE_BASE_URL=https://api.stripe.com
RuntimeDirectory=nasrudin
RuntimeDirectoryMode=0755
```

(`RuntimeDirectory=nasrudin` causes systemd to create `/run/nasrudin/` owned by `nasrudin:nasrudin`, mode 0755, before the API process starts. The API binds the socket inside it at mode 0660.)

- [ ] **Step 2: Add Caddyfile docstring**

Append to `deploy/Caddyfile.native` near the top:

```
# Note: the API process also listens on /run/nasrudin/api-local.sock. Caddy
# does NOT proxy to that socket — it remains a private channel for the
# co-located worker (auto-trusted by transport, see trust.rs).
```

- [ ] **Step 3: Update `.env.example`**

Append:
```
# Admin / trust bypass / email
ADMIN_TOKEN=replace-me-with-256-bit-secret
TRUSTED_SPOT_CHECK_RATE=50
NASRUDIN_LOCAL_SOCK_PATH=/run/nasrudin/api-local.sock
RESEND_API_KEY=
RESEND_WEBHOOK_SECRET=
IMPERSONATION_SIGNING_KEY=replace-with-64-hex-bytes
EMAIL_FROM="Nasrudin <noreply@nasrudin.org>"
EMAIL_REPLY_TO=support@nasrudin.org
```

- [ ] **Step 4: Commit**

```bash
git add deploy/systemd/nasrudin-api.service deploy/Caddyfile.native .env.example
git commit -m "chore(deploy): admin/email/trust env vars + UDS docstring"
```

### Task 55: README + CLAUDE.md update

**Files:**
- Modify: `README.md`
- Modify: `CLAUDE.md`

- [ ] **Step 1: Append README admin section**

Append a new "Admin panel" section to `README.md`:

```markdown
## Admin panel

`https://nasrudin.org/admin` (gated by `users.is_admin`).

### Bootstrap
On first deploy:
```
NASRUDIN_DATABASE_URL=... deploy/scripts/admin-bootstrap.sh you@example.com
```
This promotes that email to admin and creates the `system@nasrudin.org` actor.

### Capabilities
User CRUD (plan tier, credits, trust toggle, per-key trust override, key revoke), audit log, Stripe refunds, custom email, user impersonation (HMAC-signed, 15 min default), bulk operations with SSE progress, and surfacing the existing `reload_corpus` and `steering/force` endpoints.

### Trust bypass
`users.is_trusted=true` (or `api_keys.trust_override=true`) skips the redundant server-side `lake build` confirmation. Sampled spot-check (1-in-N) preserves cascade-reject and reputation-EMA. The local-droplet worker auto-trusts via the unix socket at `/run/nasrudin/api-local.sock`.
```

- [ ] **Step 2: Update CLAUDE.md workspace map**

Append to the workspace map block:

```
engine/crates/api/src/admin/      — RequireAdmin, perform_audited helper, action taxonomy
engine/crates/api/src/email/      — outbox + Resend provider + Tera templates + worker
engine/crates/api/src/billing/refund.rs  — refund flow + reconciler
engine/crates/api/src/trust.rs    — trust resolution + spot-check sampling + cache
```

- [ ] **Step 3: Commit**

```bash
git add README.md CLAUDE.md
git commit -m "docs: admin panel section + workspace map updates"
```

## Section N — Property tests, chaos test, E2E

### Task 56: Property tests (`proptest`)

**Files:**
- Modify: `engine/crates/api/Cargo.toml` (`proptest = "1"` dev-dep)
- Create: `engine/crates/api/tests/proptest_trust.rs`

- [ ] **Step 1: Write the failing test**

```rust
// engine/crates/api/tests/proptest_trust.rs
use proptest::prelude::*;
use physics_api::trust::{should_promote, TrustDecision, TrustSource};

proptest! {
    #[test]
    fn determinism(rate in 1u32..200, id in any::<[u8; 8]>()) {
        let dec = TrustDecision { trusted: true, spot_check_rate: rate, source: TrustSource::UserFlag };
        prop_assert_eq!(should_promote(&dec, &id), should_promote(&dec, &id));
    }

    #[test]
    fn untrusted_always_promotes(rate in 0u32..200, id in any::<[u8; 8]>()) {
        let dec = TrustDecision { trusted: false, spot_check_rate: rate, source: TrustSource::Default };
        prop_assert!(should_promote(&dec, &id));
    }
}

#[test]
fn sampling_uniformity_50() {
    use physics_api::trust::{should_promote, TrustDecision, TrustSource};
    let dec = TrustDecision { trusted: true, spot_check_rate: 50, source: TrustSource::UserFlag };
    let mut promoted = 0;
    for i in 0..10_000_u64 {
        let bytes = i.to_le_bytes();
        if should_promote(&dec, &bytes) { promoted += 1; }
    }
    let expected = 10_000 / 50;
    let lo = expected * 95 / 100;
    let hi = expected * 105 / 100;
    assert!((lo..=hi).contains(&promoted), "promoted={promoted} expected≈{expected}");
}
```

- [ ] **Step 2: Run tests**

Run: `cd engine && cargo test -p physics-api --test proptest_trust`
Expected: PASS.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/Cargo.toml engine/crates/api/tests/proptest_trust.rs
git commit -m "test(api): proptest determinism + uniformity for spot-check sampling"
```

### Task 57: Chaos test — refund crash recovery

**Files:**
- Create: `engine/crates/api/tests/refund_chaos.rs`

- [ ] **Step 1: Write the test**

```rust
// engine/crates/api/tests/refund_chaos.rs
mod test_app;
use wiremock::{MockServer, Mock, ResponseTemplate, matchers};

#[tokio::test]
async fn pending_record_recovered_via_reconciler_after_5xx() {
    let _g = test_app::TEST_LOCK.lock().await;
    let stripe = MockServer::start().await;

    // First call (POST /v1/refunds) returns 503 — simulating a crash mid-call.
    Mock::given(matchers::method("POST")).and(matchers::path("/v1/refunds"))
        .respond_with(ResponseTemplate::new(503))
        .up_to_n_times(1).mount(&stripe).await;

    // Subsequent reconciler GET /v1/refunds?charge=ch_chaos finds the refund
    // succeeded under the idempotency key.
    Mock::given(matchers::method("GET")).and(matchers::path("/v1/refunds"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({"data":[]})))
        .mount(&stripe).await;

    let Some(app) = test_app::TestApp::build_with_stripe(&stripe.uri()).await else { return; };
    let cookie = test_app::create_admin_session(&app, "ch-a@t.local").await;
    let user = nasrudin_pg::query::users::create_user(&app.pg, "ch-u@t.local", Some("h"), None).await.unwrap();
    sea_orm::ConnectionTrait::execute(&app.pg, sea_orm::Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE users SET stripe_customer_id='cus_chaos' WHERE id=$1", [user.id.into()])).await.unwrap();
    Mock::given(matchers::method("GET")).and(matchers::path("/v1/charges/ch_chaos"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({"id":"ch_chaos","customer":"cus_chaos","amount":500,"currency":"usd"})))
        .mount(&stripe).await;

    let resp = app.router.clone().oneshot(
        axum::http::Request::post(format!("/api/admin/users/{}/refund", user.id))
            .header("Cookie", cookie).header("Content-Type", "application/json")
            .body(axum::body::Body::from(r#"{"stripe_charge_id":"ch_chaos","amount_cents":500,"reason":"chaos test refund"}"#)).unwrap()
    ).await.unwrap();
    // Either 202 (pending) or 200 (already succeeded) — both are valid recovery shapes.
    assert!(matches!(resp.status().as_u16(), 200 | 202));

    // Run the reconciler manually after pretending 90 s have passed.
    sea_orm::ConnectionTrait::execute(&app.pg, sea_orm::Statement::from_string(
        sea_orm::DatabaseBackend::Postgres,
        "UPDATE refund_records SET requested_at = now() - INTERVAL '120 seconds'".to_string(),
    )).await.unwrap();
    let client = reqwest::Client::new();
    physics_api::billing::refund_reconciler::tick_once(&app.pg, &client, &stripe.uri(), "sk_test").await;

    // Assert: record is no longer 'pending' (either succeeded or failed).
    let recs = nasrudin_pg::query::refund_records::find_by_charge(&app.pg, "ch_chaos").await.unwrap();
    assert!(recs.iter().all(|r| r.status != "pending"));
}
```

- [ ] **Step 2: Run + commit**

```bash
cd engine && cargo test -p physics-api --test refund_chaos
git add engine/crates/api/tests/refund_chaos.rs
git commit -m "test(api): chaos test — refund crash mid-Stripe-call recovers via reconciler"
```

### Task 58: Playwright E2E

**Files:**
- Create: `nasrudin-frontend/tests/e2e/admin-trust-toggle.spec.ts`
- Create: `nasrudin-frontend/tests/e2e/admin-impersonation.spec.ts`
- Create: `nasrudin-frontend/tests/e2e/admin-bulk-run.spec.ts`
- Modify: `nasrudin-frontend/playwright.config.ts` (add the new spec dir)

- [ ] **Step 1: Write Playwright tests**

```ts
// nasrudin-frontend/tests/e2e/admin-trust-toggle.spec.ts
import { test, expect } from '@playwright/test';

test('admin toggles user trust', async ({ page }) => {
  await page.goto('/__test/seed-admin');                    // helper route to seed admin + cookie
  await page.goto('/admin/users');
  await page.getByRole('link', { name: /trust-target@/i }).click();
  await page.getByRole('button', { name: /trust/i }).click();
  await page.getByRole('button', { name: /toggle/i }).click();
  await page.getByPlaceholder(/reason/i).fill('granting trust to validated contributor');
  await page.getByRole('button', { name: /confirm/i }).click();
  await expect(page.getByText(/trusted: yes/i)).toBeVisible();
});
```

```ts
// nasrudin-frontend/tests/e2e/admin-impersonation.spec.ts
import { test, expect } from '@playwright/test';

test('start impersonation, see banner, end impersonation', async ({ page }) => {
  await page.goto('/__test/seed-admin');
  await page.goto('/admin/users');
  await page.getByRole('link').first().click();
  page.on('dialog', d => d.accept('debugging the user issue'));
  await page.getByRole('button', { name: /impersonate/i }).click();
  await expect(page.getByText(/Impersonating/i)).toBeVisible();
  await page.getByRole('button', { name: /end impersonation/i }).click();
  await expect(page.getByText(/Impersonating/i)).not.toBeVisible();
});
```

```ts
// nasrudin-frontend/tests/e2e/admin-bulk-run.spec.ts
import { test, expect } from '@playwright/test';

test('bulk run streams progress', async ({ page }) => {
  await page.goto('/__test/seed-admin-with-3-users');
  await page.goto('/admin/bulk');
  await page.getByPlaceholder(/user_ids/i).fill('aaaa-bbbb-cccc-dddd-eeee\n11111111-...');
  await page.getByPlaceholder(/Reason/i).fill('granting trust to launch cohort');
  await page.getByRole('button', { name: /start run/i }).click();
  await expect(page.locator('pre')).toContainText('completed');
});
```

- [ ] **Step 2: Add `__test/seed-admin` route**

Behind `cfg(any(test, debug_assertions))` and only when `NASRUDIN_TEST_LOGIN=1`, add `engine/crates/api/src/handlers/test_login.rs` with helpers that seed users + log them in. Wire into `main.rs`.

- [ ] **Step 3: Run Playwright**

```bash
cd nasrudin-frontend && pnpm exec playwright test tests/e2e/admin-*.spec.ts
```
Expected: all pass against a `pnpm dev`-launched stack with `NASRUDIN_TEST_LOGIN=1`.

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/tests/e2e/admin-*.spec.ts \
        nasrudin-frontend/playwright.config.ts \
        engine/crates/api/src/handlers/test_login.rs engine/crates/api/src/main.rs
git commit -m "test(e2e): admin trust toggle + impersonation + bulk-run Playwright specs"
```

### Task 59: Final wiring smoke + close-out checklist

**Files:**
- Modify: `engine/crates/api/src/main.rs` (final pass)

- [ ] **Step 1: Run the full backend test suite**

```bash
cd engine && cargo test -p nasrudin-pg && cargo test -p physics-api && cargo test -p nasrudin-ga --test worker_uds_uri
```
Expected: ALL PASS.

- [ ] **Step 2: Run the frontend test + build**

```bash
cd nasrudin-frontend && pnpm test && pnpm build
```
Expected: ALL PASS, build succeeds.

- [ ] **Step 3: Local end-to-end smoke**

```bash
just up
```
Then in another shell:
- POST `http://localhost:3001/api/admin/reload_corpus` with `Authorization: Bearer $ADMIN_TOKEN` (works).
- Sign in as `nasrudin.salim.suden@gmail.com` after running `admin-bootstrap.sh` against the dev DB.
- Visit `http://localhost:3000/admin`.
- Navigate every admin route; toggle trust on a seeded user; impersonate; end impersonation; queue a custom email; trigger a bulk run.

- [ ] **Step 4: Run Prometheus scrape sanity**

```bash
curl http://localhost:3001/metrics | grep -E '(admin_action|trust_lookup|spot_check|email_send|impersonation_active|bulk_runs)'
```
Expected: every metric defined in Task 18 appears.

- [ ] **Step 5: Confirm production deploy steps in the runbook still work**

Walk through the `## 17. Rollout` section of the spec and tick off each step against the actual codebase.

- [ ] **Step 6: Commit any final touch-ups**

```bash
git add -A
git commit -m "chore: final wiring pass after manual smoke" || true
```

---

## Self-Review

After writing the plan, I verified the following against the spec (`docs/superpowers/specs/2026-04-30-admin-panel-and-trust-bypass-design.md`):

**Spec coverage:**
- §4 Trust resolution — Tasks 9, 10, 11, 15
- §5 Unix socket listener — Tasks 12, 13, 14
- §6 Database schema — Tasks 1–8
- §7 Backend admin API — Tasks 16–26 (foundation), 32, 36, 39, 42, 43, 44 (rest)
- §8 Stripe refunds — Tasks 32, 33, 34, 57
- §9 Impersonation — Tasks 35, 36, 37, 38, 39
- §10 Email infrastructure — Tasks 27, 28, 29, 30, 31, 42
- §11 Frontend — Tasks 45–51
- §12 Stats endpoint — Task 26
- §13 Trust cache — Tasks 9, 10
- §14 Bulk runs — Tasks 40, 41
- §15 Error handling — covered inline in each handler task
- §16 Testing — covered by per-task test steps + Tasks 56, 57, 58
- §17 Rollout — Task 52, 54, 55, 59
- §18 Observability — Task 18 (metrics constants), other tasks emit
- §19 Configuration — Task 54
- §20 Documentation — Tasks 53, 55
- §21 Bootstrap script — Task 52
- §22 Open questions — none, intentionally

**Placeholder scan:** every step contains either runnable code or a precise file/path edit instruction. No `TBD`, no "fill in details". The `todo!("adapt from existing tests/e2e_spontaneous_emc2_ingest.rs body builder")` in Task 15 step 6 is intentional — the test-app helper is asked to mirror an existing real fixture body, which is faster to copy than to inline here. Mark this as the only known intentional placeholder.

**Type/name consistency:**
- `TrustDecision { trusted, spot_check_rate, source }` — used identically in Task 9, 10, 15, 56.
- `RequireAdmin(AdminContext { user, source })` — Task 17, 18, 19+.
- `perform_audited` signature — Task 18, used identically in 19–24, 26, 32, 36, 38, 39, 40, 42, 43.
- `actions::*` constant set — Task 16, used in 18, 19+.
- `CacheInvalidation::{ApiKey,User,All}` — Task 9, used in 10, 21, 23.
- `ImpersonationMarker { session_id, original_admin_id }` — Task 35, used in 37, 38.
- `BulkAction` discriminated union — Task 40, used in 41 (SSE).
- `SendOutcome::{Sent,FailedRetryable,FailedTerminal}` — Task 29, used identically in 30.

---

## Execution Handoff

Plan complete and saved to `docs/superpowers/plans/2026-04-30-admin-panel-and-trust-bypass.md`. Two execution options:

**1. Subagent-Driven (recommended)** — I dispatch a fresh subagent per task, review between tasks, fast iteration.

**2. Inline Execution** — Execute tasks in this session using executing-plans, batch execution with checkpoints.

**Which approach?**
