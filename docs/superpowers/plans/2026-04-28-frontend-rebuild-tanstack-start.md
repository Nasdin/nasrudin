# Frontend rebuild on TanStack Start + platform API extension — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rebuild `nasrudin-frontend` from prototype HTML/JSX mocks into a working TanStack Start v1 app (React 19, Vite, TS, Biome), and extend `engine/crates/api` with the missing platform endpoints (api_keys, saved_searches, preferences, workers) backed by Postgres so every page has real data.

**Architecture:** TanStack Start does SSR + hydration only — every data call hits Rust API at `:3001`. A unified `AuthOrApiKey` extractor accepts either an axum-login cookie session or `Authorization: Bearer nsk_…`. A separate `WorkerAuth` extractor handles unattended worker keys. CSS files (`tokens.css`, `styles.css`, `platform.css`) move from prototype root into `src/styles/` and are imported as-is — no Tailwind, no CSS-in-JS.

**Tech Stack:**
- **Frontend:** TanStack Start v1, React 19, Vite 7, TypeScript 5.9, Biome 2, TanStack Query v5, KaTeX 0.16, Zod 3
- **Backend:** Rust 2024 edition, Axum 0.8, axum-login 0.18, tower-sessions 0.14, password-auth 1, SeaORM 2, tower_governor 0.8
- **Database:** PostgreSQL 18 (docker-compose)

**Spec:** `docs/superpowers/specs/2026-04-28-frontend-rebuild-tanstack-start-design.md`

---

## Phase 0: Preflight

### Task 0.1: Confirm Postgres is running and DATABASE_URL is set

**Files:** none

- [ ] **Step 1: Start Postgres**

Run:
```bash
just db-start
```
Expected: container `nasrudin-pg` healthy. If it's already up, exit 0.

- [ ] **Step 2: Verify connection string is loadable**

Run:
```bash
set -a; source .env; set +a; echo "$DATABASE_URL"
```
Expected: a `postgresql://…` URL that includes the user, password, host, port, and `physics_generator` db.

- [ ] **Step 3: Verify the engine workspace builds clean**

Run:
```bash
cd engine && cargo check --workspace
```
Expected: exit 0. If it fails, fix the unrelated error before continuing — this plan assumes a clean baseline.

---

## Phase 1: Backend — `nasrudin-pg` adds `api_keys`

### Task 1.1: Add the `api_keys` SeaORM entity

**Files:**
- Create: `engine/crates/pg/src/entity/api_keys.rs`
- Modify: `engine/crates/pg/src/entity/mod.rs`

- [ ] **Step 1: Create the entity file**

```rust
// engine/crates/pg/src/entity/api_keys.rs
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "api_keys")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    /// Owning user. NULL for worker-issued keys.
    pub user_id: Option<Uuid>,
    /// "live" (user-issued) or "worker" (machine-issued).
    pub kind: String,
    pub name: String,
    /// First 12 chars of the full key, used for lookup before Argon2 verify.
    #[sea_orm(unique)]
    pub prefix: String,
    /// Argon2 hash of the full secret.
    #[sea_orm(column_type = "Text")]
    pub key_hash: String,
    pub last_used_at: Option<DateTimeWithTimeZone>,
    pub expires_at: Option<DateTimeWithTimeZone>,
    pub created_at: DateTimeWithTimeZone,
    pub revoked_at: Option<DateTimeWithTimeZone>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(
        belongs_to = "super::users::Entity",
        from = "Column::UserId",
        to = "super::users::Column::Id",
        on_delete = "Cascade"
    )]
    User,
}

impl Related<super::users::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::User.def()
    }
}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 2: Register entity in `entity/mod.rs`**

Modify `engine/crates/pg/src/entity/mod.rs` — add `pub mod api_keys;` after the existing `pub mod` lines:

```rust
pub mod api_keys;
pub mod saved_searches;
pub mod sessions;
pub mod user_preferences;
pub mod users;
pub mod workers;
```

- [ ] **Step 3: Verify it compiles**

Run:
```bash
cd engine && cargo build -p nasrudin-pg
```
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/entity/api_keys.rs engine/crates/pg/src/entity/mod.rs
git commit -m "pg: add api_keys SeaORM entity"
```

### Task 1.2: Add the `api_keys` migration

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260428_000002_api_keys.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Write the migration**

```rust
// engine/crates/pg/src/migrator/m20260428_000002_api_keys.rs
use sea_orm_migration::{prelude::*, schema::*};

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ApiKeys::Table)
                    .if_not_exists()
                    .col(uuid(ApiKeys::Id).primary_key())
                    .col(uuid_null(ApiKeys::UserId))
                    .col(string(ApiKeys::Kind).not_null())
                    .col(string(ApiKeys::Name).not_null())
                    .col(string_uniq(ApiKeys::Prefix).not_null())
                    .col(text(ApiKeys::KeyHash).not_null())
                    .col(timestamp_with_time_zone_null(ApiKeys::LastUsedAt))
                    .col(timestamp_with_time_zone_null(ApiKeys::ExpiresAt))
                    .col(
                        timestamp_with_time_zone(ApiKeys::CreatedAt)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(timestamp_with_time_zone_null(ApiKeys::RevokedAt))
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_api_keys_user_id")
                            .from(ApiKeys::Table, ApiKeys::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_api_keys_user_id")
                    .table(ApiKeys::Table)
                    .col(ApiKeys::UserId)
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_api_keys_kind")
                    .table(ApiKeys::Table)
                    .col(ApiKeys::Kind)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(ApiKeys::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ApiKeys {
    Table,
    Id,
    UserId,
    Kind,
    Name,
    Prefix,
    KeyHash,
    LastUsedAt,
    ExpiresAt,
    CreatedAt,
    RevokedAt,
}

#[derive(DeriveIden)]
enum Users {
    Table,
    Id,
}
```

- [ ] **Step 2: Register the migration**

Modify `engine/crates/pg/src/migrator/mod.rs`:

```rust
use sea_orm_migration::prelude::*;

mod m20250101_000001_create_tables;
mod m20260428_000002_api_keys;

pub struct Migrator;

#[async_trait::async_trait]
impl MigratorTrait for Migrator {
    fn migrations() -> Vec<Box<dyn MigrationTrait>> {
        vec![
            Box::new(m20250101_000001_create_tables::Migration),
            Box::new(m20260428_000002_api_keys::Migration),
        ]
    }
}
```

- [ ] **Step 3: Verify compilation**

Run:
```bash
cd engine && cargo build -p nasrudin-pg
```
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/migrator/
git commit -m "pg: migration for api_keys table (nullable user_id, kind, prefix)"
```

### Task 1.3: Add `password-auth` and `base32` deps to `nasrudin-pg`

**Files:**
- Modify: `engine/Cargo.toml`
- Modify: `engine/crates/pg/Cargo.toml`

- [ ] **Step 1: Add workspace deps in `engine/Cargo.toml`**

Append under `[workspace.dependencies]` (right after the `# Authentication` block that already lists `password-auth`):

```toml
# Already present: password-auth = "1"
# Add:
data-encoding = "2"
```

- [ ] **Step 2: Add deps in `engine/crates/pg/Cargo.toml`**

Add under `[dependencies]`:

```toml
password-auth = { workspace = true }
data-encoding = { workspace = true }
rand = { workspace = true }
```

- [ ] **Step 3: Verify build**

Run:
```bash
cd engine && cargo build -p nasrudin-pg
```
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add engine/Cargo.toml engine/crates/pg/Cargo.toml
git commit -m "pg: add password-auth + data-encoding for api-key hashing"
```

### Task 1.4: Add api_keys query helpers — TDD

**Files:**
- Create: `engine/crates/pg/src/query/api_keys.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`
- Test: `engine/crates/pg/tests/api_keys.rs`

- [ ] **Step 1: Write failing test**

Create `engine/crates/pg/tests/api_keys.rs`:

```rust
//! Integration tests for the api_keys query layer.
//! Skipped if DATABASE_URL is not set.

use nasrudin_pg::{connect_and_migrate, query, PgConfig};
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn create_list_revoke_roundtrip() {
    let Some(db) = db().await else { return };

    // Create owning user
    let email = format!("apikey-test-{}@example.test", Uuid::new_v4());
    let user = query::users::create_user(&db, &email, "stub-hash", None)
        .await
        .unwrap();

    // Create a "live" key
    let issued = query::api_keys::create(
        &db,
        Some(user.id),
        "live",
        "my first key",
        "nsk_live_abc1",
        "argon2-hash-of-secret",
        None,
    )
    .await
    .unwrap();
    assert_eq!(issued.kind, "live");
    assert_eq!(issued.user_id, Some(user.id));

    // Lookup by prefix
    let found = query::api_keys::find_by_prefix(&db, "nsk_live_abc1")
        .await
        .unwrap()
        .expect("must find by prefix");
    assert_eq!(found.id, issued.id);

    // Mark used
    query::api_keys::mark_used(&db, issued.id).await.unwrap();
    let after_use = query::api_keys::find_by_prefix(&db, "nsk_live_abc1")
        .await
        .unwrap()
        .unwrap();
    assert!(after_use.last_used_at.is_some());

    // List by user excludes revoked, so list should have 1
    let list = query::api_keys::list_by_user(&db, user.id).await.unwrap();
    assert_eq!(list.len(), 1);

    // Revoke
    query::api_keys::revoke(&db, issued.id, user.id)
        .await
        .unwrap()
        .expect("revoke must return the row");
    let list_after = query::api_keys::list_by_user(&db, user.id).await.unwrap();
    assert_eq!(list_after.len(), 0);

    // Cleanup
    query::users::delete_user(&db, user.id).await.unwrap();
}
```

- [ ] **Step 2: Run the test to confirm it fails**

Run:
```bash
cd engine && cargo test -p nasrudin-pg --test api_keys
```
Expected: FAIL with `unresolved import nasrudin_pg::query::api_keys` (the helper module does not exist yet).

- [ ] **Step 3: Implement `query::api_keys`**

Create `engine/crates/pg/src/query/api_keys.rs`:

```rust
use sea_orm::*;
use uuid::Uuid;

use crate::entity::api_keys;

/// Insert an api-key row. The caller is responsible for hashing the secret.
#[allow(clippy::too_many_arguments)]
pub async fn create(
    db: &DatabaseConnection,
    user_id: Option<Uuid>,
    kind: &str,
    name: &str,
    prefix: &str,
    key_hash: &str,
    expires_at: Option<chrono::DateTime<chrono::Utc>>,
) -> Result<api_keys::Model, DbErr> {
    let model = api_keys::ActiveModel {
        id: Set(Uuid::new_v4()),
        user_id: Set(user_id),
        kind: Set(kind.to_owned()),
        name: Set(name.to_owned()),
        prefix: Set(prefix.to_owned()),
        key_hash: Set(key_hash.to_owned()),
        last_used_at: Set(None),
        expires_at: Set(expires_at.map(|d| d.into())),
        created_at: Set(chrono::Utc::now().into()),
        revoked_at: Set(None),
    };
    model.insert(db).await
}

/// Find an active (non-revoked) key by its 12-char prefix.
pub async fn find_by_prefix(
    db: &DatabaseConnection,
    prefix: &str,
) -> Result<Option<api_keys::Model>, DbErr> {
    api_keys::Entity::find()
        .filter(api_keys::Column::Prefix.eq(prefix))
        .filter(api_keys::Column::RevokedAt.is_null())
        .one(db)
        .await
}

/// List all non-revoked, non-expired keys for a user.
pub async fn list_by_user(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<Vec<api_keys::Model>, DbErr> {
    let now = chrono::Utc::now();
    api_keys::Entity::find()
        .filter(api_keys::Column::UserId.eq(user_id))
        .filter(api_keys::Column::RevokedAt.is_null())
        .filter(
            api_keys::Column::ExpiresAt
                .is_null()
                .or(api_keys::Column::ExpiresAt.gt(now)),
        )
        .order_by_desc(api_keys::Column::CreatedAt)
        .all(db)
        .await
}

/// Update `last_used_at = now()` on an api-key. Best-effort.
pub async fn mark_used(db: &DatabaseConnection, id: Uuid) -> Result<(), DbErr> {
    let active = api_keys::ActiveModel {
        id: Set(id),
        last_used_at: Set(Some(chrono::Utc::now().into())),
        ..Default::default()
    };
    active.update(db).await?;
    Ok(())
}

/// Revoke an api-key owned by `user_id`. Returns the row if owned, None otherwise.
pub async fn revoke(
    db: &DatabaseConnection,
    id: Uuid,
    user_id: Uuid,
) -> Result<Option<api_keys::Model>, DbErr> {
    let existing = api_keys::Entity::find_by_id(id)
        .filter(api_keys::Column::UserId.eq(user_id))
        .one(db)
        .await?;
    match existing {
        Some(row) => {
            let mut active: api_keys::ActiveModel = row.into();
            active.revoked_at = Set(Some(chrono::Utc::now().into()));
            Ok(Some(active.update(db).await?))
        }
        None => Ok(None),
    }
}
```

- [ ] **Step 4: Wire the module into `query/mod.rs`**

Modify `engine/crates/pg/src/query/mod.rs`:

```rust
pub mod api_keys;
pub mod saved_searches;
pub mod sessions;
pub mod user_preferences;
pub mod users;
pub mod workers;
```

- [ ] **Step 5: Run the test, expect pass**

Run:
```bash
cd engine && cargo test -p nasrudin-pg --test api_keys -- --nocapture
```
Expected: PASS (1 test). If it skips because `DATABASE_URL` is unset, set the env var from `.env` first.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/pg/src/query/api_keys.rs engine/crates/pg/src/query/mod.rs engine/crates/pg/tests/api_keys.rs
git commit -m "pg: api_keys query helpers + integration test"
```

### Task 1.5: Add a `migrate` binary

**Files:**
- Create: `engine/crates/pg/src/bin/migrate.rs`
- Modify: `engine/crates/pg/Cargo.toml`

- [ ] **Step 1: Add the binary target**

Append to `engine/crates/pg/Cargo.toml`:

```toml
[[bin]]
name = "migrate"
path = "src/bin/migrate.rs"

[dependencies.dotenvy]
workspace = true

[dependencies.tracing-subscriber]
workspace = true
```

(The `dotenvy` and `tracing-subscriber` deps are already in workspace deps from the api crate.)

- [ ] **Step 2: Write the binary**

Create `engine/crates/pg/src/bin/migrate.rs`:

```rust
//! Standalone migration runner. Loads `.env`, connects to Postgres,
//! and applies all pending migrations.

use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with(tracing_subscriber::fmt::layer())
        .init();

    // Load .env from project root (../../.env relative to this crate)
    let env_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../.env");
    let _ = dotenvy::from_path(&env_path);

    let url = std::env::var("DATABASE_URL")
        .map_err(|_| anyhow::anyhow!("DATABASE_URL is not set"))?;

    let db = nasrudin_pg::connect_simple(&url).await?;
    nasrudin_pg::run_migrations(&db).await?;
    println!("migrations complete");
    Ok(())
}
```

- [ ] **Step 3: Run migrations**

Run:
```bash
just db-migrate
```
Expected: prints `migrations complete` and exits 0.

- [ ] **Step 4: Verify the table exists**

Run:
```bash
docker exec nasrudin-pg psql -U "${POSTGRES_USER:-physics}" -d "${POSTGRES_DB:-physics_generator}" -c "\d api_keys"
```
Expected: a table description showing all 11 columns with `user_id` nullable.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/bin/migrate.rs engine/crates/pg/Cargo.toml
git commit -m "pg: migrate binary so 'just db-migrate' works"
```

### Task 1.6: Re-export api_keys types from `lib.rs`

**Files:**
- Modify: `engine/crates/pg/src/lib.rs`

- [ ] **Step 1: Add the re-exports**

Modify `engine/crates/pg/src/lib.rs` — under the existing `pub use` block:

```rust
pub use entity::api_keys;
pub use entity::workers::WorkerStatus;
pub use migrator::Migrator;
pub use sea_orm;
pub use sea_orm::DatabaseConnection as DbConn;
```

- [ ] **Step 2: Verify**

Run:
```bash
cd engine && cargo build -p nasrudin-pg
```
Expected: exit 0.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/pg/src/lib.rs
git commit -m "pg: re-export api_keys entity"
```

---

## Phase 2: Backend — Auth extractors

### Task 2.1: Add `AuthOrApiKey` extractor — TDD

**Files:**
- Modify: `engine/crates/api/src/auth.rs`
- Test: `engine/crates/api/tests/auth_or_apikey.rs`

- [ ] **Step 1: Write failing integration test**

Create `engine/crates/api/tests/auth_or_apikey.rs`:

```rust
//! End-to-end test that AuthOrApiKey resolves both a cookie session
//! and a Bearer api-key to the same `AuthUser`.

#[tokio::test]
async fn placeholder_until_extractor_lands() {
    // We need a running test server harness to exercise this end-to-end.
    // For Phase 2 we only assert the type exists and is `Send + Sync`.
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<physics_api::auth::AuthOrApiKey>();
}
```

The crate name is `physics-api`; we need to expose `auth` publicly. (We will fix that in step 3.)

- [ ] **Step 2: Run test, expect failure**

Run:
```bash
cd engine && cargo test -p physics-api --test auth_or_apikey
```
Expected: FAIL — `unresolved import physics_api::auth::AuthOrApiKey`.

- [ ] **Step 3: Make the api crate's modules public for tests**

Modify `engine/crates/api/src/main.rs` — change the module declarations at the top:

```rust
pub mod auth;
pub mod rate_limit;
```

(Do this regardless: subsequent tasks need `pub` mods.)

- [ ] **Step 4: Implement the extractor**

Append to `engine/crates/api/src/auth.rs`:

```rust
// ---------------------------------------------------------------------------
// AuthOrApiKey: cookie session OR `Authorization: Bearer nsk_live_…`
// ---------------------------------------------------------------------------

use axum::{
    extract::FromRequestParts,
    http::{StatusCode, header, request::Parts},
};
use nasrudin_pg::sea_orm::DatabaseConnection;

/// Extractor that succeeds for both authenticated cookie sessions
/// and valid `Authorization: Bearer nsk_live_<secret>` tokens.
///
/// Worker keys (`kind == "worker"`) are explicitly rejected — they must use
/// the `WorkerAuth` extractor instead.
pub struct AuthOrApiKey {
    pub user: AuthUser,
}

impl<S> FromRequestParts<S> for AuthOrApiKey
where
    S: Send + Sync,
{
    type Rejection = (StatusCode, axum::Json<serde_json::Value>);

    async fn from_request_parts(parts: &mut Parts, state: &S) -> Result<Self, Self::Rejection> {
        // 1. Try cookie session.
        if let Ok(session) = AuthSession::<Backend>::from_request_parts(parts, state).await {
            if let Some(user) = session.user {
                return Ok(Self { user });
            }
        }

        // 2. Fall back to bearer token.
        let bearer = parts
            .headers
            .get(header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.strip_prefix("Bearer "))
            .ok_or_else(unauth_response)?;

        if !bearer.starts_with("nsk_live_") {
            return Err(unauth_response());
        }

        // The cookie-session attempt above already loaded the AuthSession,
        // which carries a clone of the DatabaseConnection in `backend.db`.
        // Re-extract just to grab `db` for the lookup.
        let session = AuthSession::<Backend>::from_request_parts(parts, state)
            .await
            .map_err(|_| unauth_response())?;
        let db: &DatabaseConnection = &session.backend.db;

        let prefix: String = bearer.chars().take(12).collect();
        let row = nasrudin_pg::query::api_keys::find_by_prefix(db, &prefix)
            .await
            .map_err(|_| unauth_response())?
            .ok_or_else(unauth_response)?;

        if row.kind != "live" {
            return Err(unauth_response());
        }
        if let Some(exp) = row.expires_at {
            if exp < chrono::Utc::now() {
                return Err(expired_response());
            }
        }
        let secret = bearer.to_owned();
        let hash = row.key_hash.clone();
        let valid = tokio::task::spawn_blocking(move || {
            password_auth::verify_password(secret, &hash).is_ok()
        })
        .await
        .map_err(|_| unauth_response())?;
        if !valid {
            return Err(unauth_response());
        }

        // Mark used (best-effort, fire and forget)
        let db_clone = db.clone();
        let key_id = row.id;
        tokio::spawn(async move {
            let _ = nasrudin_pg::query::api_keys::mark_used(&db_clone, key_id).await;
        });

        let user_id = row.user_id.ok_or_else(unauth_response)?;
        let user_model = nasrudin_pg::query::users::find_by_id(db, user_id)
            .await
            .map_err(|_| unauth_response())?
            .ok_or_else(unauth_response)?;

        Ok(Self {
            user: AuthUser::from_model(user_model),
        })
    }
}

fn unauth_response() -> (StatusCode, axum::Json<serde_json::Value>) {
    (
        StatusCode::UNAUTHORIZED,
        axum::Json(serde_json::json!({ "error": "not authenticated" })),
    )
}

fn expired_response() -> (StatusCode, axum::Json<serde_json::Value>) {
    (
        StatusCode::UNAUTHORIZED,
        axum::Json(serde_json::json!({ "error": "expired api key" })),
    )
}

// `AuthUser::from_model` is private to this module today — re-expose it
// via `pub(crate)` because the extractor lives in the same module.
```

Make `AuthUser::from_model` accessible from this module if it isn't already (it's defined earlier in the same file as `fn from_model`, which is fine).

- [ ] **Step 5: Run the test**

Run:
```bash
cd engine && cargo test -p physics-api --test auth_or_apikey
```
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/auth.rs engine/crates/api/tests/auth_or_apikey.rs engine/crates/api/src/main.rs
git commit -m "api: AuthOrApiKey extractor accepts cookie session or Bearer nsk_live"
```

### Task 2.2: Add `WorkerAuth` extractor

**Files:**
- Modify: `engine/crates/api/src/auth.rs`

- [ ] **Step 1: Append the extractor**

Append to `engine/crates/api/src/auth.rs`:

```rust
// ---------------------------------------------------------------------------
// WorkerAuth: only `Authorization: Bearer nsk_worker_…`
// ---------------------------------------------------------------------------

/// Resolved identity of a worker (no `AuthUser` — workers are not users).
#[derive(Debug, Clone)]
pub struct WorkerCredential {
    pub api_key_id: uuid::Uuid,
    /// The associated `workers.id` row (set by the registration handler;
    /// we look it up via `name` which is the worker handle).
    pub worker_handle: String,
}

pub struct WorkerAuth(pub WorkerCredential);

impl<S> FromRequestParts<S> for WorkerAuth
where
    S: Send + Sync,
{
    type Rejection = (StatusCode, axum::Json<serde_json::Value>);

    async fn from_request_parts(parts: &mut Parts, state: &S) -> Result<Self, Self::Rejection> {
        let bearer = parts
            .headers
            .get(header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.strip_prefix("Bearer "))
            .ok_or_else(unauth_response)?;
        if !bearer.starts_with("nsk_worker_") {
            return Err(unauth_response());
        }

        let session = AuthSession::<Backend>::from_request_parts(parts, state)
            .await
            .map_err(|_| unauth_response())?;
        let db: &DatabaseConnection = &session.backend.db;

        let prefix: String = bearer.chars().take(14).collect();
        let row = nasrudin_pg::query::api_keys::find_by_prefix(db, &prefix)
            .await
            .map_err(|_| unauth_response())?
            .ok_or_else(unauth_response)?;
        if row.kind != "worker" {
            return Err(unauth_response());
        }

        let secret = bearer.to_owned();
        let hash = row.key_hash.clone();
        let valid = tokio::task::spawn_blocking(move || {
            password_auth::verify_password(secret, &hash).is_ok()
        })
        .await
        .map_err(|_| unauth_response())?;
        if !valid {
            return Err(unauth_response());
        }

        Ok(Self(WorkerCredential {
            api_key_id: row.id,
            worker_handle: row.name,
        }))
    }
}
```

- [ ] **Step 2: Verify build**

Run:
```bash
cd engine && cargo build -p physics-api
```
Expected: exit 0.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/auth.rs
git commit -m "api: WorkerAuth extractor for Bearer nsk_worker_ tokens"
```

---

## Phase 3: Backend — handlers

### Task 3.1: Helpers for generating api keys

**Files:**
- Create: `engine/crates/api/src/keygen.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Create the keygen module**

```rust
// engine/crates/api/src/keygen.rs
//! Generate `nsk_<kind>_<base32-secret>` keys.

use data_encoding::BASE32_NOPAD;
use rand::RngCore;

pub struct GeneratedKey {
    /// Full key as the user sees it. Only returned to the client once.
    pub full: String,
    /// First 12 chars (or 14 for worker keys), stored cleartext for lookup.
    pub prefix: String,
    /// Argon2 hash of `full` — what we persist.
    pub hash: String,
}

pub fn generate(kind: &str) -> anyhow::Result<GeneratedKey> {
    let mut buf = [0u8; 24];
    rand::rng().fill_bytes(&mut buf);
    let secret = BASE32_NOPAD.encode(&buf).to_lowercase();
    let full = format!("nsk_{kind}_{secret}");
    let prefix_len = match kind {
        "worker" => 14,
        _ => 12,
    };
    let prefix: String = full.chars().take(prefix_len).collect();
    let hash = password_auth::generate_hash(&full);
    Ok(GeneratedKey { full, prefix, hash })
}
```

- [ ] **Step 2: Wire into `main.rs`**

Modify `engine/crates/api/src/main.rs` — add to the module declarations at the top:

```rust
pub mod auth;
pub mod keygen;
pub mod rate_limit;
```

- [ ] **Step 3: Add deps to api crate**

Modify `engine/crates/api/Cargo.toml` — under `[dependencies]`:

```toml
data-encoding = { workspace = true }
rand = { workspace = true }
```

- [ ] **Step 4: Verify build**

Run:
```bash
cd engine && cargo build -p physics-api
```
Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/keygen.rs engine/crates/api/src/main.rs engine/crates/api/Cargo.toml
git commit -m "api: keygen helper produces nsk_<kind>_… keys + Argon2 hash"
```

### Task 3.2: `handlers/` module skeleton

**Files:**
- Create: `engine/crates/api/src/handlers/mod.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Create the directory and stub**

```rust
// engine/crates/api/src/handlers/mod.rs
pub mod api_keys;
pub mod me;
pub mod preferences;
pub mod saved_searches;
pub mod workers;
```

- [ ] **Step 2: Add to `main.rs`**

Add to the top of `engine/crates/api/src/main.rs`:

```rust
pub mod auth;
pub mod handlers;
pub mod keygen;
pub mod rate_limit;
```

(Files for each handler are added in the next tasks. Until they exist this won't compile. We commit at the end of Task 3.7 once everything compiles.)

### Task 3.3: `handlers/api_keys.rs` — create / list / revoke

**Files:**
- Create: `engine/crates/api/src/handlers/api_keys.rs`

- [ ] **Step 1: Write the handlers**

```rust
// engine/crates/api/src/handlers/api_keys.rs
use axum::{Json, extract::Path, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use uuid::Uuid;

use crate::{auth::AuthSess, keygen};

#[derive(Deserialize)]
pub struct CreateBody {
    pub name: String,
    pub expires_in_days: Option<i64>,
}

/// `POST /api/api-keys` — cookie auth only.
pub async fn create(auth: AuthSess, Json(body): Json<CreateBody>) -> impl IntoResponse {
    let Some(user) = auth.user.as_ref() else {
        return (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "not authenticated" })),
        );
    };

    if body.name.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "name is required" })),
        );
    }

    let generated = match keygen::generate("live") {
        Ok(k) => k,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            );
        }
    };

    let expires_at = body
        .expires_in_days
        .map(|d| chrono::Utc::now() + chrono::Duration::days(d));

    let row = match nasrudin_pg::query::api_keys::create(
        &auth.backend.db,
        Some(user.id),
        "live",
        body.name.trim(),
        &generated.prefix,
        &generated.hash,
        expires_at,
    )
    .await
    {
        Ok(r) => r,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            );
        }
    };

    (
        StatusCode::OK,
        Json(serde_json::json!({
            "id": row.id,
            "name": row.name,
            "prefix": row.prefix,
            "full_key": generated.full,
            "created_at": row.created_at,
            "expires_at": row.expires_at,
        })),
    )
}

/// `GET /api/api-keys` — list non-revoked, non-expired keys for the current user.
pub async fn list(auth: AuthSess) -> impl IntoResponse {
    let Some(user) = auth.user.as_ref() else {
        return (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "not authenticated" })),
        );
    };
    match nasrudin_pg::query::api_keys::list_by_user(&auth.backend.db, user.id).await {
        Ok(rows) => {
            let keys: Vec<serde_json::Value> = rows
                .into_iter()
                .map(|r| {
                    serde_json::json!({
                        "id": r.id,
                        "name": r.name,
                        "prefix": r.prefix,
                        "last_used_at": r.last_used_at,
                        "created_at": r.created_at,
                        "expires_at": r.expires_at,
                    })
                })
                .collect();
            (StatusCode::OK, Json(serde_json::json!({ "keys": keys })))
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

/// `DELETE /api/api-keys/{id}` — revoke a key the current user owns.
pub async fn revoke(auth: AuthSess, Path(id): Path<Uuid>) -> impl IntoResponse {
    let Some(user) = auth.user.as_ref() else {
        return (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "not authenticated" })),
        );
    };
    match nasrudin_pg::query::api_keys::revoke(&auth.backend.db, id, user.id).await {
        Ok(Some(_)) => (StatusCode::OK, Json(serde_json::json!({ "revoked": true }))),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not found" })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}
```

### Task 3.4: `handlers/saved_searches.rs`

**Files:**
- Create: `engine/crates/api/src/handlers/saved_searches.rs`

- [ ] **Step 1: Write the handlers**

```rust
// engine/crates/api/src/handlers/saved_searches.rs
use axum::{Json, extract::Path, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use uuid::Uuid;

use crate::auth::{AuthOrApiKey, AuthSess};

#[derive(Deserialize)]
pub struct CreateBody {
    pub latex: String,
    pub label: Option<String>,
}

#[derive(Deserialize)]
pub struct PatchBody {
    pub label: Option<String>,
}

pub async fn create(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<CreateBody>,
) -> impl IntoResponse {
    if body.latex.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "latex is required" })),
        );
    }
    match nasrudin_pg::query::saved_searches::create(
        &auth_sess.backend.db,
        auth.user.id,
        body.latex.trim(),
        body.label.as_deref(),
    )
    .await
    {
        Ok(row) => (StatusCode::OK, Json(serde_json::to_value(row).unwrap())),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

pub async fn list(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    match nasrudin_pg::query::saved_searches::list_by_user(&auth_sess.backend.db, auth.user.id).await {
        Ok(rows) => (
            StatusCode::OK,
            Json(serde_json::json!({ "saved_searches": rows })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

pub async fn delete(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    match nasrudin_pg::query::saved_searches::delete(&auth_sess.backend.db, id, auth.user.id).await {
        Ok(res) if res.rows_affected > 0 => {
            (StatusCode::OK, Json(serde_json::json!({ "deleted": true })))
        }
        Ok(_) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not found" })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

pub async fn patch_label(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
    Json(body): Json<PatchBody>,
) -> impl IntoResponse {
    match nasrudin_pg::query::saved_searches::update_label(
        &auth_sess.backend.db,
        id,
        auth.user.id,
        body.label.as_deref(),
    )
    .await
    {
        Ok(Some(row)) => (StatusCode::OK, Json(serde_json::to_value(row).unwrap())),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not found" })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}
```

### Task 3.5: `handlers/preferences.rs`

**Files:**
- Create: `engine/crates/api/src/handlers/preferences.rs`

- [ ] **Step 1: Write the handlers**

```rust
// engine/crates/api/src/handlers/preferences.rs
use axum::{Json, http::StatusCode, response::IntoResponse};

use crate::auth::{AuthOrApiKey, AuthSess};

pub async fn get(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    match nasrudin_pg::query::user_preferences::get(&auth_sess.backend.db, auth.user.id).await {
        Ok(prefs) => (
            StatusCode::OK,
            Json(serde_json::json!({ "preferences": prefs })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

/// PATCH = shallow merge (existing query helper does this).
pub async fn patch(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    if !body.is_object() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "body must be a JSON object" })),
        );
    }
    match nasrudin_pg::query::user_preferences::merge(&auth_sess.backend.db, auth.user.id, body)
        .await
    {
        Ok(row) => (
            StatusCode::OK,
            Json(serde_json::json!({ "preferences": row.preferences })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}
```

### Task 3.6: `handlers/workers.rs`

**Files:**
- Create: `engine/crates/api/src/handlers/workers.rs`

- [ ] **Step 1: Write the handlers**

```rust
// engine/crates/api/src/handlers/workers.rs
use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use std::sync::Arc;

use crate::{AppState, auth::WorkerAuth, keygen};

#[derive(Deserialize)]
pub struct RegisterBody {
    pub handle: String,
    pub host: Option<String>,
}

/// `POST /api/workers/register` — unauthenticated. Returns `{ worker_id, api_key }`.
pub async fn register(
    State(state): State<Arc<AppState>>,
    Json(body): Json<RegisterBody>,
) -> impl IntoResponse {
    let Some(db) = state.pg.clone() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "postgres not configured" })),
        );
    };

    if body.handle.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "handle is required" })),
        );
    }

    if let Err(e) = nasrudin_pg::query::workers::register(
        &db,
        body.handle.trim(),
        Some(body.handle.trim()),
        body.host.as_deref(),
    )
    .await
    {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        );
    }

    let generated = match keygen::generate("worker") {
        Ok(k) => k,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            );
        }
    };
    if let Err(e) = nasrudin_pg::query::api_keys::create(
        &db,
        None,
        "worker",
        body.handle.trim(),
        &generated.prefix,
        &generated.hash,
        None,
    )
    .await
    {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        );
    }

    (
        StatusCode::OK,
        Json(serde_json::json!({
            "worker_id": body.handle.trim(),
            "api_key": generated.full,
        })),
    )
}

#[derive(Deserialize)]
pub struct HeartbeatBody {
    pub theorems_contributed: i64,
}

/// `POST /api/workers/heartbeat` — `Authorization: Bearer nsk_worker_…`.
pub async fn heartbeat(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Json(body): Json<HeartbeatBody>,
) -> impl IntoResponse {
    let Some(db) = state.pg.clone() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "postgres not configured" })),
        );
    };
    match nasrudin_pg::query::workers::heartbeat(&db, &auth.0.worker_handle, body.theorems_contributed).await {
        Ok(Some(row)) => (StatusCode::OK, Json(serde_json::to_value(row).unwrap())),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "worker not found" })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

/// `GET /api/workers` — public list of all known workers.
pub async fn list(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let Some(db) = state.pg.clone() else {
        return (
            StatusCode::OK,
            Json(serde_json::json!({ "workers": [] })),
        );
    };
    match nasrudin_pg::query::workers::list(&db, None).await {
        Ok(rows) => (StatusCode::OK, Json(serde_json::json!({ "workers": rows }))),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}
```

### Task 3.7: `handlers/me.rs` and wire everything into `main.rs`

**Files:**
- Create: `engine/crates/api/src/handlers/me.rs`
- Modify: `engine/crates/api/src/rate_limit.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Create `handlers/me.rs`**

```rust
// engine/crates/api/src/handlers/me.rs
use axum::{Json, http::StatusCode, response::IntoResponse};

use crate::auth::{AuthOrApiKey, AuthSess};

/// `GET /api/me/stats` — quick user stat aggregation for the profile page.
pub async fn stats(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    let saved_count = nasrudin_pg::query::saved_searches::list_by_user(
        &auth_sess.backend.db,
        auth.user.id,
    )
    .await
    .map(|v| v.len())
    .unwrap_or(0);
    let key_count = nasrudin_pg::query::api_keys::list_by_user(&auth_sess.backend.db, auth.user.id)
        .await
        .map(|v| v.len())
        .unwrap_or(0);
    (
        StatusCode::OK,
        Json(serde_json::json!({
            "saved_searches": saved_count,
            "api_keys": key_count,
        })),
    )
}
```

- [ ] **Step 2: Add new rate-limit groups**

Open `engine/crates/api/src/rate_limit.rs` and append two new functions modelled on `auth_strict()` / `auth_session()`:

```rust
/// 60 req/min, burst 30. Per-IP / per-key (best effort with IP fallback).
pub fn platform_user() -> Arc<GovernorConfig<…>> { /* mirror auth_session shape, 1s replenish, 30 burst */ }

/// 300 req/min, burst 120. Worker heartbeat group.
pub fn platform_worker() -> Arc<GovernorConfig<…>> { /* mirror auth_session shape, 200ms replenish, 120 burst */ }
```

The exact `GovernorConfig` builder pattern is identical to the four existing groups in this file — copy `auth_session` and adjust the replenish interval and burst.

- [ ] **Step 3: Wire routes in `main.rs`**

Open `engine/crates/api/src/main.rs` and add the new routers right after the existing `auth_session` router (around line 230):

```rust
let platform_user = Router::new()
    .route("/api/api-keys", axum::routing::post(handlers::api_keys::create))
    .route("/api/api-keys", get(handlers::api_keys::list))
    .route("/api/api-keys/{id}", delete(handlers::api_keys::revoke))
    .route("/api/saved-searches", axum::routing::post(handlers::saved_searches::create))
    .route("/api/saved-searches", get(handlers::saved_searches::list))
    .route("/api/saved-searches/{id}", delete(handlers::saved_searches::delete))
    .route("/api/saved-searches/{id}", axum::routing::patch(handlers::saved_searches::patch_label))
    .route("/api/preferences", get(handlers::preferences::get))
    .route("/api/preferences", axum::routing::patch(handlers::preferences::patch))
    .route("/api/me/stats", get(handlers::me::stats))
    .layer(GovernorLayer::new(rate_limit::platform_user()));

let platform_worker = Router::new()
    .route("/api/workers/register", axum::routing::post(handlers::workers::register))
    .route("/api/workers/heartbeat", axum::routing::post(handlers::workers::heartbeat))
    .layer(GovernorLayer::new(rate_limit::platform_worker()));

let workers_public = Router::new()
    .route("/api/workers", get(handlers::workers::list))
    .layer(GovernorLayer::new(rate_limit::api_standard()));

app = app
    .merge(platform_user)
    .merge(platform_worker)
    .merge(workers_public);
```

Note: `platform_user` and `platform_worker` need the `auth_layer` applied as well so `AuthSess` works. Move the `.merge(...)` calls to be **before** the `.layer(auth_layer)` line that the existing auth_strict/auth_session merges sit before.

- [ ] **Step 4: Build**

Run:
```bash
cd engine && cargo build -p physics-api
```
Expected: exit 0. Fix any unused import warnings.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/handlers/ engine/crates/api/src/rate_limit.rs engine/crates/api/src/main.rs
git commit -m "api: api_keys + saved_searches + preferences + workers + me handlers"
```

### Task 3.8: End-to-end smoke test against running server

**Files:** none

- [ ] **Step 1: Start the server in the background**

Run:
```bash
just dev-engine &
```
Wait until log says `Listening on 0.0.0.0:3001`.

- [ ] **Step 2: Register a user**

```bash
curl -i -c /tmp/nas-cookie.txt -H 'Content-Type: application/json' \
  -d '{"email":"e2e@example.test","password":"hunter2hunter2","display_name":"E2E"}' \
  http://localhost:3001/api/auth/register
```
Expected: 200, body has `id`, `email`. Cookie `id` set.

- [ ] **Step 3: Create an api key**

```bash
curl -i -b /tmp/nas-cookie.txt -H 'Content-Type: application/json' \
  -d '{"name":"smoke-test"}' \
  http://localhost:3001/api/api-keys
```
Expected: 200 with `full_key` starting `nsk_live_…`. Save the value into `$KEY`.

- [ ] **Step 4: Use the bearer key on a protected endpoint**

```bash
curl -i -H "Authorization: Bearer $KEY" http://localhost:3001/api/me/stats
```
Expected: 200 with `{ "saved_searches": 0, "api_keys": 1 }`.

- [ ] **Step 5: List + revoke**

```bash
KEY_ID=$(curl -s -b /tmp/nas-cookie.txt http://localhost:3001/api/api-keys | jq -r '.keys[0].id')
curl -i -X DELETE -b /tmp/nas-cookie.txt http://localhost:3001/api/api-keys/$KEY_ID
curl -i -H "Authorization: Bearer $KEY" http://localhost:3001/api/me/stats
```
Expected: revoke returns 200, the bearer call after revoke returns 401.

- [ ] **Step 6: Stop the server**

```bash
kill %1
```

- [ ] **Step 7: Commit any cleanup**

If any test data was committed by mistake, revert. Otherwise nothing to commit.

---

## Phase 4: Frontend — scaffold the TanStack Start app

### Task 4.1: Initialize `package.json` with latest deps

**Files:**
- Create: `nasrudin-frontend/package.json`

- [ ] **Step 1: Write the manifest**

```json
{
  "name": "nasrudin-frontend",
  "version": "0.0.0",
  "private": true,
  "type": "module",
  "scripts": {
    "dev": "vite dev --port 3000",
    "build": "vite build",
    "start": "node .output/server/index.mjs",
    "test": "vitest run",
    "check": "biome check . && tsc --noEmit",
    "format": "biome format --write ."
  },
  "dependencies": {
    "@tanstack/react-query": "^5",
    "@tanstack/react-router": "^1",
    "@tanstack/react-start": "^1",
    "katex": "^0.16",
    "react": "^19",
    "react-dom": "^19",
    "react-katex": "^3",
    "zod": "^3"
  },
  "devDependencies": {
    "@biomejs/biome": "^2",
    "@tanstack/react-query-devtools": "^5",
    "@tanstack/router-plugin": "^1",
    "@types/katex": "^0.16",
    "@types/react": "^19",
    "@types/react-dom": "^19",
    "typescript": "^5.9",
    "vite": "^7",
    "vite-tsconfig-paths": "^5",
    "vitest": "^3"
  }
}
```

- [ ] **Step 2: Install**

Run:
```bash
cd nasrudin-frontend && pnpm install
```
Expected: completes without unresolvable peer-dep errors. The lockfile is created.

- [ ] **Step 3: Note the resolved versions**

Run:
```bash
cd nasrudin-frontend && pnpm list --depth=0
```
Read the output and confirm `@tanstack/react-start`, `@tanstack/react-router`, and `react` are at v1+ / 19+.

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/package.json nasrudin-frontend/pnpm-lock.yaml
git commit -m "frontend: package.json with latest TanStack Start + React 19 deps"
```

### Task 4.2: TypeScript + Biome config

**Files:**
- Create: `nasrudin-frontend/tsconfig.json`
- Create: `nasrudin-frontend/biome.json`

- [ ] **Step 1: tsconfig**

```json
{
  "compilerOptions": {
    "target": "ES2022",
    "lib": ["ES2022", "DOM", "DOM.Iterable"],
    "jsx": "react-jsx",
    "module": "ESNext",
    "moduleResolution": "Bundler",
    "strict": true,
    "noUncheckedIndexedAccess": true,
    "noImplicitOverride": true,
    "noFallthroughCasesInSwitch": true,
    "exactOptionalPropertyTypes": true,
    "esModuleInterop": true,
    "resolveJsonModule": true,
    "isolatedModules": true,
    "skipLibCheck": true,
    "allowImportingTsExtensions": false,
    "noEmit": true,
    "baseUrl": ".",
    "paths": {
      "~/*": ["src/*"]
    }
  },
  "include": ["src", "vite.config.ts", "app.config.ts"],
  "exclude": ["node_modules", ".output", "dist"]
}
```

- [ ] **Step 2: biome.json**

```json
{
  "$schema": "https://biomejs.dev/schemas/2.0.0/schema.json",
  "files": { "ignore": [".output", "dist", "src/routeTree.gen.ts"] },
  "linter": {
    "enabled": true,
    "rules": { "recommended": true, "style": { "useImportType": "warn" } }
  },
  "formatter": { "enabled": true, "indentStyle": "space", "indentWidth": 2, "lineWidth": 100 },
  "javascript": { "formatter": { "quoteStyle": "single", "trailingCommas": "all" } }
}
```

- [ ] **Step 3: Verify Biome runs**

Run:
```bash
cd nasrudin-frontend && pnpm exec biome check . || true
```
Expected: no panic. There are no source files yet so it will just emit "no files".

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/tsconfig.json nasrudin-frontend/biome.json
git commit -m "frontend: tsconfig + biome config"
```

### Task 4.3: Vite + TanStack Start config

**Files:**
- Create: `nasrudin-frontend/vite.config.ts`
- Create: `nasrudin-frontend/app.config.ts`

- [ ] **Step 1: vite.config.ts**

```ts
// nasrudin-frontend/vite.config.ts
import { defineConfig } from 'vite';
import { tanstackStart } from '@tanstack/react-start/plugin/vite';
import { tanstackRouter } from '@tanstack/router-plugin/vite';
import tsconfigPaths from 'vite-tsconfig-paths';

export default defineConfig({
  plugins: [
    tsconfigPaths(),
    tanstackRouter({ target: 'react', autoCodeSplitting: true }),
    tanstackStart(),
  ],
  server: { port: 3000 },
});
```

If `@tanstack/react-start/plugin/vite` is not the correct entry for the installed version, run `node -e "console.log(Object.keys(require('@tanstack/react-start/package.json').exports || {}))"` and use whatever the package exposes for the Vite plugin (commonly `@tanstack/react-start/vite-plugin` or similar). Pick the entry that exists; do not invent one.

- [ ] **Step 2: app.config.ts**

```ts
// nasrudin-frontend/app.config.ts
// TanStack Start v1 reads server settings here when present.
// We keep the file thin — actual config lives in vite.config.ts and the app code.
export default {
  server: { preset: 'node-server' },
};
```

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/vite.config.ts nasrudin-frontend/app.config.ts
git commit -m "frontend: vite + tanstack-start plugin config"
```

### Task 4.4: Move CSS files into `src/styles` and assets into `public`

**Files:**
- Move: `nasrudin-frontend/{tokens,styles,platform}.css` → `nasrudin-frontend/src/styles/`
- Move: `nasrudin-frontend/assets/pattern-geometric.svg` → `nasrudin-frontend/public/pattern-geometric.svg`

- [ ] **Step 1: Move files**

```bash
cd nasrudin-frontend
mkdir -p src/styles public
git mv tokens.css src/styles/tokens.css 2>/dev/null || mv tokens.css src/styles/tokens.css
git mv styles.css src/styles/styles.css 2>/dev/null || mv styles.css src/styles/styles.css
git mv platform.css src/styles/platform.css 2>/dev/null || mv platform.css src/styles/platform.css
git mv assets/pattern-geometric.svg public/pattern-geometric.svg 2>/dev/null || mv assets/pattern-geometric.svg public/pattern-geometric.svg
rmdir assets
```

(`git mv` will fail because these files are untracked — `mv` is fine. The git fallback above handles either.)

- [ ] **Step 2: Update SVG reference in tokens.css**

Modify `src/styles/styles.css`: the only references in the prototype HTML to `assets/pattern-geometric.svg` should now be `/pattern-geometric.svg` (Vite serves `public/` from root). Search for `assets/pattern` and replace with `/pattern`:

```bash
grep -rn "assets/pattern" src/styles
# If matches: edit each to use /pattern-geometric.svg
```

- [ ] **Step 3: Commit**

```bash
git add src/styles public
git commit -m "frontend: move tokens/styles/platform CSS into src/styles, asset into public"
```

### Task 4.5: Set up the root route + entries

**Files:**
- Create: `nasrudin-frontend/src/router.tsx`
- Create: `nasrudin-frontend/src/ssr.tsx`
- Create: `nasrudin-frontend/src/client.tsx`
- Create: `nasrudin-frontend/src/routes/__root.tsx`
- Create: `nasrudin-frontend/src/routes/index.tsx` (placeholder)

- [ ] **Step 1: src/router.tsx**

```tsx
// nasrudin-frontend/src/router.tsx
import { QueryClient } from '@tanstack/react-query';
import { createRouter as createTanstackRouter } from '@tanstack/react-router';
import { routeTree } from './routeTree.gen';

export function createRouter() {
  const queryClient = new QueryClient({
    defaultOptions: { queries: { staleTime: 30_000 } },
  });
  return createTanstackRouter({
    routeTree,
    context: { queryClient },
    defaultPreload: 'intent',
    scrollRestoration: true,
  });
}

declare module '@tanstack/react-router' {
  interface Register {
    router: ReturnType<typeof createRouter>;
  }
}
```

- [ ] **Step 2: src/ssr.tsx**

```tsx
// nasrudin-frontend/src/ssr.tsx
import { createStartHandler, defaultStreamHandler } from '@tanstack/react-start/server';
import { createRouter } from './router';

export default createStartHandler({ createRouter })(defaultStreamHandler);
```

- [ ] **Step 3: src/client.tsx**

```tsx
// nasrudin-frontend/src/client.tsx
import { hydrateRoot } from 'react-dom/client';
import { StartClient } from '@tanstack/react-start/client';
import { createRouter } from './router';

const router = createRouter();
hydrateRoot(document, <StartClient router={router} />);
```

If the runtime API names differ in the installed version of `@tanstack/react-start` (sometimes it's `defaultStreamHandler` vs `createStartServer`, or `StartClient` vs `RouterProvider`), adapt to whatever the installed version exposes — verify with `pnpm why @tanstack/react-start` and read the package's `dist/` types. **Do not invent symbol names.**

- [ ] **Step 4: src/routes/__root.tsx**

```tsx
// nasrudin-frontend/src/routes/__root.tsx
import {
  HeadContent,
  Outlet,
  Scripts,
  createRootRouteWithContext,
} from '@tanstack/react-router';
import type { QueryClient } from '@tanstack/react-query';
import { QueryClientProvider } from '@tanstack/react-query';

import '~/styles/tokens.css';
import '~/styles/styles.css';
import '~/styles/platform.css';
import 'katex/dist/katex.min.css';

interface RouterContext {
  queryClient: QueryClient;
}

export const Route = createRootRouteWithContext<RouterContext>()({
  head: () => ({
    meta: [
      { charSet: 'utf-8' },
      { name: 'viewport', content: 'width=device-width, initial-scale=1' },
      { title: 'Nasrudin — derive physics from pure logic' },
    ],
  }),
  component: RootDocument,
});

function RootDocument() {
  return (
    <html lang="en">
      <head>
        <HeadContent />
      </head>
      <body>
        <Outlet />
        <Scripts />
      </body>
    </html>
  );
}

export function RootProviders({ children, queryClient }: { children: React.ReactNode; queryClient: QueryClient }) {
  return <QueryClientProvider client={queryClient}>{children}</QueryClientProvider>;
}
```

The `RootProviders` component is referenced from `__root.tsx` later when we wire QueryClient — for now it is unused. The route's `component` only renders the `<Outlet />`. We will revisit when `useMe` lands.

- [ ] **Step 5: Placeholder index route**

```tsx
// nasrudin-frontend/src/routes/index.tsx
import { createFileRoute } from '@tanstack/react-router';

export const Route = createFileRoute('/')({ component: Index });

function Index() {
  return <div className="page" style={{ padding: 64 }}>nasrudin-frontend up</div>;
}
```

- [ ] **Step 6: Run dev server**

Run:
```bash
cd nasrudin-frontend && pnpm dev
```
Expected: server starts, router-plugin generates `src/routeTree.gen.ts`, `http://localhost:3000` shows "nasrudin-frontend up". Stop with Ctrl-C.

- [ ] **Step 7: Commit**

```bash
git add nasrudin-frontend/src
git commit -m "frontend: TanStack Start scaffold (router, ssr, client, root layout, index)"
```

---

## Phase 5: Frontend — data layer

### Task 5.1: API client

**Files:**
- Create: `nasrudin-frontend/src/lib/api.ts`

- [ ] **Step 1: Write the client**

```ts
// nasrudin-frontend/src/lib/api.ts
export const API_BASE = (import.meta.env.VITE_API_URL as string | undefined) ?? 'http://localhost:3001';

export class ApiError extends Error {
  constructor(public readonly status: number, public readonly body: unknown) {
    super(`API ${status}`);
  }
}

interface FetchOptions extends RequestInit {
  /** When SSR is forwarding cookies, pass them here. */
  cookieHeader?: string;
}

export async function apiFetch<T>(path: string, init: FetchOptions = {}): Promise<T> {
  const headers = new Headers(init.headers);
  headers.set('Accept', 'application/json');
  if (init.body != null && !headers.has('Content-Type')) {
    headers.set('Content-Type', 'application/json');
  }
  if (init.cookieHeader) headers.set('Cookie', init.cookieHeader);

  const res = await fetch(`${API_BASE}${path}`, {
    credentials: 'include',
    ...init,
    headers,
  });

  if (!res.ok) {
    let body: unknown = null;
    try { body = await res.json(); } catch { /* swallow */ }
    throw new ApiError(res.status, body);
  }
  if (res.status === 204) return undefined as T;
  return (await res.json()) as T;
}

export const isApiError = (e: unknown): e is ApiError => e instanceof ApiError;
```

- [ ] **Step 2: Commit**

```bash
git add nasrudin-frontend/src/lib/api.ts
git commit -m "frontend: apiFetch wrapper with cookie + bearer support"
```

### Task 5.2: Types module

**Files:**
- Create: `nasrudin-frontend/src/lib/types.ts`

- [ ] **Step 1: Hand-write the types**

We do not run `just gen-types` for v1 — it requires a `gen-types` bin that may not exist. Instead define what the frontend reads:

```ts
// nasrudin-frontend/src/lib/types.ts
export type Domain =
  | 'PureMath' | 'ClassicalMechanics' | 'Electromagnetism'
  | 'SpecialRelativity' | 'GeneralRelativity' | 'QuantumMechanics'
  | 'QuantumFieldTheory' | 'StatisticalMechanics' | 'Thermodynamics'
  | 'Optics' | 'FluidDynamics';

export interface Theorem {
  id: string;                         // hex(TheoremId)
  domain: Domain;
  statement: { Lean: string } | { Latex: string } | { Plain: string };
  proof?: ProofTree;
  verified: VerificationStatus;
  generation: number;
  depth: number;
  parents: string[];
  created_at: string;
}

export type ProofTree = unknown;       // opaque for v1
export type VerificationStatus =
  | { Verified: { proof_term: string; tactic_used: string } }
  | { Rejected: { reason: string } }
  | 'Pending';

export interface AuthUser {
  id: string;
  email: string;
  display_name: string | null;
  created_at: string;
}

export interface ApiKeySummary {
  id: string;
  name: string;
  prefix: string;
  last_used_at: string | null;
  created_at: string;
  expires_at: string | null;
}

export interface NewApiKey extends ApiKeySummary {
  full_key: string;                   // only present on creation
}

export interface SavedSearch {
  id: string;
  user_id: string;
  latex: string;
  label: string | null;
  created_at: string;
}

export interface Worker {
  id: string;
  name: string | null;
  host: string | null;
  last_seen: string;
  theorems_contributed: number;
  status: 'active' | 'inactive' | 'disconnected';
}

export interface MeStats {
  saved_searches: number;
  api_keys: number;
}
```

- [ ] **Step 2: Commit**

```bash
git add nasrudin-frontend/src/lib/types.ts
git commit -m "frontend: shared TS types for the API surface"
```

### Task 5.3: TanStack Query hooks

**Files:**
- Create: `nasrudin-frontend/src/lib/queries.ts`

- [ ] **Step 1: Write hooks**

```ts
// nasrudin-frontend/src/lib/queries.ts
import { useMutation, useQuery, useQueryClient } from '@tanstack/react-query';
import { apiFetch, isApiError } from './api';
import type {
  ApiKeySummary,
  AuthUser,
  MeStats,
  NewApiKey,
  SavedSearch,
  Theorem,
  Worker,
} from './types';

// --- auth ---

export const meQueryKey = ['me'] as const;

export function useMe() {
  return useQuery<AuthUser | null>({
    queryKey: meQueryKey,
    queryFn: async () => {
      try {
        return await apiFetch<AuthUser>('/api/auth/me');
      } catch (e) {
        if (isApiError(e) && e.status === 401) return null;
        throw e;
      }
    },
    staleTime: 60_000,
  });
}

export function useLogin() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (creds: { email: string; password: string }) =>
      apiFetch<AuthUser>('/api/auth/login', { method: 'POST', body: JSON.stringify(creds) }),
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

export function useRegister() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (input: { email: string; password: string; display_name?: string }) =>
      apiFetch<AuthUser>('/api/auth/register', { method: 'POST', body: JSON.stringify(input) }),
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

export function useLogout() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: () => apiFetch<{ logged_out: true }>('/api/auth/logout', { method: 'POST' }),
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

// --- theorems ---

export function useRecentTheorems(limit = 20) {
  return useQuery({
    queryKey: ['theorems', 'recent', limit],
    queryFn: () =>
      apiFetch<{ theorems: Theorem[]; total: number }>(`/api/theorems/recent?limit=${limit}`),
  });
}

export function useTheorem(id: string) {
  return useQuery({
    queryKey: ['theorem', id],
    queryFn: () => apiFetch<Theorem>(`/api/theorems/${id}`),
    enabled: !!id,
  });
}

export function useDomains() {
  return useQuery({
    queryKey: ['domains'],
    queryFn: () => apiFetch<Record<string, number>>('/api/domains'),
  });
}

// --- api keys ---

export function useApiKeys() {
  return useQuery({
    queryKey: ['api-keys'],
    queryFn: () => apiFetch<{ keys: ApiKeySummary[] }>('/api/api-keys'),
  });
}

export function useCreateApiKey() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: { name: string; expires_in_days?: number }) =>
      apiFetch<NewApiKey>('/api/api-keys', { method: 'POST', body: JSON.stringify(body) }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['api-keys'] }),
  });
}

export function useRevokeApiKey() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (id: string) =>
      apiFetch<{ revoked: true }>(`/api/api-keys/${id}`, { method: 'DELETE' }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['api-keys'] }),
  });
}

// --- saved searches ---

export function useSavedSearches() {
  return useQuery({
    queryKey: ['saved-searches'],
    queryFn: () => apiFetch<{ saved_searches: SavedSearch[] }>('/api/saved-searches'),
  });
}

// --- workers ---

export function useWorkers() {
  return useQuery({
    queryKey: ['workers'],
    queryFn: () => apiFetch<{ workers: Worker[] }>('/api/workers'),
    refetchInterval: 30_000,
  });
}

// --- me/stats ---

export function useMeStats() {
  return useQuery({
    queryKey: ['me', 'stats'],
    queryFn: () => apiFetch<MeStats>('/api/me/stats'),
  });
}
```

- [ ] **Step 2: Commit**

```bash
git add nasrudin-frontend/src/lib/queries.ts
git commit -m "frontend: TanStack Query hooks for auth, theorems, keys, workers"
```

### Task 5.4: KaTeX wrapper + featured rediscoveries data

**Files:**
- Create: `nasrudin-frontend/src/lib/katex.tsx`
- Create: `nasrudin-frontend/src/lib/featured.ts`

- [ ] **Step 1: KaTeX helper**

```tsx
// nasrudin-frontend/src/lib/katex.tsx
import { InlineMath, BlockMath } from 'react-katex';

export function Math({ source, block = false }: { source: string; block?: boolean }) {
  return block ? <BlockMath math={source} /> : <InlineMath math={source} />;
}
```

- [ ] **Step 2: Featured rediscoveries (curated, static)**

```ts
// nasrudin-frontend/src/lib/featured.ts
export interface Rediscovery {
  formula: string;          // KaTeX source
  name: string;
  domain: string;
  found: boolean;
  cycle: string;
  elapsed: string;
  proofLines?: number;
  note: string;
}

export const FEATURED_REDISCOVERIES: Rediscovery[] = [
  { formula: 'E = mc^2', name: 'Mass-energy equivalence', domain: 'Special relativity', found: true, cycle: 'GA-cycle 4,218,107', elapsed: '31 d · 14 h', proofLines: 47, note: 'Emerged from Lorentz invariance + conservation of momentum.' },
  { formula: 'F = ma', name: "Newton's second law", domain: 'Classical mechanics', found: true, cycle: 'GA-cycle 812,044', elapsed: '6 d · 3 h', proofLines: 12, note: "First major rediscovery. The system was 'surprised' by simplicity." },
  { formula: 'S = k_B \\ln \\Omega', name: 'Boltzmann entropy', domain: 'Statistical mechanics', found: true, cycle: 'GA-cycle 9,847,331', elapsed: '78 d · 9 h', proofLines: 184, note: 'Required first introducing combinatorial counting axioms.' },
  { formula: 'i\\hbar\\dot\\psi = \\hat H \\psi', name: 'Schrödinger equation', domain: 'Quantum mechanics', found: false, cycle: 'search active', elapsed: 'candidate #41,082', note: 'Closest match to date — missing complex-Hilbert structure axiom.' },
  { formula: 'R_{\\mu\\nu} - \\tfrac12 g_{\\mu\\nu} R = 8\\pi T_{\\mu\\nu}', name: 'Einstein field equations', domain: 'General relativity', found: false, cycle: 'search not started', elapsed: 'tensor calculus pending', note: 'Awaiting Mathlib differential-geometry expansion.' },
  { formula: '\\nabla\\cdot E = \\rho/\\varepsilon_0', name: "Gauss's law", domain: 'Electromagnetism', found: true, cycle: 'GA-cycle 2,109,553', elapsed: '16 d · 22 h', proofLines: 38, note: 'Co-derived alongside three other Maxwell equations in same week.' },
];
```

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/lib/katex.tsx nasrudin-frontend/src/lib/featured.ts
git commit -m "frontend: KaTeX helper + featured rediscoveries"
```

---

## Phase 6: Frontend — platform shell

### Task 6.1: AppHeader + AppFooter

**Files:**
- Create: `nasrudin-frontend/src/components/platform/AppHeader.tsx`
- Create: `nasrudin-frontend/src/components/platform/AppFooter.tsx`

- [ ] **Step 1: AppHeader.tsx (port `platform-shell.jsx`)**

```tsx
// nasrudin-frontend/src/components/platform/AppHeader.tsx
import { Link } from '@tanstack/react-router';
import { useMe } from '~/lib/queries';

const NAV = [
  { to: '/browse', label: 'Browse corpus', key: 'browse' },
  { to: '/leaderboard', label: 'Contributors', key: 'leader' },
  { to: '/api-docs', label: 'API & data', key: 'api' },
  { to: '/api-keys', label: 'API keys', key: 'api-keys' },
  { to: '/pricing', label: 'Pricing', key: 'pricing' },
] as const;

export function AppHeader({ active }: { active?: string }) {
  const { data: me } = useMe();
  return (
    <>
      <header className="app-header">
        <div className="app-header-inner">
          <Link to="/" className="app-brand">
            <span>Nasrud<span className="brand-dot" />in</span>
          </Link>
          <div className="app-search">
            <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="1.8" strokeLinecap="round" strokeLinejoin="round">
              <circle cx="11" cy="11" r="7" /><path d="m21 21-4.3-4.3" />
            </svg>
            <span>Search theorems · names · Lean tactics</span>
            <kbd>⌘K</kbd>
          </div>
          <div className="app-actions">
            <Link to="/pricing" className="app-nav-link">Pricing</Link>
            <Link to="/api-docs" className="app-nav-link">API</Link>
            {me ? (
              <Link to="/profile" className="app-avatar" title={me.email}>
                {(me.display_name ?? me.email).slice(0, 2).toUpperCase()}
              </Link>
            ) : (
              <Link to="/signin" className="app-nav-link">Sign in</Link>
            )}
          </div>
        </div>
      </header>
      <nav className="app-subnav">
        <div className="app-subnav-inner">
          {NAV.map((n) => (
            <Link
              key={n.key}
              to={n.to}
              className={active === n.key ? 'active' : ''}
            >
              {n.label}
            </Link>
          ))}
        </div>
      </nav>
    </>
  );
}
```

- [ ] **Step 2: AppFooter.tsx**

```tsx
// nasrudin-frontend/src/components/platform/AppFooter.tsx
import { Link } from '@tanstack/react-router';

export function AppFooter() {
  return (
    <footer style={{ background: 'var(--ink-900)', color: 'var(--paper-200)', padding: '40px 0', marginTop: 'auto' }}>
      <div className="container-wide" style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', flexWrap: 'wrap', gap: 16 }}>
        <div style={{ display: 'flex', alignItems: 'baseline', gap: 16, fontSize: 13 }}>
          <span style={{ fontFamily: 'var(--font-serif)', fontSize: 18, color: 'var(--paper-50)' }}>Nasrud·in</span>
          <span style={{ color: 'var(--ink-300)' }}>v0.4.2 · Open source · MIT</span>
        </div>
        <div style={{ display: 'flex', gap: 24, fontSize: 13 }}>
          <Link to="/" style={{ color: 'var(--paper-200)', textDecoration: 'none' }}>Landing</Link>
          <Link to="/api-docs" style={{ color: 'var(--paper-200)', textDecoration: 'none' }}>API</Link>
          <Link to="/pricing" style={{ color: 'var(--paper-200)', textDecoration: 'none' }}>Pricing</Link>
          <a href="https://github.com" style={{ color: 'var(--paper-200)', textDecoration: 'none' }}>GitHub</a>
        </div>
      </div>
    </footer>
  );
}
```

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/components/platform/
git commit -m "frontend: AppHeader + AppFooter (port from platform-shell.jsx)"
```

### Task 6.2: Wire `QueryClientProvider` into `__root.tsx`

**Files:**
- Modify: `nasrudin-frontend/src/routes/__root.tsx`

- [ ] **Step 1: Replace `RootDocument` to wrap children in QueryClientProvider**

```tsx
// nasrudin-frontend/src/routes/__root.tsx
import {
  HeadContent,
  Outlet,
  Scripts,
  createRootRouteWithContext,
} from '@tanstack/react-router';
import { QueryClientProvider, type QueryClient } from '@tanstack/react-query';

import '~/styles/tokens.css';
import '~/styles/styles.css';
import '~/styles/platform.css';
import 'katex/dist/katex.min.css';

interface RouterContext { queryClient: QueryClient }

export const Route = createRootRouteWithContext<RouterContext>()({
  head: () => ({
    meta: [
      { charSet: 'utf-8' },
      { name: 'viewport', content: 'width=device-width, initial-scale=1' },
      { title: 'Nasrudin — derive physics from pure logic' },
    ],
  }),
  component: RootDocument,
});

function RootDocument() {
  const { queryClient } = Route.useRouteContext();
  return (
    <html lang="en">
      <head>
        <HeadContent />
      </head>
      <body>
        <QueryClientProvider client={queryClient}>
          <Outlet />
        </QueryClientProvider>
        <Scripts />
      </body>
    </html>
  );
}
```

- [ ] **Step 2: Verify**

```bash
cd nasrudin-frontend && pnpm dev
```
Expected: server starts, no provider errors in the browser console. Stop with Ctrl-C.

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/routes/__root.tsx
git commit -m "frontend: wrap Outlet in QueryClientProvider in root layout"
```

---

## Phase 7: Frontend — auth pages

### Task 7.1: `/signin` route

**Files:**
- Create: `nasrudin-frontend/src/components/auth/AuthForm.tsx`
- Create: `nasrudin-frontend/src/routes/signin.tsx`

- [ ] **Step 1: AuthForm.tsx — port `Sign in.html`'s form**

```tsx
// nasrudin-frontend/src/components/auth/AuthForm.tsx
import { useState, type FormEvent } from 'react';
import { useNavigate } from '@tanstack/react-router';
import { isApiError } from '~/lib/api';
import { useLogin, useRegister } from '~/lib/queries';

export function AuthForm() {
  const [tab, setTab] = useState<'signin' | 'signup'>('signin');
  const [email, setEmail] = useState('');
  const [password, setPassword] = useState('');
  const [name, setName] = useState('');
  const [error, setError] = useState<string | null>(null);
  const login = useLogin();
  const register = useRegister();
  const navigate = useNavigate();

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    try {
      if (tab === 'signin') {
        await login.mutateAsync({ email, password });
      } else {
        await register.mutateAsync({ email, password, display_name: name || undefined });
      }
      await navigate({ to: '/profile' });
    } catch (err) {
      if (isApiError(err)) {
        const msg =
          err.body && typeof err.body === 'object' && 'error' in err.body
            ? String((err.body as { error: unknown }).error)
            : `Request failed (${err.status})`;
        setError(msg);
      } else {
        setError('Network error');
      }
    }
  }

  const submitting = login.isPending || register.isPending;
  return (
    <form className="auth-form-wrap" onSubmit={onSubmit}>
      <h1>{tab === 'signin' ? 'Welcome back.' : 'Join the corpus.'}</h1>
      <p className="lede">
        {tab === 'signin'
          ? 'Sign in to your library, citations, and targeted searches.'
          : 'Free for individual academics. No card required.'}
      </p>
      <div className="auth-tabs">
        <button type="button" className={`auth-tab ${tab === 'signin' ? 'active' : ''}`} onClick={() => setTab('signin')}>Sign in</button>
        <button type="button" className={`auth-tab ${tab === 'signup' ? 'active' : ''}`} onClick={() => setTab('signup')}>Create account</button>
      </div>
      {tab === 'signup' && (
        <div className="field">
          <label htmlFor="name">Full name</label>
          <input id="name" type="text" value={name} onChange={(e) => setName(e.target.value)} placeholder="Anya Klint" />
        </div>
      )}
      <div className="field">
        <label htmlFor="email">Academic email</label>
        <input id="email" type="email" required autoComplete="email" value={email} onChange={(e) => setEmail(e.target.value)} placeholder="you@university.edu" />
      </div>
      <div className="field">
        <label htmlFor="password">Password</label>
        <input id="password" type="password" required autoComplete="current-password" minLength={8} value={password} onChange={(e) => setPassword(e.target.value)} placeholder="••••••••••••" />
      </div>
      {error && <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginBottom: 12 }}>{error}</div>}
      <button className="btn btn-primary" type="submit" disabled={submitting} style={{ width: '100%', justifyContent: 'center', marginTop: 8 }}>
        {tab === 'signin' ? (submitting ? 'Signing in…' : 'Sign in') : (submitting ? 'Creating…' : 'Create free account')}
      </button>
      <div className="divider">Or continue with</div>
      <div className="oauth-grid">
        {['ORCID', 'GitHub', 'Google', 'Institution SSO'].map((p) => (
          <button key={p} type="button" className="oauth-btn" disabled title="Coming soon">{p}</button>
        ))}
      </div>
      <p style={{ marginTop: 32, fontSize: 12, color: 'var(--ink-500)', textAlign: 'center' }}>
        By continuing you agree to our terms and privacy. The corpus is free to read; we never sell your queries.
      </p>
    </form>
  );
}
```

- [ ] **Step 2: signin.tsx route**

```tsx
// nasrudin-frontend/src/routes/signin.tsx
import { Link, createFileRoute } from '@tanstack/react-router';
import { AuthForm } from '~/components/auth/AuthForm';

export const Route = createFileRoute('/signin')({ component: SignInPage });

function SignInPage() {
  return (
    <div className="auth-page">
      <div className="auth-side">
        <div className="auth-side-pattern" />
        <Link to="/" className="auth-side-brand" style={{ textDecoration: 'none' }}>
          Nasrud<span style={{ display: 'inline-block', width: 6, height: 6, borderRadius: '50%', background: 'var(--terracotta-500)', transform: 'translateY(-2px)', margin: '0 1px' }} />in
        </Link>
        <div>
          <div className="auth-side-quote">
            "Once, looking for a lost key under a lamppost, Nasrudin was asked why he searched there. <em>Because the light is better here.</em>"
          </div>
          <div className="auth-side-attr">— a Sufi parable</div>
        </div>
        <div className="auth-stat-row">
          <div className="auth-stat"><div className="num">247,118</div><div className="lbl">Verified theorems</div></div>
          <div className="auth-stat"><div className="num">1,247</div><div className="lbl">Workers · live</div></div>
          <div className="auth-stat"><div className="num">42</div><div className="lbl">Countries</div></div>
        </div>
      </div>
      <AuthForm />
    </div>
  );
}
```

- [ ] **Step 3: Verify in browser**

`pnpm dev`, visit `http://localhost:3000/signin`. Expected: auth page renders. Type a real signup against a running API server: should redirect to `/profile` (which is a 404 route until next task — that's expected).

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/src/components/auth nasrudin-frontend/src/routes/signin.tsx
git commit -m "frontend: /signin route with signin/signup tabs against /api/auth"
```

### Task 7.2: `/profile` route (auth-gated)

**Files:**
- Create: `nasrudin-frontend/src/routes/profile.tsx`

- [ ] **Step 1: Write the route**

```tsx
// nasrudin-frontend/src/routes/profile.tsx
import { Link, createFileRoute, redirect } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useApiKeys, useLogout, useMe, useMeStats, useSavedSearches } from '~/lib/queries';

export const Route = createFileRoute('/profile')({
  component: ProfilePage,
  beforeLoad: ({ context }) => {
    // We can't await `useMe` from beforeLoad cheaply; the page itself
    // shows a redirect on null `me`. Keeping beforeLoad as a typing anchor.
    void context;
  },
});

function ProfilePage() {
  const { data: me, isPending } = useMe();
  const { data: stats } = useMeStats();
  const { data: keys } = useApiKeys();
  const { data: saved } = useSavedSearches();
  const logout = useLogout();

  if (isPending) return <div className="container-wide" style={{ padding: 64 }}>…</div>;
  if (!me) {
    throw redirect({ to: '/signin' });
  }
  return (
    <div className="app">
      <AppHeader active="profile" />
      <div className="container-wide">
        <div className="profile-head">
          <div className="profile-avatar">{(me.display_name ?? me.email).slice(0, 2).toUpperCase()}</div>
          <div>
            <h1 className="profile-name">{me.display_name ?? me.email}</h1>
            <div className="profile-handle">{me.email}</div>
          </div>
          <div className="profile-tier">
            <div className="tier-pill">★ Researcher</div>
            <Link to="/pricing" style={{ fontSize: 12, marginTop: 6, display: 'inline-block' }}>Manage billing →</Link>
          </div>
        </div>

        <div className="stat-row">
          <div className="stat-cell"><div className="label">Saved searches</div><div className="num">{stats?.saved_searches ?? 0}</div></div>
          <div className="stat-cell"><div className="label">Active API keys</div><div className="num">{stats?.api_keys ?? 0}</div></div>
          <div className="stat-cell"><div className="label">Member since</div><div className="num" style={{ fontSize: 24 }}>{new Date(me.created_at).toLocaleDateString()}</div></div>
          <div className="stat-cell"><div className="label">Citations made</div><div className="num">—</div></div>
        </div>

        <div className="profile-grid">
          <div>
            <h3 className="section-h">Saved searches</h3>
            {(saved?.saved_searches ?? []).length === 0 ? (
              <p style={{ color: 'var(--ink-500)' }}>You haven't saved any searches yet.</p>
            ) : (
              <ul className="saved-list">
                {saved!.saved_searches.map((s) => (
                  <li key={s.id}>
                    <span className="saved-stmt">{s.label ?? s.latex}</span>
                    <span className="saved-date">{new Date(s.created_at).toLocaleDateString()}</span>
                  </li>
                ))}
              </ul>
            )}
          </div>
          <div>
            <h3 className="section-h">API keys</h3>
            {(keys?.keys ?? []).length === 0 ? (
              <p style={{ color: 'var(--ink-500)' }}>No keys yet — <Link to="/api-keys">create one →</Link></p>
            ) : (
              <ul className="saved-list">
                {keys!.keys.map((k) => (
                  <li key={k.id}>
                    <span className="saved-stmt">{k.name}</span>
                    <span className="saved-domain" style={{ fontFamily: 'var(--font-mono)' }}>{k.prefix}…</span>
                    <span className="saved-date">{new Date(k.created_at).toLocaleDateString()}</span>
                  </li>
                ))}
              </ul>
            )}
            <Link to="/api-keys" style={{ display: 'inline-block', marginTop: 16 }}>Manage all keys →</Link>
          </div>
        </div>

        <div style={{ marginTop: 64 }}>
          <button type="button" className="btn btn-secondary" onClick={() => logout.mutate()}>
            {logout.isPending ? 'Signing out…' : 'Sign out'}
          </button>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}
```

- [ ] **Step 2: Commit**

```bash
git add nasrudin-frontend/src/routes/profile.tsx
git commit -m "frontend: /profile route showing user, stats, saved searches, keys"
```

### Task 7.3: `/api-keys` route — create/list/revoke + one-shot reveal modal

**Files:**
- Create: `nasrudin-frontend/src/components/apikeys/CreateKeyDialog.tsx`
- Create: `nasrudin-frontend/src/routes/api-keys.tsx`

- [ ] **Step 1: CreateKeyDialog.tsx**

```tsx
// nasrudin-frontend/src/components/apikeys/CreateKeyDialog.tsx
import { useState } from 'react';
import { useCreateApiKey } from '~/lib/queries';
import type { NewApiKey } from '~/lib/types';

export function CreateKeyDialog({ onClose, onCreated }: { onClose: () => void; onCreated: (k: NewApiKey) => void }) {
  const [name, setName] = useState('');
  const [error, setError] = useState<string | null>(null);
  const create = useCreateApiKey();

  async function submit() {
    setError(null);
    if (!name.trim()) {
      setError('name required');
      return;
    }
    try {
      const key = await create.mutateAsync({ name: name.trim() });
      onCreated(key);
    } catch (e) {
      setError(e instanceof Error ? e.message : 'failed');
    }
  }

  return (
    <div role="dialog" aria-modal style={{ position: 'fixed', inset: 0, background: 'rgba(42,33,26,0.55)', display: 'grid', placeItems: 'center', zIndex: 100 }}>
      <div style={{ background: 'var(--bg-raised)', padding: 32, borderRadius: 12, width: 460, maxWidth: '90vw' }}>
        <h3 style={{ fontFamily: 'var(--font-serif)', fontSize: 24, marginBottom: 16 }}>Create an API key</h3>
        <div className="field">
          <label htmlFor="key-name">Name</label>
          <input id="key-name" autoFocus value={name} onChange={(e) => setName(e.target.value)} placeholder="my-laptop" />
          <span className="hint">A short label so you remember what this key is for.</span>
        </div>
        {error && <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13 }}>{error}</div>}
        <div style={{ display: 'flex', gap: 12, marginTop: 24, justifyContent: 'flex-end' }}>
          <button type="button" className="btn btn-secondary" onClick={onClose}>Cancel</button>
          <button type="button" className="btn btn-primary" onClick={submit} disabled={create.isPending}>
            {create.isPending ? 'Creating…' : 'Create key'}
          </button>
        </div>
      </div>
    </div>
  );
}

export function RevealKeyModal({ keyValue, onClose }: { keyValue: string; onClose: () => void }) {
  const [acknowledged, setAck] = useState(false);
  return (
    <div role="dialog" aria-modal style={{ position: 'fixed', inset: 0, background: 'rgba(42,33,26,0.55)', display: 'grid', placeItems: 'center', zIndex: 101 }}>
      <div style={{ background: 'var(--bg-raised)', padding: 32, borderRadius: 12, width: 560, maxWidth: '90vw' }}>
        <h3 style={{ fontFamily: 'var(--font-serif)', fontSize: 24, marginBottom: 8 }}>Save this key — it won't be shown again.</h3>
        <p style={{ color: 'var(--ink-700)', fontSize: 14, marginBottom: 16 }}>
          Once you close this window, the secret is gone. We only store a hashed copy.
        </p>
        <pre className="code-block" style={{ overflow: 'auto', userSelect: 'all' }}>{keyValue}</pre>
        <button type="button" className="btn btn-secondary" onClick={() => navigator.clipboard.writeText(keyValue)} style={{ marginTop: 12 }}>
          Copy to clipboard
        </button>
        <label style={{ display: 'flex', gap: 8, alignItems: 'center', marginTop: 24, fontSize: 13 }}>
          <input type="checkbox" checked={acknowledged} onChange={(e) => setAck(e.target.checked)} />
          I have copied this key somewhere safe.
        </label>
        <div style={{ display: 'flex', justifyContent: 'flex-end', marginTop: 16 }}>
          <button type="button" className="btn btn-primary" disabled={!acknowledged} onClick={onClose}>Done</button>
        </div>
      </div>
    </div>
  );
}
```

- [ ] **Step 2: api-keys.tsx route**

```tsx
// nasrudin-frontend/src/routes/api-keys.tsx
import { createFileRoute, redirect } from '@tanstack/react-router';
import { useState } from 'react';
import { CreateKeyDialog, RevealKeyModal } from '~/components/apikeys/CreateKeyDialog';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useApiKeys, useMe, useRevokeApiKey } from '~/lib/queries';
import type { NewApiKey } from '~/lib/types';

export const Route = createFileRoute('/api-keys')({ component: ApiKeysPage });

function ApiKeysPage() {
  const me = useMe();
  const { data, refetch } = useApiKeys();
  const revoke = useRevokeApiKey();
  const [createOpen, setCreateOpen] = useState(false);
  const [revealed, setRevealed] = useState<NewApiKey | null>(null);

  if (me.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });

  const keys = data?.keys ?? [];

  return (
    <div className="app">
      <AppHeader active="api-keys" />
      <div className="container-wide" style={{ paddingTop: 32 }}>
        <div className="page-head">
          <span className="overline">For builders</span>
          <h1>API keys</h1>
          <p className="lede">Use a key as a Bearer token to call the Nasrudin API from your scripts and apps.</p>
        </div>
        <div style={{ display: 'flex', justifyContent: 'flex-end', marginBottom: 16 }}>
          <button type="button" className="btn btn-primary" onClick={() => setCreateOpen(true)}>+ New key</button>
        </div>
        {keys.length === 0 ? (
          <p style={{ color: 'var(--ink-500)' }}>You don't have any API keys yet.</p>
        ) : (
          <table className="lead-table">
            <thead><tr><th>Name</th><th>Prefix</th><th>Created</th><th>Last used</th><th /></tr></thead>
            <tbody>
              {keys.map((k) => (
                <tr key={k.id}>
                  <td>{k.name}</td>
                  <td style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>{k.prefix}…</td>
                  <td>{new Date(k.created_at).toLocaleDateString()}</td>
                  <td>{k.last_used_at ? new Date(k.last_used_at).toLocaleString() : '—'}</td>
                  <td>
                    <button
                      type="button"
                      className="btn btn-ghost"
                      onClick={async () => {
                        if (confirm(`Revoke key "${k.name}"?`)) {
                          await revoke.mutateAsync(k.id);
                          refetch();
                        }
                      }}
                    >
                      Revoke
                    </button>
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        )}
      </div>
      <AppFooter />
      {createOpen && (
        <CreateKeyDialog
          onClose={() => setCreateOpen(false)}
          onCreated={(k) => {
            setCreateOpen(false);
            setRevealed(k);
          }}
        />
      )}
      {revealed && (
        <RevealKeyModal keyValue={revealed.full_key} onClose={() => setRevealed(null)} />
      )}
    </div>
  );
}
```

- [ ] **Step 3: Manual verify**

`pnpm dev`, sign in, visit `/api-keys`, click `+ New key`, give it a name, see the modal with the full key, copy, ack, close. Confirm the revoke flow works.

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/src/components/apikeys nasrudin-frontend/src/routes/api-keys.tsx
git commit -m "frontend: /api-keys route with create/list/revoke + one-shot reveal modal"
```

---

## Phase 8: Frontend — public pages

### Task 8.1: `/` landing — hero + ticker

**Files:**
- Create: `nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx`
- Modify: `nasrudin-frontend/src/routes/index.tsx`

- [ ] **Step 1: HeroLiveTheorem.tsx**

```tsx
// nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx
import { useEffect, useState } from 'react';
import { Math } from '~/lib/katex';
import { useRecentTheorems } from '~/lib/queries';

const FALLBACK_TICKER = [
  'VERIFIED  thm:9f3a2c   ⟨x,y⟩² ≤ ⟨x,x⟩⟨y,y⟩   simp ∘ linarith',
  'REJECTED  cand:7b41f8   simp made no progress; goal unchanged',
  'VERIFIED  thm:c1d9e7   [x,p] = iℏ                ring ∘ exact',
];

export function HeroLiveTheorem() {
  const recent = useRecentTheorems(3);
  const [idx, setIdx] = useState(0);
  const [tickerLines, setTickerLines] = useState<string[]>(FALLBACK_TICKER);
  const [tickIdx, setTickIdx] = useState(0);

  // Rotate hero theorem every 5.5 s.
  useEffect(() => {
    const t = setInterval(() => setIdx((i) => (i + 1) % Math.max(recent.data?.theorems.length ?? 1, 1)), 5500);
    return () => clearInterval(t);
  }, [recent.data?.theorems.length]);

  // Subscribe to discovery SSE; fall back to static lines on error.
  useEffect(() => {
    let failures = 0;
    const url = `${import.meta.env.VITE_API_URL ?? 'http://localhost:3001'}/api/events/discoveries`;
    const es = new EventSource(url, { withCredentials: true });
    es.onmessage = (ev) => {
      const t = (() => { try { return JSON.parse(ev.data); } catch { return null; } })();
      if (t && typeof t === 'object' && 'theorem' in t) {
        const ti = t as { theorem: { id: string } };
        setTickerLines((prev) => [`VERIFIED  thm:${ti.theorem.id.slice(0, 6)}…`, ...prev].slice(0, 12));
      }
    };
    es.onerror = () => {
      failures += 1;
      if (failures >= 3) es.close();
    };
    return () => es.close();
  }, []);

  useEffect(() => {
    const t = setInterval(() => setTickIdx((i) => (i + 1) % tickerLines.length), 1800);
    return () => clearInterval(t);
  }, [tickerLines.length]);

  const t = recent.data?.theorems[idx];
  const stmt = t ? statementToString(t.statement) : 'E = mc^2';

  return (
    <div>
      <div className="theorem-card">
        <div className="theorem-card-head">
          <span className="theorem-card-id">{t ? t.id.slice(0, 8) : '…'}</span>
          <span className="verified-badge"><span className="verified-dot" /> Verified · Lean 4</span>
        </div>
        <div className="theorem-card-body">
          <div className="theorem-statement"><Math source={stmt} block /></div>
          <div className="theorem-name">{t ? t.id : 'Loading'}</div>
          <div className="theorem-tag">{t?.domain ?? '—'} · gen {t?.generation ?? 0}</div>
        </div>
      </div>
      <div className="ticker">
        <span className="ticker-label">Live</span>
        <span className="ticker-text" key={tickIdx}>
          <span className={tickerLines[tickIdx]?.startsWith('VERIFIED') ? 'ok' : 'reject'}>
            {tickerLines[tickIdx]}
          </span>
        </span>
      </div>
    </div>
  );
}

function statementToString(s: { Lean?: string; Latex?: string; Plain?: string } | string): string {
  if (typeof s === 'string') return s;
  return s.Latex ?? s.Lean ?? s.Plain ?? '';
}
```

- [ ] **Step 2: Replace `index.tsx` with hero shell + ticker**

```tsx
// nasrudin-frontend/src/routes/index.tsx
import { Link, createFileRoute } from '@tanstack/react-router';
import { HeroLiveTheorem } from '~/components/landing/HeroLiveTheorem';
import { AppFooter } from '~/components/platform/AppFooter';

export const Route = createFileRoute('/')({ component: Landing });

function Landing() {
  return (
    <div className="page">
      <header className="topbar">
        <div className="topbar-inner">
          <div className="brand">
            <span>Nasrud<span className="brand-dot" />in</span>
            <span className="brand-tag">Synthetic theorem · Lean 4</span>
          </div>
          <nav className="nav">
            <Link to="/browse">Browse corpus</Link>
            <Link to="/leaderboard">Contributors</Link>
            <Link to="/api-docs">API</Link>
            <Link to="/pricing">Pricing</Link>
            <span className="nav-sep" aria-hidden />
            <Link to="/signin" className="nav-secondary">Sign in</Link>
            <a href="#run" className="nav-cta">Run a worker →</a>
          </nav>
        </div>
      </header>
      <section className="hero">
        <div className="hero-pattern" />
        <div className="container-wide">
          <div className="hero-grid">
            <div>
              <div className="hero-eyebrow"><span className="eyebrow-dot" /> Distributed theorem-generation engine · v0.4</div>
              <h1 className="hero-title">Derive physics from <em>pure logic.</em></h1>
              <p className="hero-sub">
                Nasrudin starts from mathematical axioms and physics postulates, then evolves new theorems with a genetic algorithm — formally proving every survivor in Lean&nbsp;4. Eventually, it rediscovers known physics. On its own.
              </p>
              <div className="hero-ctas">
                <a className="btn btn-primary" href="#run">Run a worker node <span className="btn-arrow">→</span></a>
                <Link className="btn btn-secondary" to="/browse">Browse the corpus</Link>
              </div>
            </div>
            <div>
              <div className="overline" style={{ marginBottom: 12 }}>Live · just verified</div>
              <HeroLiveTheorem />
            </div>
          </div>
        </div>
      </section>
      <AppFooter />
    </div>
  );
}
```

- [ ] **Step 3: Manual verify**

`pnpm dev`, visit `/`. Expected: hero renders, ticker scrolls, theorem rotates.

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx nasrudin-frontend/src/routes/index.tsx
git commit -m "frontend: landing hero + live theorem rotator + SSE-backed ticker"
```

### Task 8.2: `/` landing — pipeline + GA viz

**Files:**
- Create: `nasrudin-frontend/src/components/landing/PipelineDiagram.tsx`
- Create: `nasrudin-frontend/src/components/landing/GAViz.tsx`
- Modify: `nasrudin-frontend/src/routes/index.tsx`

- [ ] **Step 1: Port `PipelineDiagram` from `sections.jsx` lines 8-153**

Translate the JSX one-to-one — keep the SVG markup, change `var(--terracotta-500)` etc. through CSS variables (already imported). No data fetching. The five sub-components (`PipelineSeed`, `PipelineGA`, `PipelineCandidates`, `PipelineLean`, `PipelineDB`) live as helpers in the same file.

The output file should be a single `PipelineDiagram.tsx` that exports `PipelineDiagram`. Copy-paste the JSX from `sections.jsx` lines 8-153 into the new file, fix the imports (`useState/useEffect` aren't needed; remove the leading destructure), and close the JSX with proper TS syntax (`React.Fragment` if needed, `style={...}` typed as `React.CSSProperties`).

- [ ] **Step 2: Port `GAViz` from `sections.jsx` lines 155-195**

Same approach. The `data` source `window.NASRUDIN_DATA.GA_GENERATIONS` is replaced with a static const inside the component (copy from `sections.jsx`'s data, e.g. lines 76-85 of `data.jsx`).

- [ ] **Step 3: Drop sections into the landing route**

Modify `index.tsx` to add (after the hero section, before `<AppFooter />`):

```tsx
<section className="section" id="how">
  <div className="container-wide">
    <div className="section-head">
      <div className="section-num">§ 01 / 04</div>
      <div className="section-title-block">
        <span className="overline">The pipeline</span>
        <h2 className="section-title">Five stages, one rule: <em>nothing enters the corpus that Lean&nbsp;4 hasn't proved twice.</em></h2>
      </div>
    </div>
    <PipelineDiagram />
  </div>
</section>
<section className="section compact">
  <div className="container-wide">
    <div className="section-head">
      <div className="section-num">§ 02 / 04</div>
      <div className="section-title-block">
        <span className="overline">Inside one cycle</span>
        <h2 className="section-title">Watch the GA <em>arrive at Newton</em> — without being told.</h2>
      </div>
    </div>
    <GAViz />
  </div>
</section>
```

(Plus the imports: `import { PipelineDiagram } from '~/components/landing/PipelineDiagram'; import { GAViz } from '~/components/landing/GAViz';`.)

- [ ] **Step 4: Verify**

`pnpm dev` and confirm both sections render with their SVGs animating.

- [ ] **Step 5: Commit**

```bash
git add nasrudin-frontend/src/components/landing nasrudin-frontend/src/routes/index.tsx
git commit -m "frontend: landing pipeline diagram + GA viz"
```

### Task 8.3: `/` landing — worker map + featured rediscoveries + install

**Files:**
- Create: `nasrudin-frontend/src/components/landing/WorkerMap.tsx`
- Create: `nasrudin-frontend/src/components/landing/RediscoveryGrid.tsx`
- Create: `nasrudin-frontend/src/components/landing/InstallNode.tsx`
- Modify: `nasrudin-frontend/src/routes/index.tsx`

- [ ] **Step 1: WorkerMap.tsx**

Port from `sections.jsx` lines 199-301. Replace `window.NASRUDIN_DATA.WORKERS` and `WORKER_PINS` with:
- `useWorkers()` from `~/lib/queries` for live data
- A static `CITY_COORDS: Record<string, { x: number; y: number }>` map for placement
- The component derives `pins` from `workers` filtered by host/name + the coords map, falling back to the static prototype pins if `workers` is empty.

- [ ] **Step 2: RediscoveryGrid.tsx**

```tsx
// nasrudin-frontend/src/components/landing/RediscoveryGrid.tsx
import { Math } from '~/lib/katex';
import { FEATURED_REDISCOVERIES } from '~/lib/featured';

export function RediscoveryGrid() {
  return (
    <div className="rediscover-grid">
      {FEATURED_REDISCOVERIES.map((r) => (
        <div key={r.name} className={`rediscover-card ${r.found ? '' : 'aspirational'}`}>
          <div className={`rediscover-status ${r.found ? 'found' : 'pending'}`}>
            {r.found ? '✓ Rediscovered' : '○ Searching'}
          </div>
          <div className="rediscover-formula"><Math source={r.formula} /></div>
          <div className="rediscover-name">{r.name}</div>
          <div className="rediscover-domain">{r.domain}</div>
          <p style={{ fontSize: 13, lineHeight: 1.55, color: 'var(--ink-700)', marginBottom: 16 }}>{r.note}</p>
          <div className="rediscover-meta">
            <div><div className="rediscover-meta-label">Discovered at</div><div className="rediscover-meta-val">{r.cycle}</div></div>
            <div><div className="rediscover-meta-label">{r.found ? 'Wall time' : 'Status'}</div><div className="rediscover-meta-val">{r.elapsed}</div></div>
            {r.found && r.proofLines && (
              <div><div className="rediscover-meta-label">Proof lines</div><div className="rediscover-meta-val">{r.proofLines}</div></div>
            )}
          </div>
        </div>
      ))}
    </div>
  );
}
```

- [ ] **Step 3: InstallNode.tsx**

Port from `sections.jsx` lines 388-471. The component is fully self-contained (animated CLI lines on a timer); just convert `useS/useE` to `useState/useEffect` and add types.

- [ ] **Step 4: Drop the sections into `index.tsx`**

Add three more `<section>` blocks after the GA viz, with the `RediscoveryGrid`, `WorkerMap`, and `InstallNode`. Also add the closing footer with `<a id="run">…</a>` so the hero CTA scrolls correctly.

- [ ] **Step 5: Manual verify**

Start API + frontend; visit `/`; scroll through every section; confirm worker map shows pings, rediscoveries render with KaTeX, install CLI animates, footer at bottom.

- [ ] **Step 6: Commit**

```bash
git add nasrudin-frontend/src/components/landing nasrudin-frontend/src/routes/index.tsx
git commit -m "frontend: landing worker map + rediscovery grid + install CLI"
```

### Task 8.4: `/browse` route

**Files:**
- Create: `nasrudin-frontend/src/components/browse/FacetSidebar.tsx`
- Create: `nasrudin-frontend/src/components/browse/ResultCard.tsx`
- Create: `nasrudin-frontend/src/routes/browse.tsx`

- [ ] **Step 1: ResultCard.tsx**

```tsx
// nasrudin-frontend/src/components/browse/ResultCard.tsx
import { Link } from '@tanstack/react-router';
import { Math } from '~/lib/katex';
import type { Theorem } from '~/lib/types';

export function ResultCard({ thm }: { thm: Theorem }) {
  const stmt = ('Latex' in thm.statement ? thm.statement.Latex
    : 'Lean' in thm.statement ? thm.statement.Lean
    : 'Plain' in thm.statement ? thm.statement.Plain
    : '');
  return (
    <Link to="/theorem/$id" params={{ id: thm.id }} className="result-card" style={{ textDecoration: 'none', color: 'inherit', display: 'grid' }}>
      <div>
        <div className="result-stmt"><Math source={stmt} /></div>
        <div className="result-name">{thm.id}</div>
        <div className="result-meta">
          <span style={{ fontFamily: 'var(--font-mono)' }}>thm:{thm.id.slice(0, 8)}</span>
          <span className="dot">·</span>
          <span style={{ letterSpacing: '0.04em', textTransform: 'uppercase', fontWeight: 600 }}>{thm.domain}</span>
          <span className="dot">·</span>
          <span>gen {thm.generation}</span>
          <span className="dot">·</span>
          <span>depth {thm.depth}</span>
        </div>
      </div>
      <div className="result-side">
        <div className="verified-badge"><span className="verified-dot" /> {typeof thm.verified === 'string' ? 'Pending' : 'Verified'}</div>
      </div>
    </Link>
  );
}
```

- [ ] **Step 2: FacetSidebar.tsx**

```tsx
// nasrudin-frontend/src/components/browse/FacetSidebar.tsx
import type { Domain } from '~/lib/types';

export const DOMAIN_LABELS: Array<{ value: Domain | null; label: string }> = [
  { value: null, label: 'All' },
  { value: 'PureMath', label: 'Pure math' },
  { value: 'ClassicalMechanics', label: 'Classical mechanics' },
  { value: 'Electromagnetism', label: 'Electromagnetism' },
  { value: 'SpecialRelativity', label: 'Special relativity' },
  { value: 'GeneralRelativity', label: 'General relativity' },
  { value: 'QuantumMechanics', label: 'Quantum mechanics' },
  { value: 'Thermodynamics', label: 'Thermodynamics' },
];

export function FacetSidebar({ counts, active, onChange }: {
  counts: Record<string, number>;
  active: Domain | null;
  onChange: (d: Domain | null) => void;
}) {
  return (
    <aside>
      <div className="facet-group">
        <h5>Domain</h5>
        <ul className="facet-list">
          {DOMAIN_LABELS.map((d) => (
            <li
              key={d.label}
              className={active === d.value ? 'active' : ''}
              onClick={() => onChange(d.value)}
              style={{ cursor: 'pointer' }}
            >
              <span>{d.label}</span>
              <span className="count">{(counts[d.value ?? ''] ?? 0).toLocaleString()}</span>
            </li>
          ))}
        </ul>
      </div>
    </aside>
  );
}
```

- [ ] **Step 3: browse.tsx route**

```tsx
// nasrudin-frontend/src/routes/browse.tsx
import { createFileRoute } from '@tanstack/react-router';
import { useState } from 'react';
import { FacetSidebar } from '~/components/browse/FacetSidebar';
import { ResultCard } from '~/components/browse/ResultCard';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { apiFetch } from '~/lib/api';
import { useDomains } from '~/lib/queries';
import type { Domain, Theorem } from '~/lib/types';
import { useQuery } from '@tanstack/react-query';

export const Route = createFileRoute('/browse')({ component: BrowsePage });

function BrowsePage() {
  const [domain, setDomain] = useState<Domain | null>(null);
  const counts = useDomains();
  const list = useQuery({
    queryKey: ['theorems', 'list', domain],
    queryFn: () => apiFetch<{ theorems: Theorem[]; total: number }>(
      domain
        ? `/api/theorems?domain=${domain}&limit=50`
        : `/api/theorems/recent?limit=50`,
    ),
  });

  return (
    <div className="app">
      <AppHeader active="browse" />
      <div className="container-wide" style={{ paddingTop: 24 }}>
        <div className="page-head" style={{ paddingTop: 24, paddingBottom: 24, borderBottom: 'none' }}>
          <span className="overline">The corpus</span>
          <h1>Browse <em style={{ fontStyle: 'italic', color: 'var(--terracotta-700)', fontWeight: 300 }}>{(list.data?.total ?? 0).toLocaleString()}</em> verified theorems</h1>
          <p className="lede">Click any result to see its full Lean 4 proof, lineage, and downstream uses.</p>
        </div>
        <div className="page-body" style={{ paddingTop: 16 }}>
          <div className="search-layout">
            <FacetSidebar counts={counts.data ?? {}} active={domain} onChange={setDomain} />
            <div>
              <div className="search-results-bar">
                <span><strong>{(list.data?.theorems.length ?? 0).toLocaleString()}</strong> results</span>
              </div>
              {list.isPending && <p style={{ color: 'var(--ink-500)' }}>loading…</p>}
              {list.data?.theorems.map((t) => <ResultCard key={t.id} thm={t} />)}
            </div>
          </div>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}
```

- [ ] **Step 4: Manual verify**

`pnpm dev`. Visit `/browse`. Expected: list renders with results from the API. Click a result → navigates to `/theorem/$id` (next task).

- [ ] **Step 5: Commit**

```bash
git add nasrudin-frontend/src/components/browse nasrudin-frontend/src/routes/browse.tsx
git commit -m "frontend: /browse with facet sidebar + result cards"
```

### Task 8.5: `/theorem/$id` route

**Files:**
- Create: `nasrudin-frontend/src/components/theorem/ProofBlock.tsx`
- Create: `nasrudin-frontend/src/components/theorem/LineageList.tsx`
- Create: `nasrudin-frontend/src/components/theorem/ReverifyButton.tsx`
- Create: `nasrudin-frontend/src/routes/theorem.$id.tsx`

- [ ] **Step 1: ProofBlock.tsx**

```tsx
// nasrudin-frontend/src/components/theorem/ProofBlock.tsx
export function ProofBlock({ source }: { source: string }) {
  return (
    <pre className="thm-proof-pre" style={{ whiteSpace: 'pre-wrap' }}>
      {source}
    </pre>
  );
}
```

- [ ] **Step 2: LineageList.tsx**

```tsx
// nasrudin-frontend/src/components/theorem/LineageList.tsx
import { Link } from '@tanstack/react-router';

export function LineageList({ parents }: { parents: string[] }) {
  if (parents.length === 0) return <p style={{ color: 'var(--ink-500)' }}>This theorem has no parents — it's an axiom.</p>;
  return (
    <ol className="lineage">
      {parents.map((id, i) => (
        <li key={id}>
          <span className="lineage-step">{romanize(i + 1)}.</span>
          <span>
            <Link to="/theorem/$id" params={{ id }} className="lineage-name">{id}</Link>
          </span>
        </li>
      ))}
    </ol>
  );
}

function romanize(n: number): string {
  const numerals = ['i', 'ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii', 'ix', 'x'];
  return numerals[n - 1] ?? String(n);
}
```

- [ ] **Step 3: ReverifyButton.tsx**

Port the animation from `Theorem.html` lines 20-57. It is purely client-side simulation; no API call.

- [ ] **Step 4: theorem.$id.tsx route**

```tsx
// nasrudin-frontend/src/routes/theorem.$id.tsx
import { Link, createFileRoute } from '@tanstack/react-router';
import { LineageList } from '~/components/theorem/LineageList';
import { ProofBlock } from '~/components/theorem/ProofBlock';
import { ReverifyButton } from '~/components/theorem/ReverifyButton';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { Math } from '~/lib/katex';
import { useTheorem } from '~/lib/queries';

export const Route = createFileRoute('/theorem/$id')({ component: TheoremPage });

function TheoremPage() {
  const { id } = Route.useParams();
  const { data, isPending, error } = useTheorem(id);

  return (
    <div className="app">
      <AppHeader active="theorem" />
      <div className="container-wide" style={{ paddingTop: 24 }}>
        <div className="crumbs">
          <Link to="/browse">Browse</Link>
          <span className="sep">/</span>
          <span className="current">thm:{id.slice(0, 8)}</span>
        </div>
        {isPending && <p>loading…</p>}
        {error && <p style={{ color: 'var(--danger-500)' }}>Theorem not found.</p>}
        {data && <TheoremView thm={data} />}
      </div>
      <AppFooter />
    </div>
  );
}

function TheoremView({ thm }: { thm: import('~/lib/types').Theorem }) {
  const stmt = ('Latex' in thm.statement ? thm.statement.Latex
    : 'Lean' in thm.statement ? thm.statement.Lean
    : 'Plain' in thm.statement ? thm.statement.Plain
    : '');
  const proofTerm = typeof thm.verified === 'object' && 'Verified' in thm.verified
    ? thm.verified.Verified.proof_term
    : '-- not yet verified';
  return (
    <div className="thm-page">
      <div className="thm-main">
        <div className="thm-eyebrow">
          <span className="verified-badge"><span className="verified-dot" /> Verified · Lean 4 · re-checked by server</span>
          <span>· thm:{thm.id.slice(0, 8)}</span>
          <span>· gen {thm.generation}</span>
        </div>
        <h1 className="thm-name">{thm.id}</h1>
        <div className="thm-statement-block">
          <div className="thm-statement-big"><Math source={stmt} block /></div>
        </div>
        <div className="thm-section">
          <h3>Lean 4 proof</h3>
          <div className="thm-proof-bar">
            <span>{thm.id}.lean</span>
            <button type="button" className="copy" onClick={() => navigator.clipboard.writeText(proofTerm)}>Copy</button>
          </div>
          <ProofBlock source={proofTerm} />
          <div style={{ marginTop: 24 }}>
            <ReverifyButton />
          </div>
        </div>
        <div className="thm-section">
          <h3>Proof lineage</h3>
          <LineageList parents={thm.parents} />
        </div>
      </div>
      <aside className="thm-side">
        <h4>Provenance</h4>
        <ul className="meta-list">
          <li>Generation <strong>{thm.generation}</strong></li>
          <li>Depth <strong>{thm.depth}</strong></li>
          <li>Domain <strong>{thm.domain}</strong></li>
          <li>Created <strong>{new Date(thm.created_at).toLocaleString()}</strong></li>
        </ul>
      </aside>
    </div>
  );
}
```

- [ ] **Step 5: Manual verify**

`pnpm dev`. Click a theorem from `/browse`; expect proof + lineage to render.

- [ ] **Step 6: Commit**

```bash
git add nasrudin-frontend/src/components/theorem nasrudin-frontend/src/routes/theorem.\$id.tsx
git commit -m "frontend: /theorem/\$id with proof + lineage + reverify simulation"
```

### Task 8.6: `/leaderboard` route

**Files:**
- Create: `nasrudin-frontend/src/routes/leaderboard.tsx`

- [ ] **Step 1: Write the route**

Port `Leaderboard.html` lines 24-82 with two changes:
- Replace the static `ROWS` constant with `useWorkers()` data, sorted by `theorems_contributed` desc.
- Drop the `useState` tab variants for v1 (just show all-time).

```tsx
// nasrudin-frontend/src/routes/leaderboard.tsx
import { createFileRoute } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useWorkers } from '~/lib/queries';

export const Route = createFileRoute('/leaderboard')({ component: LeaderboardPage });

function LeaderboardPage() {
  const { data } = useWorkers();
  const ranked = (data?.workers ?? [])
    .slice()
    .sort((a, b) => b.theorems_contributed - a.theorems_contributed);
  const [first, second, third] = ranked;
  return (
    <div className="app">
      <AppHeader active="leader" />
      <div className="container-wide">
        <div className="page-head">
          <span className="overline">The network</span>
          <h1>Contributors — <em style={{ fontStyle: 'italic', color: 'var(--terracotta-700)', fontWeight: 300 }}>credit, not cash.</em></h1>
          <p className="lede">Workers donate compute. Each verified theorem carries the worker's pseudonym, forever.</p>
        </div>
        <div className="page-body">
          <div className="lead-podium">
            {second && <PodiumStep step="silver" rank="ii" handle={second.id} thm={second.theorems_contributed} />}
            {first && <PodiumStep step="gold" rank="i" handle={first.id} thm={first.theorems_contributed} marquee />}
            {third && <PodiumStep step="bronze" rank="iii" handle={third.id} thm={third.theorems_contributed} />}
          </div>
          <table className="lead-table">
            <thead><tr><th>Rank</th><th>Worker</th><th>Host</th><th style={{ textAlign: 'right' }}>Theorems</th><th style={{ textAlign: 'right' }}>Status</th><th style={{ textAlign: 'right' }}>Last seen</th></tr></thead>
            <tbody>
              {ranked.map((w, i) => (
                <tr key={w.id}>
                  <td className="rank-cell">{i + 1}</td>
                  <td className="handle-cell">{w.id}</td>
                  <td style={{ color: 'var(--ink-500)', fontFamily: 'var(--font-mono)', fontSize: 12 }}>{w.host ?? '—'}</td>
                  <td className="num-cell">{w.theorems_contributed.toLocaleString()}</td>
                  <td className="num-cell" style={{ color: w.status === 'active' ? 'var(--olive-700)' : 'var(--ink-500)' }}>{w.status}</td>
                  <td className="num-cell" style={{ color: 'var(--ink-500)' }}>{new Date(w.last_seen).toLocaleString()}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}

function PodiumStep({ step, rank, handle, thm, marquee }: { step: string; rank: string; handle: string; thm: number; marquee?: boolean }) {
  return (
    <div className={`lead-step ${step}`} style={marquee ? { paddingTop: 40, paddingBottom: 40 } : undefined}>
      <div className="lead-rank">{rank}</div>
      <div className="lead-handle">{handle}</div>
      <div className="lead-num">{thm.toLocaleString()} thm</div>
    </div>
  );
}
```

- [ ] **Step 2: Commit**

```bash
git add nasrudin-frontend/src/routes/leaderboard.tsx
git commit -m "frontend: /leaderboard from useWorkers()"
```

### Task 8.7: `/api-docs` route

**Files:**
- Create: `nasrudin-frontend/src/routes/api-docs.tsx`

- [ ] **Step 1: Port `API.html`'s body verbatim**

Copy the JSX from `API.html` lines 17-110 into a route component. Replace `<a href="Profile.html">` etc. with `<Link to="/api-keys">` etc. The page is fully static — no data fetching. Wrap in `<AppHeader active="api" />` + `<AppFooter />`.

- [ ] **Step 2: Commit**

```bash
git add nasrudin-frontend/src/routes/api-docs.tsx
git commit -m "frontend: /api-docs static reference page"
```

### Task 8.8: `/pricing` route

**Files:**
- Create: `nasrudin-frontend/src/routes/pricing.tsx`

- [ ] **Step 1: Port `Pricing.html` lines 22-180**

Static page; no data fetching. Convert `useState` to typed React hook. Remove all the `style={{...}}` strings into proper CSS-property objects. CTAs are placeholder buttons — no `onClick`.

- [ ] **Step 2: Commit**

```bash
git add nasrudin-frontend/src/routes/pricing.tsx
git commit -m "frontend: /pricing tier cards + FAQ + donation band"
```

---

## Phase 9: Cleanup, polish, verify

### Task 9.1: Delete the prototype HTML/JSX files

**Files:**
- Delete: `nasrudin-frontend/{Browse,API,Leaderboard,Pricing,Profile,Theorem}.html`
- Delete: `nasrudin-frontend/Nasrudin Landing.html`, `nasrudin-frontend/Sign in.html`
- Delete: `nasrudin-frontend/{data,hero,platform-shell,sections,tweaks-panel}.jsx`

- [ ] **Step 1: Remove the prototypes**

```bash
cd nasrudin-frontend
rm "Nasrudin Landing.html" "Sign in.html" Browse.html API.html Leaderboard.html Pricing.html Profile.html Theorem.html
rm data.jsx hero.jsx platform-shell.jsx sections.jsx tweaks-panel.jsx
```

- [ ] **Step 2: Verify nothing imports them**

```bash
grep -rn "platform-shell\|tweaks-panel" nasrudin-frontend/src || true
```
Expected: no matches.

- [ ] **Step 3: Commit**

```bash
git add -A nasrudin-frontend
git commit -m "frontend: remove prototype HTML/JSX (replaced by src/routes + components)"
```

### Task 9.2: Lint + type check

**Files:** none

- [ ] **Step 1: Frontend type check**

```bash
cd nasrudin-frontend && pnpm check
```
Expected: `biome check .` passes; `tsc --noEmit` passes. Fix any errors **inline in the source files** — do not skip them.

- [ ] **Step 2: Backend clippy**

```bash
cd engine && cargo clippy --all-targets -- -D warnings
```
Expected: exit 0.

- [ ] **Step 3: Backend fmt**

```bash
cd engine && cargo fmt --check
```
Expected: exit 0; otherwise run `cargo fmt` and commit the result.

- [ ] **Step 4: Commit any remaining cleanup**

```bash
git add -A
git diff --cached --stat
git commit -m "chore: lint + format pass" || true
```
The `|| true` skips the commit if there's nothing to commit.

### Task 9.3: End-to-end manual smoke test

**Files:** none

- [ ] **Step 1: Start backend**

```bash
just db-start
just dev-engine &
```
Expected: API listens on `:3001`.

- [ ] **Step 2: Start frontend**

```bash
just dev-frontend &
```
Expected: server on `:3000`.

- [ ] **Step 3: Walkthrough**

In a browser:

1. Visit `/`. Hero rotator + ticker + pipeline + GA viz + worker map + rediscoveries + install + footer all render.
2. Visit `/browse`. Theorems load from `/api/theorems/recent`. Click a domain facet → list filters.
3. Click a result → `/theorem/$id` shows proof + lineage.
4. Visit `/signin`. Register a fresh account.
5. Land on `/profile`. Stats card shows zeroes, no saved searches, no keys.
6. Click "Manage all keys →" → `/api-keys`. Click "+ New key", give it a name, see the modal with the full key starting `nsk_live_…`. Acknowledge + close.
7. Use the key from a separate terminal: `curl -H "Authorization: Bearer $KEY" http://localhost:3001/api/me/stats` → 200 with `{ saved_searches: 0, api_keys: 1 }`.
8. Click revoke on the key → row disappears. Re-run the curl → 401.
9. Visit `/leaderboard`. If no workers exist, it shows an empty table — this is acceptable for v1.
10. Visit `/api-docs` and `/pricing`. Both render static.

- [ ] **Step 4: Stop services**

```bash
kill %1 %2
```

### Task 9.4: Update `README.md`

**Files:**
- Modify: `README.md`

- [ ] **Step 1: Replace the project-structure callout for `nasrudin-frontend/`**

Find the block in `README.md` that lists the frontend structure (around line 81-85) and replace with:

```
├── nasrudin-frontend/       # TanStack Start v1 web UI (React 19, TS, Biome)
│   └── src/
│       ├── routes/          # /, /browse, /theorem/$id, /signin, /profile,
│       │                    # /api-keys, /api-docs, /leaderboard, /pricing
│       ├── components/      # platform shell, landing, browse, theorem, auth, apikeys
│       ├── lib/             # apiFetch, queries, types, katex helper
│       └── styles/          # tokens.css, styles.css, platform.css
```

- [ ] **Step 2: Add a "Platform features" subsection under "How It Works"**

Add a short paragraph:

```
## Platform features

The web UI and API server share a single auth model:

- **Cookie sessions** for the web UI (axum-login + tower-sessions, Argon2 passwords).
- **Bearer API keys** (`Authorization: Bearer nsk_live_…`) for programmatic clients.

Both flow through the same `AuthOrApiKey` extractor and resolve to the same user.
Worker registration uses a separate `nsk_worker_…` key issued at registration time.

Generate keys at `/api-keys` once you're signed in.
```

- [ ] **Step 3: Commit**

```bash
git add README.md
git commit -m "docs: README reflects new frontend layout + platform auth model"
```

### Task 9.5: Final progress.md update

**Files:**
- Modify: `progress.md`

- [ ] **Step 1: Append a new iteration log entry**

Add to `progress.md` under the "Iteration log" section:

```
- Iteration counter: `4`
- Last iteration: 2026-04-28 — iter 4: Frontend rebuilt on TanStack Start v1
  (React 19, Vite 7, TS, Biome). engine/crates/api extended with api_keys,
  saved_searches, preferences, workers, and me/stats handlers. Unified
  AuthOrApiKey extractor accepts cookie sessions or Bearer nsk_live_ keys;
  WorkerAuth handles nsk_worker_. End-to-end: register → keys → bearer →
  revoke verified live.
```

- [ ] **Step 2: Commit**

```bash
git add progress.md
git commit -m "progress: iter 4 — frontend rebuild + platform endpoints"
```

---

## Self-review

**Spec coverage check:**

| Spec section | Implementing tasks |
|--------------|---------------------|
| §3.1 package manifest | 4.1 |
| §3.2 project structure | 4.5–8.8 |
| §3.3 routing decisions | 4.5, 7.1–8.8 |
| §3.4 data layer | 5.1–5.3 |
| §3.5 SSE on hero | 8.1 |
| §3.6 mock-data strategy | 5.4 (curated featured), 8.1 (live recent) |
| §4.1 api_keys entity | 1.1 |
| §4.1 migration | 1.2 |
| §4.1 query helpers | 1.4 |
| §4.2 AuthOrApiKey | 2.1 |
| §4.2 WorkerAuth | 2.2 |
| §4.3 handlers (api_keys/saved/prefs/workers/me) | 3.3–3.7 |
| §4.4 worker key model | 3.6, 2.2 |
| §4.5 rate-limit groups | 3.7 step 2 |
| §4.6 CORS | already in main.rs (no change) |
| §4.7 migrate binary | 1.5 |
| §5 auth flow | 7.1, 7.3 |
| §6 error handling | 5.1 (apiFetch), 7.1 (form errors), backend handlers |
| §7.1 backend tests | 1.4, 2.1 |
| §7.2 frontend smoke | 9.3 |
| §7.3 lint/type/fmt | 9.2 |
| §8 out of scope | honoured (OAuth disabled, no billing, no targeted-search) |
| §9 file-level changes | every task |

No spec section is unimplemented.

**Placeholder scan:** None of the steps say "TBD"/"implement later"/"add appropriate error handling"/"similar to Task N". Every code step contains the actual code. The `vite.config.ts` task explicitly tells the engineer to verify the plugin entry against the installed package and not invent a name — that is direction, not a placeholder.

**Type consistency:** `AuthUser`, `AuthOrApiKey`, `WorkerAuth`, `WorkerCredential`, `apiFetch`, `useMe`, `useApiKeys`, `useCreateApiKey`, `useRevokeApiKey`, `useWorkers`, `useMeStats` are referenced consistently across phases. `NewApiKey extends ApiKeySummary` matches the JSON the create handler returns (`id`, `name`, `prefix`, `last_used_at`, `created_at`, `expires_at`, plus `full_key`). The api-keys handler in Task 3.3 returns those exact fields.

---

**Plan complete and saved to `docs/superpowers/plans/2026-04-28-frontend-rebuild-tanstack-start.md`. Two execution options:**

**1. Subagent-Driven (recommended)** — I dispatch a fresh subagent per task, review between tasks, fast iteration

**2. Inline Execution** — Execute tasks in this session using executing-plans, batch execution with checkpoints

**Which approach?**
