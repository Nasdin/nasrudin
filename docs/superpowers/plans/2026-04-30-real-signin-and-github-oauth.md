# Real Sign-In Page Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the hardcoded sidebar stats on `/signin` with live values, and add GitHub OAuth on the existing axum-login backend.

**Architecture:** Two surfaces ship together. (1) A new `GET /api/stats/landing` endpoint reads from RocksDB + Postgres with a 60-second in-process cache and is consumed by a TanStack Query hook on the sign-in page. (2) A new `auth_oauth` module on the api crate wraps the `oauth2` crate to implement the GitHub authorization-code flow, persists the GitHub identity on the existing `users` table (via a new migration that adds `github_id`/`github_login` and makes `password_hash` nullable), and reuses the existing axum-login session machinery so OAuth and password users share one session/cookie/identity.

**Tech Stack:** Rust (axum 0.7, axum-login 0.18, sea-orm, sea-orm-migration, oauth2 4.x, reqwest), Postgres, TanStack Start frontend (React 18, TanStack Query 5).

**Spec:** `docs/superpowers/specs/2026-04-30-real-signin-and-github-oauth-design.md`

---

## File Structure

**Backend — Rust**

| Path | Status | Responsibility |
|---|---|---|
| `engine/crates/pg/src/migrator/m20260430_000014_user_oauth_identity.rs` | new | Adds `users.github_id BIGINT NULL UNIQUE`, `users.github_login TEXT NULL`, drops `NOT NULL` on `users.password_hash`. |
| `engine/crates/pg/src/migrator/mod.rs` | modify | Register the new migration. |
| `engine/crates/pg/src/entity/users.rs` | modify | Add `github_id`, `github_login` fields; change `password_hash: String` → `Option<String>`. |
| `engine/crates/pg/src/query/users.rs` | modify | Update `create_user` signature to take `Option<&str>` for password hash; add `find_or_create_from_github`. |
| `engine/crates/pg/src/query/workers.rs` | modify | Add `count_active_workers(threshold)` and `count_distinct_user_ids` helpers used by the stats endpoint. |
| `engine/crates/pg/tests/users_oauth_link.rs` | new | Integration test for `find_or_create_from_github` (3 branches). |
| `engine/crates/pg/tests/workers_query.rs` | modify | Add tests for the two new helpers. |
| `engine/crates/api/Cargo.toml` | modify | Add `oauth2 = "4"` and `cookie = "0.18"` (signed cookie for OAuth state). |
| `engine/crates/api/src/auth.rs` | modify | `AuthUser.password_hash: Option<String>`; `session_auth_hash` falls back to `github_id` bytes when password_hash is None. |
| `engine/crates/api/src/auth_oauth.rs` | new | GitHub OAuth handlers (`start`, `callback`); find-or-create wiring via `query::users::find_or_create_from_github`. |
| `engine/crates/api/src/handlers/stats.rs` | new | `landing` handler + `LandingStatsCache` in-process cache. |
| `engine/crates/api/src/handlers/mod.rs` | modify | Register `pub mod stats;` and `pub mod` (already implicit, just confirm). |
| `engine/crates/api/src/state.rs` | modify | `AppState.oauth_github: Option<OAuthConfig>` and `AppState.landing_stats: Arc<LandingStatsCache>`. |
| `engine/crates/api/src/lib.rs` | modify | Add `pub mod auth_oauth;`. |
| `engine/crates/api/src/main.rs` | modify | Load OAuth env vars; instantiate `LandingStatsCache`; register `/api/stats/landing`, `/api/auth/github/start`, `/api/auth/github/callback`. |
| `engine/crates/api/tests/stats_handler.rs` | new | Integration test for `/api/stats/landing`. |

**Frontend — TypeScript / React**

| Path | Status | Responsibility |
|---|---|---|
| `nasrudin-frontend/src/lib/types.ts` | modify | Add `LandingStats` type. |
| `nasrudin-frontend/src/lib/queries.ts` | modify | Add `useLandingStats()` hook. |
| `nasrudin-frontend/src/routes/signin.tsx` | modify | Replace hardcoded stats with `useLandingStats()` values. |
| `nasrudin-frontend/src/components/auth/AuthForm.tsx` | modify | Replace OAuth grid with single full-width "Continue with GitHub" anchor above the email form; remove the four disabled buttons. |
| `nasrudin-frontend/src/styles/platform.css` | modify | Add `.oauth-primary` style; keep existing `.oauth-btn` for future providers. |

**Config / docs**

| Path | Status | Responsibility |
|---|---|---|
| `.env.example` | modify | Add `GITHUB_OAUTH_CLIENT_ID`, `GITHUB_OAUTH_CLIENT_SECRET`, `GITHUB_OAUTH_REDIRECT_URI`. |
| `deploy/README.md` (or whichever existing deploy doc) | modify | One-paragraph "Register the GitHub OAuth app" snippet. |

---

## Task 1: Schema migration — `users.github_id`, `users.github_login`, nullable `password_hash`

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000014_user_oauth_identity.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Create the migration file**

Write `engine/crates/pg/src/migrator/m20260430_000014_user_oauth_identity.rs`:

```rust
//! Adds OAuth identity columns to `users` and drops the NOT NULL on
//! `password_hash` so OAuth-only accounts can exist without a password.
//!
//! `github_id` is the canonical link key (GitHub's user ID is immutable);
//! `github_login` is stored for display only and may change over time.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        // 1. Add github_id (UNIQUE, NULL).
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .add_column_if_not_exists(
                        ColumnDef::new(Users::GithubId).big_integer().null(),
                    )
                    .to_owned(),
            )
            .await?;

        // 2. Add github_login (TEXT, NULL).
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .add_column_if_not_exists(
                        ColumnDef::new(Users::GithubLogin).text().null(),
                    )
                    .to_owned(),
            )
            .await?;

        // 3. Unique partial index on github_id (multiple NULLs are fine in PG).
        manager
            .create_index(
                Index::create()
                    .name("users_github_id_unique")
                    .table(Users::Table)
                    .col(Users::GithubId)
                    .unique()
                    .to_owned(),
            )
            .await?;

        // 4. Drop NOT NULL on password_hash. SeaQuery's column-modify path is
        //    awkward on Postgres; use raw SQL.
        let stmt = sea_orm::Statement::from_string(
            sea_orm::DatabaseBackend::Postgres,
            "ALTER TABLE users ALTER COLUMN password_hash DROP NOT NULL".to_owned(),
        );
        manager.get_connection().execute(stmt).await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        // Reverse order: re-add NOT NULL first (will fail if any OAuth-only
        // rows exist — that's intentional, the operator must clean up first).
        let stmt = sea_orm::Statement::from_string(
            sea_orm::DatabaseBackend::Postgres,
            "ALTER TABLE users ALTER COLUMN password_hash SET NOT NULL".to_owned(),
        );
        manager.get_connection().execute(stmt).await?;

        manager
            .drop_index(
                Index::drop()
                    .name("users_github_id_unique")
                    .table(Users::Table)
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .drop_column(Users::GithubLogin)
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .drop_column(Users::GithubId)
                    .to_owned(),
            )
            .await?;
        Ok(())
    }
}

#[derive(DeriveIden)]
enum Users {
    Table,
    GithubId,
    GithubLogin,
}
```

- [ ] **Step 2: Register the migration in `mod.rs`**

Edit `engine/crates/pg/src/migrator/mod.rs`. Add the `mod` line at the bottom of the existing list (after `m20260501_000003_research_credits`):

```rust
mod m20260430_000014_user_oauth_identity;
```

And add to the `migrations()` vec, last entry:

```rust
            Box::new(m20260430_000014_user_oauth_identity::Migration),
```

- [ ] **Step 3: Confirm the migration compiles**

Run: `cargo check -p nasrudin-pg`
Expected: builds cleanly.

- [ ] **Step 4: Run the migration against a local DB**

Run: `DATABASE_URL=$DATABASE_URL cargo run -p nasrudin-pg --bin migrate` (or whatever the project's existing migrate command is — check `engine/crates/pg/src/bin/` for the entrypoint).
Expected: migration applies; `psql -c "\d users"` shows `github_id`, `github_login`, and `password_hash` is nullable.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000014_user_oauth_identity.rs \
        engine/crates/pg/src/migrator/mod.rs
git commit -m "$(cat <<'EOF'
pg: migration for OAuth identity columns on users

Adds github_id (BIGINT, UNIQUE NULL) and github_login (TEXT NULL),
drops NOT NULL on password_hash so OAuth-only users can exist.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: Update `users` entity for new columns + nullable password_hash

**Files:**
- Modify: `engine/crates/pg/src/entity/users.rs`

- [ ] **Step 1: Add the new fields and change password_hash type**

Edit `engine/crates/pg/src/entity/users.rs`. Replace the `Model` struct with:

```rust
#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    #[sea_orm(unique)]
    pub email: String,
    #[sea_orm(column_type = "Text")]
    pub password_hash: Option<String>,
    pub display_name: Option<String>,
    pub created_at: DateTimeWithTimeZone,
    pub plan_tier: String,
    pub stripe_customer_id: Option<String>,
    pub stripe_subscription_id: Option<String>,
    pub current_period_end: Option<DateTimeWithTimeZone>,
    pub plan_cycle_start: Option<DateTimeWithTimeZone>,
    pub research_credits: i32,
    pub github_id: Option<i64>,
    pub github_login: Option<String>,
}
```

- [ ] **Step 2: Confirm `cargo check` passes for the pg crate**

Run: `cargo check -p nasrudin-pg`
Expected: builds. SeaORM `ActiveModel` and column enums are auto-derived; no other entity changes needed.

- [ ] **Step 3: Confirm `cargo check` passes for the api crate (will reveal call-site breakage)**

Run: `cargo check -p physics-api`
Expected: **fails** with errors at `engine/crates/api/src/auth.rs` (uses `password_hash: String` not `Option<String>`) and at `engine/crates/pg/src/query/users.rs::create_user` (calls `Set(password_hash.to_owned())` which now needs `Some(...)`). These are fixed in Tasks 3 and 4 — leave the failure for now.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/entity/users.rs
git commit -m "$(cat <<'EOF'
pg: users entity — add github_id/github_login, nullable password_hash

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: Update `query::users::create_user` for nullable password + add `find_or_create_from_github`

**Files:**
- Modify: `engine/crates/pg/src/query/users.rs`

- [ ] **Step 1: Change `create_user` to accept `Option<&str>` for password_hash**

Edit `engine/crates/pg/src/query/users.rs`. Replace `create_user`:

```rust
/// Create a new user account. Pass `None` for `password_hash` to create an
/// OAuth-only user (sign-in flows that lack a password). Returns the inserted
/// model.
pub async fn create_user(
    db: &DatabaseConnection,
    email: &str,
    password_hash: Option<&str>,
    display_name: Option<&str>,
) -> Result<users::Model, DbErr> {
    let model = users::ActiveModel {
        id: Set(Uuid::new_v4()),
        email: Set(email.to_owned()),
        password_hash: Set(password_hash.map(|s| s.to_owned())),
        display_name: Set(display_name.map(|s| s.to_owned())),
        created_at: Set(chrono::Utc::now().into()),
        plan_tier: Set("free".to_owned()),
        stripe_customer_id: Set(None),
        stripe_subscription_id: Set(None),
        current_period_end: Set(None),
        plan_cycle_start: Set(None),
        research_credits: Set(0),
        github_id: Set(None),
        github_login: Set(None),
    };
    model.insert(db).await
}
```

- [ ] **Step 2: Add `find_or_create_from_github`**

Append this function to the same file:

```rust
/// Find or create a user from a verified GitHub OAuth response.
///
/// Resolution order:
/// 1. Match by `github_id` → return existing row, refresh `github_login` and
///    `display_name` if changed.
/// 2. Match by lowercased email and `github_id IS NULL` → link: set
///    `github_id` and `github_login` on that row, return updated row.
/// 3. Else create a new row with `password_hash = NULL`.
///
/// Caller must already have verified that GitHub flagged this email as
/// `primary == true && verified == true`. We do **not** trust unverified
/// emails to identify pre-existing accounts.
pub async fn find_or_create_from_github(
    db: &DatabaseConnection,
    github_id: i64,
    github_login: &str,
    primary_verified_email: &str,
    display_name: Option<&str>,
) -> Result<users::Model, DbErr> {
    let email_norm = primary_verified_email.to_lowercase();

    // 1. Match by github_id.
    if let Some(existing) = users::Entity::find()
        .filter(users::Column::GithubId.eq(github_id))
        .one(db)
        .await?
    {
        let needs_login_update =
            existing.github_login.as_deref() != Some(github_login);
        let needs_name_update = display_name.is_some()
            && existing.display_name.as_deref() != display_name;
        if needs_login_update || needs_name_update {
            let mut active: users::ActiveModel = existing.clone().into();
            if needs_login_update {
                active.github_login = Set(Some(github_login.to_owned()));
            }
            if needs_name_update {
                active.display_name = Set(display_name.map(|s| s.to_owned()));
            }
            return active.update(db).await;
        }
        return Ok(existing);
    }

    // 2. Match by email.
    if let Some(existing) = users::Entity::find()
        .filter(users::Column::Email.eq(&email_norm))
        .one(db)
        .await?
    {
        // Only auto-link when the row has no GitHub identity yet — never
        // overwrite an existing link (would be a hijack vector).
        if existing.github_id.is_none() {
            let mut active: users::ActiveModel = existing.into();
            active.github_id = Set(Some(github_id));
            active.github_login = Set(Some(github_login.to_owned()));
            return active.update(db).await;
        }
        // Email collision but the row already has a different github_id —
        // treat as conflict so the caller surfaces a clear error.
        return Err(DbErr::Custom(format!(
            "email {} is linked to a different github account",
            email_norm
        )));
    }

    // 3. Create new.
    let model = users::ActiveModel {
        id: Set(Uuid::new_v4()),
        email: Set(email_norm),
        password_hash: Set(None),
        display_name: Set(display_name.map(|s| s.to_owned())),
        created_at: Set(chrono::Utc::now().into()),
        plan_tier: Set("free".to_owned()),
        stripe_customer_id: Set(None),
        stripe_subscription_id: Set(None),
        current_period_end: Set(None),
        plan_cycle_start: Set(None),
        research_credits: Set(0),
        github_id: Set(Some(github_id)),
        github_login: Set(Some(github_login.to_owned())),
    };
    model.insert(db).await
}
```

- [ ] **Step 3: Fix any existing call site that passed a `&str` to `create_user`**

Run: `cargo check -p nasrudin-pg`
Look for: errors pointing to call sites of `create_user`.

There is currently one in-tree caller — `engine/crates/pg/tests/api_keys.rs:18`:

```rust
let user = query::users::create_user(&db, &email, "stub-hash", None)
```

Change to:

```rust
let user = query::users::create_user(&db, &email, Some("stub-hash"), None)
```

There is also one caller in `engine/crates/api/src/auth.rs::register` (covered in Task 4).

Run: `cargo check -p nasrudin-pg`
Expected: builds cleanly.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/query/users.rs engine/crates/pg/tests/api_keys.rs
git commit -m "$(cat <<'EOF'
pg: users query — Option password_hash + find_or_create_from_github

create_user takes Option<&str> for password_hash so OAuth flows can pass
None. find_or_create_from_github resolves by github_id, then by verified
email (auto-link), else creates a new OAuth-only row.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: Update `AuthUser` for `Option<String>` password_hash + fix `register` handler

**Files:**
- Modify: `engine/crates/api/src/auth.rs`

- [ ] **Step 1: Change `AuthUser.password_hash` to `Option<String>` and update `session_auth_hash`**

Edit `engine/crates/api/src/auth.rs`. Replace the `AuthUser` struct (lines ~14–27) and its `from_model` impl with:

```rust
#[derive(Debug, Clone, Serialize)]
pub struct AuthUser {
    pub id: Uuid,
    pub email: String,
    #[serde(skip)]
    pub password_hash: Option<String>,
    pub display_name: Option<String>,
    pub created_at: chrono::DateTime<chrono::FixedOffset>,
    pub plan_tier: String,
    pub stripe_customer_id: Option<String>,
    pub stripe_subscription_id: Option<String>,
    pub current_period_end: Option<chrono::DateTime<chrono::FixedOffset>>,
    pub plan_cycle_start: Option<chrono::DateTime<chrono::FixedOffset>>,
    pub github_id: Option<i64>,
    pub github_login: Option<String>,
    /// Stable per-user secret used by axum-login's session_auth_hash.
    /// For password users this is the hash bytes; for OAuth-only users it
    /// is the github_id encoded as 8 big-endian bytes. Never serialised.
    #[serde(skip)]
    pub auth_hash_bytes: Vec<u8>,
}

impl AuthUser {
    fn from_model(m: nasrudin_pg::entity::users::Model) -> Self {
        let auth_hash_bytes = if let Some(ref hash) = m.password_hash {
            hash.as_bytes().to_vec()
        } else if let Some(gid) = m.github_id {
            gid.to_be_bytes().to_vec()
        } else {
            // Defensive: a user with neither password nor github_id should not
            // exist. Use the user's UUID bytes so axum-login still gets a
            // stable, non-empty value.
            m.id.as_bytes().to_vec()
        };
        Self {
            id: m.id,
            email: m.email,
            password_hash: m.password_hash,
            display_name: m.display_name,
            created_at: m.created_at,
            plan_tier: m.plan_tier,
            stripe_customer_id: m.stripe_customer_id,
            stripe_subscription_id: m.stripe_subscription_id,
            current_period_end: m.current_period_end,
            plan_cycle_start: m.plan_cycle_start,
            github_id: m.github_id,
            github_login: m.github_login,
            auth_hash_bytes,
        }
    }
}

impl axum_login::AuthUser for AuthUser {
    type Id = Uuid;

    fn id(&self) -> Uuid {
        self.id
    }

    fn session_auth_hash(&self) -> &[u8] {
        &self.auth_hash_bytes
    }
}
```

- [ ] **Step 2: Update `authenticate` to handle a NULL password_hash**

Same file, in `impl AuthnBackend for Backend`, replace the `authenticate` body:

```rust
    async fn authenticate(
        &self,
        creds: Self::Credentials,
    ) -> Result<Option<Self::User>, Self::Error> {
        let user = nasrudin_pg::query::users::find_by_email(&self.db, &creds.email).await?;

        let Some(user) = user else {
            return Ok(None);
        };

        // OAuth-only users have no password — treat as auth failure rather
        // than panicking. They must use the GitHub button to sign in.
        let Some(stored_hash) = user.password_hash.clone() else {
            return Ok(None);
        };

        // Argon2 verification is CPU-intensive — run on blocking thread.
        let password = creds.password;
        let valid = tokio::task::spawn_blocking(move || {
            password_auth::verify_password(password, &stored_hash).is_ok()
        })
        .await?;

        if valid {
            Ok(Some(AuthUser::from_model(user)))
        } else {
            Ok(None)
        }
    }
```

- [ ] **Step 3: Fix the `register` handler to pass `Some(&hash)` to `create_user`**

Same file, in the `register` function (~line 145), find this call:

```rust
    let user = match nasrudin_pg::query::users::create_user(
        &db,
        &body.email,
        &hash,
        body.display_name.as_deref(),
    )
```

Change `&hash` to `Some(hash.as_str())`:

```rust
    let user = match nasrudin_pg::query::users::create_user(
        &db,
        &body.email,
        Some(hash.as_str()),
        body.display_name.as_deref(),
    )
```

- [ ] **Step 4: Confirm the api crate builds**

Run: `cargo check -p physics-api`
Expected: builds cleanly.

- [ ] **Step 5: Run the existing auth-touching tests**

Run: `cargo test -p physics-api auth_or_apikey worker_auth -- --nocapture`
Expected: passes (these don't exercise password_hash directly but confirm we haven't broken the extractors).

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/auth.rs
git commit -m "$(cat <<'EOF'
api: AuthUser handles Option<password_hash>

session_auth_hash falls back to github_id bytes for OAuth-only users.
authenticate returns Ok(None) when an email matches but the row has no
password (those users must sign in via GitHub).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Tests for `find_or_create_from_github`

**Files:**
- Create: `engine/crates/pg/tests/users_oauth_link.rs`

- [ ] **Step 1: Write the integration test**

Create `engine/crates/pg/tests/users_oauth_link.rs`:

```rust
//! Integration tests for `find_or_create_from_github`.
//! Skipped when DATABASE_URL is unset.

use nasrudin_pg::{PgConfig, connect_and_migrate, query};
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

#[tokio::test]
async fn branch_1_match_by_github_id_updates_login_and_name() {
    let Some(db) = db().await else { return };
    let token = Uuid::new_v4();
    let email = format!("gh-link-1-{token}@example.test");
    let github_id: i64 = (token.as_u128() as i64).abs().wrapping_add(1);

    // Seed.
    let created = query::users::find_or_create_from_github(
        &db, github_id, "octocat", &email, Some("Old Name"),
    )
    .await
    .unwrap();
    assert_eq!(created.github_id, Some(github_id));
    assert_eq!(created.github_login.as_deref(), Some("octocat"));
    assert_eq!(created.display_name.as_deref(), Some("Old Name"));
    assert_eq!(created.password_hash, None);

    // Re-call with renamed login + name.
    let updated = query::users::find_or_create_from_github(
        &db, github_id, "octocat-renamed", &email, Some("New Name"),
    )
    .await
    .unwrap();
    assert_eq!(updated.id, created.id);
    assert_eq!(updated.github_login.as_deref(), Some("octocat-renamed"));
    assert_eq!(updated.display_name.as_deref(), Some("New Name"));

    let _ = query::users::delete_user(&db, created.id).await;
}

#[tokio::test]
async fn branch_2_match_by_email_links_existing_account() {
    let Some(db) = db().await else { return };
    let token = Uuid::new_v4();
    let email = format!("gh-link-2-{token}@example.test");
    let github_id: i64 = (token.as_u128() as i64).abs().wrapping_add(2);

    // Pre-seed: an email/password user with no GitHub link.
    let pw_user =
        query::users::create_user(&db, &email, Some("argon2-stub-hash"), Some("Anya"))
            .await
            .unwrap();
    assert_eq!(pw_user.github_id, None);

    // Sign in with GitHub using the same primary verified email.
    let linked = query::users::find_or_create_from_github(
        &db, github_id, "anya", &email, Some("Anya K"),
    )
    .await
    .unwrap();

    assert_eq!(linked.id, pw_user.id, "must reuse existing row");
    assert_eq!(linked.github_id, Some(github_id));
    assert_eq!(linked.github_login.as_deref(), Some("anya"));
    assert!(linked.password_hash.is_some(), "password_hash must be preserved");

    let _ = query::users::delete_user(&db, pw_user.id).await;
}

#[tokio::test]
async fn branch_3_creates_new_oauth_only_user() {
    let Some(db) = db().await else { return };
    let token = Uuid::new_v4();
    let email = format!("gh-link-3-{token}@example.test");
    let github_id: i64 = (token.as_u128() as i64).abs().wrapping_add(3);

    let created = query::users::find_or_create_from_github(
        &db, github_id, "newcomer", &email, Some("Newcomer"),
    )
    .await
    .unwrap();
    assert_eq!(created.github_id, Some(github_id));
    assert_eq!(created.password_hash, None);
    assert_eq!(created.plan_tier, "free");

    let _ = query::users::delete_user(&db, created.id).await;
}

#[tokio::test]
async fn email_collision_with_different_github_id_errors() {
    let Some(db) = db().await else { return };
    let token = Uuid::new_v4();
    let email = format!("gh-link-4-{token}@example.test");
    let gh1: i64 = (token.as_u128() as i64).abs().wrapping_add(4);
    let gh2: i64 = (token.as_u128() as i64).abs().wrapping_add(5);

    // Existing user already linked to gh1.
    let first = query::users::find_or_create_from_github(
        &db, gh1, "first", &email, None,
    )
    .await
    .unwrap();

    // A different github_id with the same primary email should error.
    let result = query::users::find_or_create_from_github(
        &db, gh2, "second", &email, None,
    )
    .await;
    assert!(result.is_err(), "must refuse to silently re-link");

    let _ = query::users::delete_user(&db, first.id).await;
}
```

- [ ] **Step 2: Run the tests**

Run: `DATABASE_URL=$DATABASE_URL cargo test -p nasrudin-pg --test users_oauth_link -- --test-threads=1`
Expected: all four tests pass. (`--test-threads=1` because they share the live DB.)

- [ ] **Step 3: Commit**

```bash
git add engine/crates/pg/tests/users_oauth_link.rs
git commit -m "$(cat <<'EOF'
pg: tests for find_or_create_from_github (4 branches)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: Worker stats query helpers

**Files:**
- Modify: `engine/crates/pg/src/query/workers.rs`
- Modify: `engine/crates/pg/tests/workers_query.rs`

- [ ] **Step 1: Add `count_active_workers` and `count_distinct_user_ids`**

Append to `engine/crates/pg/src/query/workers.rs`:

```rust
/// Count workers whose `last_seen` is more recent than `now() - threshold`.
/// Used by the public landing-stats endpoint.
pub async fn count_active_workers(
    db: &impl ConnectionTrait,
    threshold: chrono::Duration,
) -> Result<u64> {
    let cutoff = chrono::Utc::now() - threshold;
    let cutoff_offset: chrono::DateTime<chrono::FixedOffset> = cutoff.into();
    let count = workers::Entity::find()
        .filter(workers::Column::LastSeen.gt(cutoff_offset))
        .count(db)
        .await?;
    Ok(count)
}

/// Count distinct user_ids on api_keys rows of kind = 'worker' — i.e. the
/// number of people who have ever registered a worker. Used by the public
/// landing-stats endpoint.
pub async fn count_distinct_contributors(db: &impl ConnectionTrait) -> Result<u64> {
    use sea_orm::FromQueryResult;
    #[derive(FromQueryResult)]
    struct R {
        n: i64,
    }
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "SELECT COUNT(DISTINCT user_id)::bigint AS n \
         FROM api_keys WHERE kind = 'worker' AND user_id IS NOT NULL",
        [],
    );
    let row = R::find_by_statement(stmt).one(db).await?;
    Ok(row.map(|r| r.n).unwrap_or(0).max(0) as u64)
}
```

- [ ] **Step 2: Add tests for the two helpers**

Append to `engine/crates/pg/tests/workers_query.rs`:

```rust
#[tokio::test]
async fn count_active_workers_within_threshold() {
    let Some(db) = db().await else { return };
    let token = uuid::Uuid::new_v4();
    let id = format!("active-test-{token}");

    // Register a fresh worker (last_seen = now).
    nasrudin_pg::query::workers::register(&db, &id, Some("active-test"), None)
        .await
        .unwrap();

    let n = nasrudin_pg::query::workers::count_active_workers(
        &db,
        chrono::Duration::minutes(5),
    )
    .await
    .unwrap();
    assert!(n >= 1, "freshly registered worker should be counted");

    let _ = nasrudin_pg::query::workers::delete(&db, &id).await;
}

#[tokio::test]
async fn count_distinct_contributors_does_not_panic() {
    // Sanity check: returns a number, doesn't error. We don't assert a
    // specific count because other tests share the same database.
    let Some(db) = db().await else { return };
    let _n = nasrudin_pg::query::workers::count_distinct_contributors(&db)
        .await
        .unwrap();
}
```

If `db()` is not already defined at the top of `workers_query.rs`, add the same helper used in the api_keys tests:

```rust
async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(nasrudin_pg::connect_and_migrate(&nasrudin_pg::PgConfig::new(&url)).await.unwrap())
}
```

- [ ] **Step 3: Run the tests**

Run: `DATABASE_URL=$DATABASE_URL cargo test -p nasrudin-pg --test workers_query -- --test-threads=1`
Expected: passes.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/query/workers.rs engine/crates/pg/tests/workers_query.rs
git commit -m "$(cat <<'EOF'
pg: workers query — count_active_workers + count_distinct_contributors

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Landing-stats endpoint with 60s in-process cache

**Files:**
- Create: `engine/crates/api/src/handlers/stats.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs`
- Modify: `engine/crates/api/src/state.rs`
- Modify: `engine/crates/api/src/main.rs`
- Create: `engine/crates/api/tests/stats_handler.rs`

- [ ] **Step 1: Add the cache type and handler**

Create `engine/crates/api/src/handlers/stats.rs`:

```rust
//! Public landing-page stats. 60-second in-process cache, no auth.
//!
//! Drives the sign-in page sidebar. Returns three numbers — total verified
//! theorems (RocksDB stats), workers heartbeating in the last 5 minutes
//! (PG), and distinct contributors (PG). On any source error we return the
//! stale cached value if we have one, else zeros.

use std::sync::Arc;
use std::time::{Duration, Instant};

use axum::{Json, extract::State};
use serde::Serialize;
use tokio::sync::RwLock;

use crate::state::AppState;

const CACHE_TTL: Duration = Duration::from_secs(60);
const ACTIVE_WINDOW: chrono::Duration = chrono::Duration::minutes(5);

#[derive(Clone, Debug, Serialize)]
pub struct LandingStats {
    pub verified_theorems: u64,
    pub active_workers: u64,
    pub contributors: u64,
}

impl LandingStats {
    pub fn zero() -> Self {
        Self {
            verified_theorems: 0,
            active_workers: 0,
            contributors: 0,
        }
    }
}

#[derive(Default)]
pub struct LandingStatsCache {
    inner: RwLock<Option<(Instant, LandingStats)>>,
}

impl LandingStatsCache {
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(None),
        }
    }

    /// Returns the cached value if younger than `CACHE_TTL`, else None.
    async fn get_fresh(&self) -> Option<LandingStats> {
        let guard = self.inner.read().await;
        if let Some((ts, ref stats)) = *guard {
            if ts.elapsed() < CACHE_TTL {
                return Some(stats.clone());
            }
        }
        None
    }

    async fn store(&self, stats: LandingStats) {
        *self.inner.write().await = Some((Instant::now(), stats));
    }

    /// Returns the cached value regardless of age (used as a fallback when
    /// recomputation fails).
    async fn get_stale(&self) -> Option<LandingStats> {
        self.inner.read().await.as_ref().map(|(_, s)| s.clone())
    }
}

/// `GET /api/stats/landing` — public, 60s cached.
pub async fn landing(State(state): State<Arc<AppState>>) -> Json<LandingStats> {
    if let Some(fresh) = state.landing_stats.get_fresh().await {
        return Json(fresh);
    }

    let stats = compute(&state).await.unwrap_or_else(|e| {
        tracing::warn!(error = %e, "landing stats: compute failed; returning stale or zeros");
        // Best-effort fallback: stale cache > zeros.
        // Return is sync; we'll resolve the stale value below in the caller path.
        LandingStats::zero()
    });

    // If compute returned zeros and we have a stale value, prefer the stale value.
    let to_return = if stats.verified_theorems == 0
        && stats.active_workers == 0
        && stats.contributors == 0
    {
        state.landing_stats.get_stale().await.unwrap_or(stats)
    } else {
        stats.clone()
    };

    state.landing_stats.store(to_return.clone()).await;
    Json(to_return)
}

async fn compute(state: &Arc<AppState>) -> anyhow::Result<LandingStats> {
    let verified_theorems = state
        .db
        .get_stats()
        .map(|s| s.total_theorems)
        .unwrap_or(0);

    let (active_workers, contributors) = if let Some(ref pg) = state.pg {
        let active =
            nasrudin_pg::query::workers::count_active_workers(pg, ACTIVE_WINDOW).await?;
        let contrib = nasrudin_pg::query::workers::count_distinct_contributors(pg).await?;
        (active, contrib)
    } else {
        (0, 0)
    };

    Ok(LandingStats {
        verified_theorems,
        active_workers,
        contributors,
    })
}
```

- [ ] **Step 2: Register the new handler module**

Edit `engine/crates/api/src/handlers/mod.rs`. Add (alphabetically with the rest):

```rust
pub mod stats;
```

- [ ] **Step 3: Add the cache to `AppState`**

Edit `engine/crates/api/src/state.rs`. Add the import at the top of the imports block:

```rust
use crate::handlers::stats::LandingStatsCache;
```

Then add a field to the `AppState` struct (place it next to `seed_cache` for visual grouping):

```rust
    /// 60-second cache backing `GET /api/stats/landing`.
    pub landing_stats: Arc<LandingStatsCache>,
```

- [ ] **Step 4: Construct the cache in `main.rs`**

Edit `engine/crates/api/src/main.rs`. In the `AppState { … }` literal (~line 377), add (next to `seed_cache`):

```rust
        landing_stats: Arc::new(physics_api::handlers::stats::LandingStatsCache::new()),
```

- [ ] **Step 5: Register the route in `main.rs`**

Edit `engine/crates/api/src/main.rs`. In the `health` router block (~line 622) add the new route inside the same `Router::new()`:

```rust
    let health = Router::new()
        .route("/api/health", get(self::health))
        .route("/api/stats", get(stats))
        .route("/api/stats/landing", get(handlers::stats::landing))
        .route("/metrics", get(physics_api::metrics::metrics))
        .layer(GovernorLayer::new(rate_limit::health_relaxed()));
```

The endpoint shares the health-relaxed bucket (120 req/min, burst 30) since it's a public read served from cache.

- [ ] **Step 6: Confirm api crate builds**

Run: `cargo check -p physics-api`
Expected: builds cleanly.

- [ ] **Step 7: Write the integration test**

Create `engine/crates/api/tests/stats_handler.rs`:

```rust
//! Smoke test for /api/stats/landing.
//!
//! Requires DATABASE_URL + a writable RocksDB temp dir. Skips otherwise.

use std::sync::Arc;

use axum::{Router, body::Body, http::Request, routing::get};
use tower::util::ServiceExt;

#[tokio::test]
async fn landing_returns_expected_shape() {
    let Some(state) = test_state().await else { return };

    let app: Router = Router::new()
        .route(
            "/api/stats/landing",
            get(physics_api::handlers::stats::landing),
        )
        .with_state(Arc::clone(&state));

    let req = Request::builder()
        .uri("/api/stats/landing")
        .body(Body::empty())
        .unwrap();
    let resp = app.oneshot(req).await.unwrap();
    assert_eq!(resp.status(), 200);

    let body = axum::body::to_bytes(resp.into_body(), 1 << 16)
        .await
        .unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
    assert!(v.get("verified_theorems").and_then(|n| n.as_u64()).is_some());
    assert!(v.get("active_workers").and_then(|n| n.as_u64()).is_some());
    assert!(v.get("contributors").and_then(|n| n.as_u64()).is_some());
}

#[tokio::test]
async fn landing_cache_returns_same_bytes_within_ttl() {
    let Some(state) = test_state().await else { return };

    let app: Router = Router::new()
        .route(
            "/api/stats/landing",
            get(physics_api::handlers::stats::landing),
        )
        .with_state(Arc::clone(&state));

    let one = hit(&app).await;
    let two = hit(&app).await;
    assert_eq!(one, two, "second call within 60s must be a cache hit");
}

async fn hit(app: &Router) -> Vec<u8> {
    let req = Request::builder()
        .uri("/api/stats/landing")
        .body(Body::empty())
        .unwrap();
    let resp = app.clone().oneshot(req).await.unwrap();
    axum::body::to_bytes(resp.into_body(), 1 << 16)
        .await
        .unwrap()
        .to_vec()
}

async fn test_state() -> Option<Arc<physics_api::state::AppState>> {
    // Reuse the existing test_app harness if one exists; otherwise the test
    // skips. The api crate already has helpers under tests/test_app — read
    // tests/test_app/mod.rs and call the canonical builder. This test file
    // depends on that helper exposing a function returning Arc<AppState>.
    physics_api::test_app::try_build_test_state().await
}
```

> **Note for the implementer:** the api crate already has a `tests/test_app/` directory used by other handler tests (e.g. `me_stats.rs`, `seed_handler.rs`). Read `tests/test_app/mod.rs` first; if it doesn't expose `try_build_test_state` returning `Option<Arc<AppState>>`, add a public helper there that constructs a minimal AppState (PG from `DATABASE_URL`, RocksDB in a `tempfile::tempdir()`, all other Optional fields = None) and returns `None` if `DATABASE_URL` is unset. Match the patterns used by the existing test files exactly — do not invent a new harness.

- [ ] **Step 8: Run the tests**

Run: `DATABASE_URL=$DATABASE_URL cargo test -p physics-api --test stats_handler -- --test-threads=1`
Expected: both tests pass when DATABASE_URL is set, or both no-op when it isn't.

- [ ] **Step 9: Commit**

```bash
git add engine/crates/api/src/handlers/stats.rs \
        engine/crates/api/src/handlers/mod.rs \
        engine/crates/api/src/state.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/stats_handler.rs
git commit -m "$(cat <<'EOF'
api: GET /api/stats/landing — public 60s-cached landing stats

Reads total theorems from RocksDB and active-worker / contributor counts
from PG. Falls back to stale cached value (or zeros) on compute error.
Wired under the health-relaxed rate-limit bucket.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8: OAuth config plumbing

**Files:**
- Modify: `engine/crates/api/Cargo.toml`
- Modify: `engine/crates/api/src/state.rs`
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/api/src/lib.rs`

- [ ] **Step 1: Add the `oauth2` dependency**

Edit `engine/crates/api/Cargo.toml`. Under `[dependencies]`, add:

```toml
oauth2 = { version = "4", default-features = false, features = ["reqwest", "rustls-tls"] }
```

- [ ] **Step 2: Add `OAuthConfig` to `state.rs`**

Edit `engine/crates/api/src/state.rs`. Add the type and a field on `AppState`:

```rust
/// GitHub OAuth credentials. `None` when any of the three env vars is
/// unset — the start/callback handlers return 503 in that case so the
/// rest of the API works without GitHub configured.
#[derive(Clone)]
pub struct GithubOAuthConfig {
    pub client_id: String,
    pub client_secret: String,
    pub redirect_uri: String,
}

impl GithubOAuthConfig {
    pub fn from_env() -> Option<Self> {
        let client_id = std::env::var("GITHUB_OAUTH_CLIENT_ID").ok().filter(|s| !s.is_empty())?;
        let client_secret = std::env::var("GITHUB_OAUTH_CLIENT_SECRET").ok().filter(|s| !s.is_empty())?;
        let redirect_uri = std::env::var("GITHUB_OAUTH_REDIRECT_URI").ok().filter(|s| !s.is_empty())?;
        Some(Self { client_id, client_secret, redirect_uri })
    }
}
```

Then add to `AppState`:

```rust
    /// GitHub OAuth config — `None` disables the GitHub sign-in routes.
    pub oauth_github: Option<GithubOAuthConfig>,
```

- [ ] **Step 3: Add the `auth_oauth` module to lib.rs**

Edit `engine/crates/api/src/lib.rs`. Add (next to `pub mod auth;`):

```rust
pub mod auth_oauth;
```

- [ ] **Step 4: Wire the config in `main.rs`**

Edit `engine/crates/api/src/main.rs`. After the `admin_token` block (~line 141) add:

```rust
    let oauth_github = physics_api::state::GithubOAuthConfig::from_env();
    if oauth_github.is_some() {
        tracing::info!("GitHub OAuth configured");
    } else {
        tracing::info!(
            "GITHUB_OAUTH_* env vars unset — /api/auth/github/* returns 503"
        );
    }
```

In the `AppState { … }` literal, add:

```rust
        oauth_github,
```

- [ ] **Step 5: Confirm everything compiles** (the `auth_oauth` module is empty for now — we'll fill it in next)

Create a stub `engine/crates/api/src/auth_oauth.rs`:

```rust
//! GitHub OAuth handlers. See spec at
//! docs/superpowers/specs/2026-04-30-real-signin-and-github-oauth-design.md
```

Run: `cargo check -p physics-api`
Expected: builds cleanly.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/Cargo.toml \
        engine/crates/api/src/state.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/src/lib.rs \
        engine/crates/api/src/auth_oauth.rs
git commit -m "$(cat <<'EOF'
api: scaffold for GitHub OAuth (config + module + dep)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: GitHub OAuth `start` handler

**Files:**
- Modify: `engine/crates/api/src/auth_oauth.rs`

- [ ] **Step 1: Implement `start`**

Replace the contents of `engine/crates/api/src/auth_oauth.rs` with:

```rust
//! GitHub OAuth handlers — authorization-code flow on top of axum-login.
//!
//! Two endpoints:
//!   - `GET /api/auth/github/start`    — issue state, redirect to github.com
//!   - `GET /api/auth/github/callback` — verify state, exchange code, sign in
//!
//! Both return 503 when `oauth_github` is unconfigured. State is stored
//! in a 5-minute signed cookie, not server-side, so dev restarts don't
//! break in-flight flows. The cookie is HttpOnly + SameSite=Lax + Secure
//! when behind TLS (toggled via the `OAUTH_COOKIE_SECURE` env var; default
//! true in production-like deployments).

use std::sync::Arc;

use axum::{
    Json,
    extract::State,
    http::{StatusCode, header},
    response::{IntoResponse, Redirect, Response},
};
use axum_extra::extract::cookie::{Cookie, CookieJar, SameSite};
use oauth2::{
    AuthUrl, ClientId, ClientSecret, CsrfToken, RedirectUrl, Scope, TokenUrl,
    basic::BasicClient,
};
use rand::RngCore;

use crate::state::{AppState, GithubOAuthConfig};

const STATE_COOKIE: &str = "github_oauth_state";
const STATE_TTL_SECS: i64 = 300;

fn cookie_secure() -> bool {
    std::env::var("OAUTH_COOKIE_SECURE")
        .map(|v| !matches!(v.trim(), "0" | "false" | "no"))
        .unwrap_or(true)
}

fn oauth_unconfigured() -> Response {
    (
        StatusCode::SERVICE_UNAVAILABLE,
        Json(serde_json::json!({ "error": "oauth_not_configured" })),
    )
        .into_response()
}

fn build_client(cfg: &GithubOAuthConfig) -> BasicClient {
    BasicClient::new(
        ClientId::new(cfg.client_id.clone()),
        Some(ClientSecret::new(cfg.client_secret.clone())),
        AuthUrl::new("https://github.com/login/oauth/authorize".into())
            .expect("valid authorize url"),
        Some(
            TokenUrl::new("https://github.com/login/oauth/access_token".into())
                .expect("valid token url"),
        ),
    )
    .set_redirect_uri(
        RedirectUrl::new(cfg.redirect_uri.clone()).expect("valid redirect url"),
    )
}

/// `GET /api/auth/github/start` — sets a state cookie and 302s to GitHub.
pub async fn start(
    State(state): State<Arc<AppState>>,
    jar: CookieJar,
) -> Response {
    let Some(ref cfg) = state.oauth_github else {
        return oauth_unconfigured();
    };

    let client = build_client(cfg);

    // Generate state and a fresh authorize URL.
    let mut state_bytes = [0u8; 32];
    rand::thread_rng().fill_bytes(&mut state_bytes);
    let state_value = data_encoding::BASE64URL_NOPAD.encode(&state_bytes);

    let (auth_url, _csrf) = client
        .authorize_url(|| CsrfToken::new(state_value.clone()))
        .add_scope(Scope::new("read:user".into()))
        .add_scope(Scope::new("user:email".into()))
        .url();

    let cookie = Cookie::build((STATE_COOKIE, state_value))
        .http_only(true)
        .same_site(SameSite::Lax)
        .secure(cookie_secure())
        .path("/")
        .max_age(time::Duration::seconds(STATE_TTL_SECS))
        .build();

    let jar = jar.add(cookie);

    (jar, Redirect::temporary(auth_url.as_ref())).into_response()
}
```

> **Implementer notes:**
> - The `axum-extra` crate is already a workspace dep (`engine/crates/api/Cargo.toml` line 41). Verify `cookie` feature is enabled — if not, add `axum-extra = { workspace = true, features = ["cookie"] }` here, or to the workspace Cargo.toml if there is one defining feature lists.
> - The `time` crate ships transitively via `cookie`; if compilation fails, add `time = "0.3"` as a direct dep on the api crate.
> - `data-encoding` is already a workspace dep (line 63 of api Cargo.toml).

- [ ] **Step 2: Confirm api crate builds**

Run: `cargo check -p physics-api`
Expected: builds. If `axum-extra` cookie feature is missing, add it as documented above and re-run.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/auth_oauth.rs engine/crates/api/Cargo.toml
git commit -m "$(cat <<'EOF'
api: GitHub OAuth start handler

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 10: GitHub OAuth `callback` handler — exchange code, fetch user, sign in

**Files:**
- Modify: `engine/crates/api/src/auth_oauth.rs`

- [ ] **Step 1: Implement `callback`**

Append to `engine/crates/api/src/auth_oauth.rs`:

```rust
use axum::extract::Query;
use oauth2::{AuthorizationCode, TokenResponse, reqwest::async_http_client};
use serde::Deserialize;

use crate::auth::{AuthSess, AuthUser};

#[derive(Deserialize)]
pub struct CallbackParams {
    pub code: String,
    pub state: String,
}

#[derive(Deserialize)]
struct GithubUser {
    id: i64,
    login: String,
    name: Option<String>,
}

#[derive(Deserialize)]
struct GithubEmail {
    email: String,
    primary: bool,
    verified: bool,
}

/// `GET /api/auth/github/callback` — verify state, exchange the code for a
/// token, fetch the user's primary verified email, find-or-create the user,
/// log them in, redirect to /profile.
pub async fn callback(
    State(state): State<Arc<AppState>>,
    mut auth_session: AuthSess,
    jar: CookieJar,
    Query(params): Query<CallbackParams>,
) -> Response {
    let Some(ref cfg) = state.oauth_github else {
        return oauth_unconfigured();
    };

    // 1. State check.
    let cookie_state = match jar.get(STATE_COOKIE).map(|c| c.value().to_owned()) {
        Some(v) => v,
        None => return bad_request("missing oauth state cookie"),
    };
    if cookie_state != params.state {
        return bad_request("oauth state mismatch");
    }
    // Always clear the cookie after one use.
    let jar = jar.remove(Cookie::from(STATE_COOKIE));

    // 2. Exchange code → token.
    let client = build_client(cfg);
    let token = match client
        .exchange_code(AuthorizationCode::new(params.code))
        .request_async(async_http_client)
        .await
    {
        Ok(t) => t,
        Err(e) => {
            tracing::warn!(error = %e, "github code exchange failed");
            return upstream_error("code_exchange_failed");
        }
    };
    let access_token = token.access_token().secret();

    // 3. Fetch user identity.
    let http = reqwest::Client::builder()
        .user_agent("nasrudin-api")
        .build()
        .expect("reqwest client");

    let gh_user: GithubUser = match http
        .get("https://api.github.com/user")
        .bearer_auth(access_token)
        .header(header::ACCEPT, "application/vnd.github+json")
        .send()
        .await
        .and_then(|r| r.error_for_status())
    {
        Ok(r) => match r.json().await {
            Ok(u) => u,
            Err(e) => {
                tracing::warn!(error = %e, "github user json parse failed");
                return upstream_error("user_parse_failed");
            }
        },
        Err(e) => {
            tracing::warn!(error = %e, "github user fetch failed");
            return upstream_error("user_fetch_failed");
        }
    };

    // 4. Fetch emails — pick primary && verified.
    let emails: Vec<GithubEmail> = match http
        .get("https://api.github.com/user/emails")
        .bearer_auth(access_token)
        .header(header::ACCEPT, "application/vnd.github+json")
        .send()
        .await
        .and_then(|r| r.error_for_status())
    {
        Ok(r) => r.json().await.unwrap_or_default(),
        Err(e) => {
            tracing::warn!(error = %e, "github emails fetch failed");
            return upstream_error("emails_fetch_failed");
        }
    };

    let primary = match emails.iter().find(|e| e.primary && e.verified) {
        Some(p) => p,
        None => return upstream_error("no_verified_primary_email"),
    };

    // 5. Find-or-create.
    let pg = match auth_session.backend.db.clone() {
        db => db,
    };
    let user_model = match nasrudin_pg::query::users::find_or_create_from_github(
        &pg,
        gh_user.id,
        &gh_user.login,
        &primary.email,
        gh_user.name.as_deref(),
    )
    .await
    {
        Ok(m) => m,
        Err(e) => {
            tracing::warn!(error = %e, "find_or_create_from_github failed");
            return conflict_error("github_link_conflict");
        }
    };

    let auth_user = AuthUser::from_model(user_model);

    // 6. Sign in via axum-login.
    if let Err(e) = auth_session.login(&auth_user).await {
        tracing::error!(error = %e, "axum-login session create failed");
        return upstream_error("session_create_failed");
    }

    // 7. Redirect to /profile.
    (jar, Redirect::temporary("/profile")).into_response()
}

fn bad_request(msg: &str) -> Response {
    (
        StatusCode::BAD_REQUEST,
        Json(serde_json::json!({ "error": msg })),
    )
        .into_response()
}

fn upstream_error(msg: &str) -> Response {
    (
        StatusCode::BAD_GATEWAY,
        Json(serde_json::json!({ "error": msg })),
    )
        .into_response()
}

fn conflict_error(msg: &str) -> Response {
    (
        StatusCode::CONFLICT,
        Json(serde_json::json!({ "error": msg })),
    )
        .into_response()
}
```

> **Implementer note:** The pattern `let pg = match auth_session.backend.db.clone() { db => db };` is intentional: it clones the `DatabaseConnection` out of the `AuthSession` so we can pass `&pg` to the query layer without holding a borrow that would conflict with `auth_session.login()` later. Replace with `let pg = auth_session.backend.db.clone();` if the simpler form works (it should).

- [ ] **Step 2: Confirm api crate builds**

Run: `cargo check -p physics-api`
Expected: builds cleanly.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/auth_oauth.rs
git commit -m "$(cat <<'EOF'
api: GitHub OAuth callback — code exchange, email fetch, find-or-create

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11: Wire OAuth routes into the router

**Files:**
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Register `/api/auth/github/start` and `/callback`**

Edit `engine/crates/api/src/main.rs`. In the `if let Some(ref pg_conn) = state.pg { … }` block where auth routes are registered (~line 680), find the `auth_strict` Router and add the OAuth routes there:

```rust
        let auth_strict = Router::new()
            .route("/api/auth/register", axum::routing::post(auth::register))
            .route("/api/auth/login", axum::routing::post(auth::login))
            .route(
                "/api/auth/github/start",
                get(physics_api::auth_oauth::start),
            )
            .route(
                "/api/auth/github/callback",
                get(physics_api::auth_oauth::callback),
            )
            .layer(GovernorLayer::new(rate_limit::auth_strict()));
```

The OAuth routes share the auth-strict bucket (5 req/min, burst 5) — same threat model as login attempts.

- [ ] **Step 2: Confirm everything builds**

Run: `cargo check -p physics-api`
Expected: builds cleanly.

- [ ] **Step 3: Run existing auth tests to confirm no regression**

Run: `cargo test -p physics-api auth_or_apikey worker_auth -- --nocapture`
Expected: passes.

- [ ] **Step 4: Manual smoke test (optional, requires GitHub OAuth app)**

If you have a registered GitHub OAuth app:

```bash
export GITHUB_OAUTH_CLIENT_ID=...
export GITHUB_OAUTH_CLIENT_SECRET=...
export GITHUB_OAUTH_REDIRECT_URI=http://localhost:3001/api/auth/github/callback
DATABASE_URL=$DATABASE_URL OAUTH_COOKIE_SECURE=false cargo run -p physics-api --bin physics-api
```

Open http://localhost:3001/api/auth/github/start in a browser → should redirect to GitHub → after consent, lands on `http://localhost:3001/profile` (which 404s for now since the frontend isn't running, but `GET /api/auth/me` should now return the user).

```bash
curl -b cookies.txt -c cookies.txt http://localhost:3001/api/auth/github/start -L
curl -b cookies.txt http://localhost:3001/api/auth/me
```

If the GitHub app isn't registered, skip this step — it's covered by the frontend manual test in Task 14.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/main.rs
git commit -m "$(cat <<'EOF'
api: wire GitHub OAuth routes under auth-strict bucket

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12: Frontend — `useLandingStats` hook + signin sidebar wiring

**Files:**
- Modify: `nasrudin-frontend/src/lib/types.ts`
- Modify: `nasrudin-frontend/src/lib/queries.ts`
- Modify: `nasrudin-frontend/src/routes/signin.tsx`

- [ ] **Step 1: Add the `LandingStats` type**

Edit `nasrudin-frontend/src/lib/types.ts`. Add (alphabetically among the exports, or near other public-stat types):

```ts
export interface LandingStats {
  verified_theorems: number;
  active_workers: number;
  contributors: number;
}
```

- [ ] **Step 2: Add the `useLandingStats` hook**

Edit `nasrudin-frontend/src/lib/queries.ts`. Import `LandingStats` at the top:

```ts
import type {
  ApiKeySummary,
  AuthUser,
  // ... existing ...
  LandingStats,
  // ... existing ...
} from './types';
```

Add the hook (alphabetical or near other `useMe*` hooks):

```ts
export function useLandingStats() {
  return useQuery<LandingStats>({
    queryKey: ['stats', 'landing'],
    queryFn: () => apiFetch<LandingStats>('/api/stats/landing'),
    staleTime: 60_000,
    refetchOnWindowFocus: false,
  });
}
```

- [ ] **Step 3: Consume the hook in `signin.tsx`**

Edit `nasrudin-frontend/src/routes/signin.tsx`. Replace the entire `SignInPage` component body:

```tsx
import { createFileRoute, Link } from '@tanstack/react-router';
import { AuthForm } from '~/components/auth/AuthForm';
import { useLandingStats } from '~/lib/queries';

export const Route = createFileRoute('/signin')({ component: SignInPage });

function fmt(n: number | undefined): string {
  if (typeof n !== 'number') return '—';
  return n.toLocaleString('en-US');
}

function SignInPage() {
  const stats = useLandingStats();
  return (
    <div className="auth-page">
      <div className="auth-side">
        <div className="auth-side-pattern" />
        <Link to="/" className="auth-side-brand" style={{ textDecoration: 'none' }}>
          Nasrud
          <span
            style={{
              display: 'inline-block',
              width: 6,
              height: 6,
              borderRadius: '50%',
              background: 'var(--terracotta-500)',
              transform: 'translateY(-2px)',
              margin: '0 1px',
            }}
          />
          in
        </Link>
        <div>
          <div className="auth-side-quote">
            "Once, looking for a lost key under a lamppost, Nasrudin was asked why he searched
            there. <em>Because the light is better here.</em>"
          </div>
          <div className="auth-side-attr">— a Sufi parable</div>
        </div>
        <div className="auth-stat-row">
          <div className="auth-stat">
            <div className="num">{fmt(stats.data?.verified_theorems)}</div>
            <div className="lbl">Verified theorems</div>
          </div>
          <div className="auth-stat">
            <div className="num">{fmt(stats.data?.active_workers)}</div>
            <div className="lbl">Workers · live</div>
          </div>
          <div className="auth-stat">
            <div className="num">{fmt(stats.data?.contributors)}</div>
            <div className="lbl">Contributors</div>
          </div>
        </div>
      </div>
      <AuthForm />
    </div>
  );
}
```

- [ ] **Step 4: Type-check the frontend**

Run: `pnpm -C nasrudin-frontend exec tsc --noEmit`
Expected: no errors.

- [ ] **Step 5: Commit**

```bash
git add nasrudin-frontend/src/lib/types.ts \
        nasrudin-frontend/src/lib/queries.ts \
        nasrudin-frontend/src/routes/signin.tsx
git commit -m "$(cat <<'EOF'
frontend: live landing stats on /signin sidebar

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 13: Frontend — replace OAuth grid with single full-width "Continue with GitHub"

**Files:**
- Modify: `nasrudin-frontend/src/components/auth/AuthForm.tsx`
- Modify: `nasrudin-frontend/src/styles/platform.css`

- [ ] **Step 1: Add CSS for the primary OAuth button**

Edit `nasrudin-frontend/src/styles/platform.css`. After the existing `.oauth-btn` block (~line 1320), add:

```css
.oauth-primary {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 10px;
  width: 100%;
  padding: 12px 16px;
  border-radius: 10px;
  border: 1px solid var(--ink-200);
  background: var(--ink-900);
  color: var(--paper-50);
  font-size: 15px;
  font-weight: 500;
  text-decoration: none;
  transition: background 120ms ease;
}
.oauth-primary:hover { background: var(--ink-800); }
.oauth-primary svg { width: 18px; height: 18px; fill: currentColor; }
```

(If `--ink-800` does not exist as a CSS variable, swap for the closest existing token by reading the top of `platform.css` for the variable definitions.)

- [ ] **Step 2: Rewrite `AuthForm.tsx` OAuth section**

Edit `nasrudin-frontend/src/components/auth/AuthForm.tsx`. Replace the entire return statement with:

```tsx
  return (
    <form className="auth-form-wrap" onSubmit={onSubmit}>
      <h1>{tab === 'signin' ? 'Welcome back.' : 'Join the corpus.'}</h1>
      <p className="lede">
        {tab === 'signin'
          ? 'Sign in to your library, citations, and targeted searches.'
          : 'Free for individual academics. No card required.'}
      </p>

      <a href="/api/auth/github/start" className="oauth-primary">
        <svg viewBox="0 0 24 24" aria-hidden="true">
          <path d="M12 .3a12 12 0 0 0-3.79 23.4c.6.11.82-.26.82-.58v-2.05c-3.34.73-4.04-1.61-4.04-1.61-.55-1.39-1.34-1.76-1.34-1.76-1.09-.74.08-.73.08-.73 1.21.09 1.85 1.24 1.85 1.24 1.07 1.84 2.81 1.31 3.5 1 .11-.78.42-1.31.76-1.61-2.66-.3-5.46-1.33-5.46-5.93 0-1.31.47-2.38 1.24-3.22-.13-.3-.54-1.52.11-3.18 0 0 1-.32 3.3 1.23a11.5 11.5 0 0 1 6 0c2.3-1.55 3.3-1.23 3.3-1.23.65 1.66.24 2.88.12 3.18.77.84 1.24 1.91 1.24 3.22 0 4.61-2.81 5.62-5.49 5.92.43.37.81 1.1.81 2.22v3.29c0 .32.22.7.83.58A12 12 0 0 0 12 .3" />
        </svg>
        Continue with GitHub
      </a>

      <div className="divider">or</div>

      <div className="auth-tabs">
        <button
          type="button"
          className={`auth-tab ${tab === 'signin' ? 'active' : ''}`}
          onClick={() => setTab('signin')}
        >
          Sign in
        </button>
        <button
          type="button"
          className={`auth-tab ${tab === 'signup' ? 'active' : ''}`}
          onClick={() => setTab('signup')}
        >
          Create account
        </button>
      </div>
      {tab === 'signup' && (
        <div className="field">
          <label htmlFor="name">Full name</label>
          <input
            id="name"
            type="text"
            value={name}
            onChange={(e) => setName(e.target.value)}
            placeholder="Anya Klint"
          />
        </div>
      )}
      <div className="field">
        <label htmlFor="email">Academic email</label>
        <input
          id="email"
          type="email"
          required
          autoComplete="email"
          value={email}
          onChange={(e) => setEmail(e.target.value)}
          placeholder="you@university.edu"
        />
      </div>
      <div className="field">
        <label htmlFor="password">Password</label>
        <input
          id="password"
          type="password"
          required
          autoComplete="current-password"
          minLength={8}
          value={password}
          onChange={(e) => setPassword(e.target.value)}
          placeholder="••••••••••••"
        />
      </div>
      {error && (
        <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginBottom: 12 }}>
          {error}
        </div>
      )}
      <button
        className="btn btn-primary"
        type="submit"
        disabled={submitting}
        style={{ width: '100%', justifyContent: 'center', marginTop: 8 }}
      >
        {tab === 'signin'
          ? submitting
            ? 'Signing in…'
            : 'Sign in'
          : submitting
            ? 'Creating…'
            : 'Create free account'}
      </button>

      <p
        style={{
          marginTop: 32,
          fontSize: 12,
          color: 'var(--ink-500)',
          textAlign: 'center',
        }}
      >
        By continuing you agree to our terms and privacy. The corpus is free to read; we never sell
        your queries.
      </p>
    </form>
  );
```

The disabled `.oauth-grid` and its four "Coming soon" buttons are gone. The `.divider` element is now between the GitHub button and the email/password tabs. All state hooks at the top of the component are unchanged.

- [ ] **Step 3: Type-check + visual smoke test**

Run: `pnpm -C nasrudin-frontend exec tsc --noEmit`
Expected: no errors.

Run: `pnpm -C nasrudin-frontend dev` and visit `http://localhost:3000/signin`. Visually confirm:
- Sidebar shows three numbers (or `—` if API isn't reachable).
- Sign-in form has a single black "Continue with GitHub" button at the top, then `or`, then the existing email/password tabs.
- No disabled `Coming soon` buttons remain.

If `GITHUB_OAUTH_*` is set on the API, click the GitHub button and walk through the flow to `/profile`.

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/src/components/auth/AuthForm.tsx \
        nasrudin-frontend/src/styles/platform.css
git commit -m "$(cat <<'EOF'
frontend: replace OAuth grid with full-width 'Continue with GitHub'

Removes the four disabled 'Coming soon' OAuth buttons. GitHub OAuth is
now a single primary anchor above the email/password form, linking to
/api/auth/github/start.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 14: Config + deploy docs

**Files:**
- Modify: `.env.example`
- Modify: `deploy/README.md` (or the canonical deploy doc — check `deploy/` for the file currently used)

- [ ] **Step 1: Add the new env vars to `.env.example`**

Edit `.env.example`. Add (group near other auth-related vars; if there is no auth section, add at the bottom under a new `# GitHub OAuth` heading):

```sh
# GitHub OAuth — optional. When unset, /api/auth/github/* returns 503.
# Register an app at https://github.com/settings/developers (OAuth Apps).
# The redirect URI must EXACTLY match what's registered there.
GITHUB_OAUTH_CLIENT_ID=
GITHUB_OAUTH_CLIENT_SECRET=
GITHUB_OAUTH_REDIRECT_URI=http://localhost:3001/api/auth/github/callback

# Set to "false" only for non-TLS local dev. Default is true (production).
OAUTH_COOKIE_SECURE=true
```

- [ ] **Step 2: Add a brief deploy note**

Find the canonical deploy doc:

```bash
ls deploy/
cat deploy/README.md 2>/dev/null | head -30
```

If `deploy/README.md` exists, append a section. Otherwise add to whichever doc covers env-var setup (likely `deploy/Caddyfile.native`'s neighbor or `docs/superpowers/specs/2026-04-28-rediscover-physics-architecture.md`'s deployment section). The note:

```markdown
## GitHub OAuth (sign-in)

To enable the "Continue with GitHub" button on `/signin`, register a GitHub
OAuth app:

1. Visit https://github.com/settings/developers → "New OAuth App".
2. **Application name:** Nasrudin (or per-environment, e.g. "Nasrudin (staging)").
3. **Homepage URL:** `https://nasrudin.app` (or staging URL).
4. **Authorization callback URL:** `https://nasrudin.app/api/auth/github/callback`
   (must match `GITHUB_OAUTH_REDIRECT_URI` exactly — including the scheme).
5. After creation, click "Generate a new client secret".
6. Set in the systemd unit `Environment=` block (or `.env`):
   - `GITHUB_OAUTH_CLIENT_ID=Iv1.…`
   - `GITHUB_OAUTH_CLIENT_SECRET=<the secret>`
   - `GITHUB_OAUTH_REDIRECT_URI=https://nasrudin.app/api/auth/github/callback`

The API logs `GitHub OAuth configured` at startup when all three are set;
otherwise the routes return 503 and the rest of the API works as normal.
```

- [ ] **Step 3: Commit**

```bash
git add .env.example deploy/README.md
git commit -m "$(cat <<'EOF'
docs: GitHub OAuth env vars + deploy note

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Final verification

- [ ] **Build everything**

Run: `cargo build --workspace`
Expected: clean build.

- [ ] **Type-check the frontend**

Run: `pnpm -C nasrudin-frontend exec tsc --noEmit`
Expected: no errors.

- [ ] **Run the new tests**

Run:
```bash
DATABASE_URL=$DATABASE_URL cargo test -p nasrudin-pg --test users_oauth_link --test workers_query -- --test-threads=1
DATABASE_URL=$DATABASE_URL cargo test -p physics-api --test stats_handler -- --test-threads=1
```
Expected: all pass.

- [ ] **Visual + behavioural check**

With API + DB + frontend running locally:

1. Visit `/signin`. Confirm the three sidebar stats reflect real DB values (or `—` if API is down).
2. With `GITHUB_OAUTH_*` set, click "Continue with GitHub". Walk through the full GitHub consent → callback → `/profile` flow with a fresh GitHub account. Confirm `GET /api/auth/me` returns the user with `github_id` populated and `password_hash = null` in the DB.
3. Pre-create an email/password account with email matching a GitHub primary verified email. Sign out. Click GitHub button, complete flow. Confirm the same `users.id` is reused (auto-link by email) and `password_hash` is preserved.
4. Without `GITHUB_OAUTH_*` set, confirm `GET /api/auth/github/start` returns 503 and the email/password form still works.

- [ ] **Push and open PR**

```bash
git push origin <branch>
gh pr create --title "Real sign-in: live stats + GitHub OAuth" --body "..."
```
