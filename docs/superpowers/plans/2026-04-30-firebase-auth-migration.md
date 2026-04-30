# Firebase Auth Migration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace email/password (axum-login + Argon2) and GitHub OAuth with Firebase Auth. Day-1 providers: email/password (Firebase-managed verification + reset) and Google OAuth.

**Architecture:** Firebase owns sign-up, login, password storage, password reset, email verification, Google OAuth. Our backend keeps the `users` table, gains a `firebase_uid` column, and exposes one new endpoint (`POST /api/auth/firebase-session`) that verifies a Firebase ID token (RS256 JWT against Google's JWKs), find-or-creates the user, and issues an axum-login session cookie. Existing `AuthSess`, `AuthOrApiKey`, `WorkerAuth` extractors and every handler that consumes them are untouched.

**Tech Stack:** Rust (axum 0.7, axum-login 0.18, sea-orm, sea-orm-migration, jsonwebtoken 9, reqwest), Postgres, TanStack Start frontend (React 18, TanStack Query 5), Firebase Web SDK 10+, Firebase Auth (Google-hosted).

**Spec:** `docs/superpowers/specs/2026-04-30-firebase-auth-migration-design.md`

---

## File Structure

**Backend — Rust**

| Path | Status | Responsibility |
|---|---|---|
| `engine/crates/pg/src/migrator/m20260430_000016_firebase_auth.rs` | new | Wipes `users`, drops `password_hash`/`github_id`/`github_login`, adds `firebase_uid TEXT NOT NULL UNIQUE`. |
| `engine/crates/pg/src/migrator/mod.rs` | modify | Register new migration. |
| `engine/crates/pg/src/entity/users.rs` | modify | Drop password/github fields; add `firebase_uid`. |
| `engine/crates/pg/src/query/users.rs` | modify | Replace `create_user` with `create_firebase_user`; delete `find_or_create_from_github`. |
| `engine/crates/pg/tests/users_oauth_link.rs` | delete | Tests of deleted `find_or_create_from_github`. |
| `engine/crates/pg/tests/api_keys.rs` | modify | Update `create_user` call site. |
| `engine/crates/pg/tests/conjecture_jobs_query.rs` | modify | Update `create_user` call site. |
| `engine/crates/api/Cargo.toml` | modify | Drop `oauth2`; add `jsonwebtoken`; add `rsa` to dev-dependencies. |
| `engine/crates/api/src/firebase_auth.rs` | new | `FirebaseClaims`, `JwksCache`, `verify_id_token`. |
| `engine/crates/api/src/auth.rs` | modify | Rewrite `AuthUser` (drop password/github, add firebase_uid); replace `register`/`login`/`me` chain with `firebase_session` + `me` + `logout`. |
| `engine/crates/api/src/auth_oauth.rs` | delete | The GitHub OAuth handlers from the previous round. |
| `engine/crates/api/src/state.rs` | modify | Drop `GithubOAuthConfig` + `oauth_github` field. Add `firebase_project_id: Option<String>` and `firebase_jwks: Arc<firebase_auth::JwksCache>`. |
| `engine/crates/api/src/main.rs` | modify | Load `FIREBASE_PROJECT_ID`; build JWKs cache + pre-warm; register `/api/auth/firebase-session`; delete register/login/github routes; remove `OAUTH_COOKIE_SECURE` reading. |
| `engine/crates/api/src/lib.rs` | modify | Remove `auth_oauth` module; add `firebase_auth` module. |
| `engine/crates/api/tests/test_app/mod.rs` | modify | Drop `oauth_github` from AppState construction; add `firebase_project_id` and a test JWKs cache constructor. |
| `engine/crates/api/tests/firebase_verify.rs` | new | Unit-style integration tests for `verify_id_token`. |
| `engine/crates/api/tests/firebase_session.rs` | new | End-to-end test for `POST /api/auth/firebase-session`. |

**Frontend — TypeScript / React**

| Path | Status | Responsibility |
|---|---|---|
| `nasrudin-frontend/package.json` | modify | Add `firebase` dependency. |
| `nasrudin-frontend/src/lib/firebase.ts` | new | Lazy-init Firebase app; wrap SDK calls (`signInWithEmail`, `signUpWithEmail`, `signInWithGoogle`, `sendPasswordReset`, `sendVerificationEmail`, `firebaseSignOut`, `getCurrentIdToken`). |
| `nasrudin-frontend/src/lib/queries.ts` | modify | Replace `useLogin`, `useRegister`, `useLogout`. Add `useGoogleLogin`, `useResetPassword`, `useResendVerification`. |
| `nasrudin-frontend/src/components/auth/AuthForm.tsx` | modify | Full-width "Continue with Google", `or` divider, sign-in/create tabs, "Forgot password?" inline reset, post-signup verification alert. |
| `nasrudin-frontend/src/styles/platform.css` | modify | `.oauth-primary` swaps GitHub mark for Google G mark; minor color tweak. |

**Config / docs**

| Path | Status | Responsibility |
|---|---|---|
| `.env.example` | modify | Remove GitHub OAuth block; add Firebase block (backend `FIREBASE_PROJECT_ID` + frontend `VITE_FIREBASE_*`). |
| `deploy/README.md` | modify | Replace GitHub OAuth section with Firebase setup steps. |

---

## Task 1: Schema migration — wipe users, drop password/github, add firebase_uid

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000016_firebase_auth.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Create the migration file**

Write `engine/crates/pg/src/migrator/m20260430_000016_firebase_auth.rs`:

```rust
//! Migrate `users` to Firebase-shaped identity:
//!   - DELETE all rows (none in production today; cascades to dependents).
//!   - DROP password_hash, github_id, github_login (no longer used).
//!   - ADD firebase_uid TEXT NOT NULL UNIQUE.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();

        // 1. Wipe — there are no production accounts. CASCADE clears every
        //    dependent row (api_keys, workers, saved_searches, etc.).
        conn.execute_unprepared("DELETE FROM users").await?;

        // 2. Drop github_id unique index from m20260430_000014.
        conn.execute_unprepared("DROP INDEX IF EXISTS users_github_id_unique")
            .await?;

        // 3. Drop columns.
        conn.execute_unprepared("ALTER TABLE users DROP COLUMN IF EXISTS password_hash")
            .await?;
        conn.execute_unprepared("ALTER TABLE users DROP COLUMN IF EXISTS github_id")
            .await?;
        conn.execute_unprepared("ALTER TABLE users DROP COLUMN IF EXISTS github_login")
            .await?;

        // 4. Add firebase_uid + unique index.
        conn.execute_unprepared(
            "ALTER TABLE users ADD COLUMN firebase_uid TEXT NOT NULL UNIQUE",
        )
        .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();
        conn.execute_unprepared("ALTER TABLE users DROP COLUMN IF EXISTS firebase_uid")
            .await?;
        // Restore the columns dropped in `up`. Defaults match the original
        // schema; rows can't be reconstructed so password_hash is left NULL.
        conn.execute_unprepared("ALTER TABLE users ADD COLUMN password_hash TEXT")
            .await?;
        conn.execute_unprepared("ALTER TABLE users ADD COLUMN github_id BIGINT")
            .await?;
        conn.execute_unprepared("ALTER TABLE users ADD COLUMN github_login TEXT")
            .await?;
        conn.execute_unprepared(
            "CREATE UNIQUE INDEX users_github_id_unique ON users (github_id)",
        )
        .await?;
        Ok(())
    }
}
```

- [ ] **Step 2: Register the migration in `mod.rs`**

Edit `engine/crates/pg/src/migrator/mod.rs`. Append after the existing `m20260430_000015_library` mod line:

```rust
mod m20260430_000016_firebase_auth;
```

And add the last entry to the `migrations()` vec:

```rust
            Box::new(m20260430_000016_firebase_auth::Migration),
```

- [ ] **Step 3: Confirm pg crate compiles**

Run: `cd engine && cargo check -p nasrudin-pg`
Expected: builds cleanly (the `users` entity still has the old fields — that's intentional, Task 2 fixes it).

- [ ] **Step 4: Apply the migration to the local dev DB**

Run:
```bash
DATABASE_URL="postgresql://physics:physics_dev@localhost:5432/physics_generator" \
  cargo run -p nasrudin-pg --bin migrate
```
Expected: `Migration 'm20260430_000016_firebase_auth' has been applied`.

- [ ] **Step 5: Verify schema changed**

Run:
```bash
PGPASSWORD=physics_dev psql -h localhost -U physics -d physics_generator \
  -c "\d users" | grep -E "firebase|password|github"
```
Expected output contains `firebase_uid | text` and **does not** contain `password_hash`, `github_id`, or `github_login`.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000016_firebase_auth.rs \
        engine/crates/pg/src/migrator/mod.rs
git commit -m "$(cat <<'EOF'
pg: migration to Firebase-shaped users (drop password+github, add firebase_uid)

Wipes the users table (zero production accounts), drops password_hash,
github_id, github_login, adds firebase_uid TEXT NOT NULL UNIQUE.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: Update users entity for Firebase fields

**Files:**
- Modify: `engine/crates/pg/src/entity/users.rs`

- [ ] **Step 1: Replace the entity Model**

Edit `engine/crates/pg/src/entity/users.rs`. Replace the `Model` struct:

```rust
#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    #[sea_orm(unique)]
    pub email: String,
    pub display_name: Option<String>,
    pub created_at: DateTimeWithTimeZone,
    pub plan_tier: String,
    pub stripe_customer_id: Option<String>,
    pub stripe_subscription_id: Option<String>,
    pub current_period_end: Option<DateTimeWithTimeZone>,
    pub plan_cycle_start: Option<DateTimeWithTimeZone>,
    /// $19/mo Researcher tier credit ledger. One credit is debited
    /// when a paid `conjecture_jobs` row is created and refunded on
    /// cancel-before-progress or zero-result `budget_exhausted`.
    pub research_credits: i32,
    /// Firebase UID — the source-of-truth identity link. Stable across
    /// provider linking (e.g. user adds Google to an email/password
    /// account → same UID).
    #[sea_orm(unique)]
    pub firebase_uid: String,
}
```

The `Relation` enum and `Related` impls below are unchanged.

- [ ] **Step 2: Confirm pg crate compiles**

Run: `cd engine && cargo check -p nasrudin-pg`
Expected: **fails** at `query/users.rs::create_user` and `query/users.rs::find_or_create_from_github` because the field set changed. Task 3 fixes them.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/pg/src/entity/users.rs
git commit -m "$(cat <<'EOF'
pg: users entity — drop password_hash/github_*, add firebase_uid

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: Replace `create_user` with `create_firebase_user`; delete `find_or_create_from_github`

**Files:**
- Modify: `engine/crates/pg/src/query/users.rs`
- Delete: `engine/crates/pg/tests/users_oauth_link.rs`
- Modify: `engine/crates/pg/tests/api_keys.rs`
- Modify: `engine/crates/pg/tests/conjecture_jobs_query.rs`

- [ ] **Step 1: Rewrite the head of `query/users.rs`**

Edit `engine/crates/pg/src/query/users.rs`. Replace `create_user` and delete `find_or_create_from_github` entirely. The new file head reads:

```rust
use sea_orm::*;
use uuid::Uuid;

use crate::entity::users;

/// Create a new user backed by a Firebase identity. The caller has already
/// verified the Firebase ID token; `firebase_uid` is the verified `sub`
/// claim. Returns the inserted model.
pub async fn create_firebase_user(
    db: &DatabaseConnection,
    firebase_uid: &str,
    email: &str,
    display_name: Option<&str>,
) -> Result<users::Model, DbErr> {
    let model = users::ActiveModel {
        id: Set(Uuid::new_v4()),
        email: Set(email.to_owned()),
        display_name: Set(display_name.map(|s| s.to_owned())),
        created_at: Set(chrono::Utc::now().into()),
        plan_tier: Set("free".to_owned()),
        stripe_customer_id: Set(None),
        stripe_subscription_id: Set(None),
        current_period_end: Set(None),
        plan_cycle_start: Set(None),
        research_credits: Set(0),
        firebase_uid: Set(firebase_uid.to_owned()),
    };
    model.insert(db).await
}

/// Find a user by Firebase UID. Used by the session-exchange endpoint
/// to decide insert-vs-return.
pub async fn find_by_firebase_uid(
    db: &DatabaseConnection,
    firebase_uid: &str,
) -> Result<Option<users::Model>, DbErr> {
    users::Entity::find()
        .filter(users::Column::FirebaseUid.eq(firebase_uid))
        .one(db)
        .await
}
```

Below those, **keep all the existing functions** unchanged: `set_stripe_customer_id`, `find_by_id`, `find_by_email`, `update_display_name`, `delete_user`, `try_decrement_research_credits`, `refund_research_credit`, `grant_research_credits_on_period_advance`. They reference no removed columns.

The old `create_user` and `find_or_create_from_github` are gone.

- [ ] **Step 2: Delete `users_oauth_link.rs`**

```bash
rm engine/crates/pg/tests/users_oauth_link.rs
```

- [ ] **Step 3: Update `tests/api_keys.rs` call site**

Edit `engine/crates/pg/tests/api_keys.rs`. Find:

```rust
let user = query::users::create_user(&db, &email, Some("stub-hash"), None)
    .await
    .unwrap();
```

Replace with:

```rust
let user = query::users::create_firebase_user(&db, &format!("fb_{}", unique_token.simple()), &email, None)
    .await
    .unwrap();
```

- [ ] **Step 4: Update `tests/conjecture_jobs_query.rs` call site**

Edit `engine/crates/pg/tests/conjecture_jobs_query.rs`. Find:

```rust
let m = u::create_user(db, "owner@test", Some("x"), Some("Owner"))
```

Replace with:

```rust
let m = u::create_firebase_user(db, "fb_owner_test", "owner@test", Some("Owner"))
```

- [ ] **Step 5: Confirm pg crate + tests compile**

Run: `cd engine && cargo check -p nasrudin-pg --tests`
Expected: builds cleanly.

- [ ] **Step 6: Run the surviving pg tests against the migrated dev DB**

Run:
```bash
PGPASSWORD=physics_dev psql -h 127.0.0.1 -U physics -d postgres \
  -c "DROP DATABASE IF EXISTS physics_generator_test;"
PGPASSWORD=physics_dev psql -h 127.0.0.1 -U physics -d postgres \
  -c "CREATE DATABASE physics_generator_test;"
TEST_DATABASE_URL="postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test" \
  cargo test -p nasrudin-pg --test workers_query --test api_keys -- --test-threads=1
```
Expected: all pass.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/pg/src/query/users.rs \
        engine/crates/pg/tests/api_keys.rs \
        engine/crates/pg/tests/conjecture_jobs_query.rs
git rm engine/crates/pg/tests/users_oauth_link.rs
git commit -m "$(cat <<'EOF'
pg: users query — Firebase-shaped (create_firebase_user, find_by_firebase_uid)

Drops the old create_user signature (Argon2-style) and find_or_create_from_github.
Updates test call sites; deletes users_oauth_link.rs (tests of deleted code).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: Add `jsonwebtoken` dep + `firebase_auth.rs` types and JwksCache

**Files:**
- Modify: `engine/crates/api/Cargo.toml`
- Create: `engine/crates/api/src/firebase_auth.rs`
- Modify: `engine/crates/api/src/lib.rs`

- [ ] **Step 1: Add `jsonwebtoken` and dev-dep `rsa`**

Edit `engine/crates/api/Cargo.toml`. Under `[dependencies]` (alongside other crates), add:

```toml
jsonwebtoken = "9"
```

Under `[dev-dependencies]`, add:

```toml
rsa = "0.9"
```

(`rsa` is needed by tests in Task 5 to generate a keypair for signing JWT fixtures.)

- [ ] **Step 2: Create the firebase_auth module skeleton**

Write `engine/crates/api/src/firebase_auth.rs`:

```rust
//! Firebase ID token verification.
//!
//! Verifies short-lived (≤1h) Google-signed RS256 JWTs against Google's
//! published JWKs. Used exactly once per session by
//! `POST /api/auth/firebase-session` to exchange an ID token for an
//! axum-login session cookie. After exchange, the cookie is the source of
//! truth and Firebase is not consulted again.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

use jsonwebtoken::DecodingKey;
use serde::Deserialize;
use thiserror::Error;
use tokio::sync::RwLock;

const GOOGLE_JWKS_URL: &str =
    "https://www.googleapis.com/robot/v1/metadata/x509/securetoken@system.gserviceaccount.com";
const JWKS_REFRESH_INTERVAL: Duration = Duration::from_secs(3600);
const ISS_PREFIX: &str = "https://securetoken.google.com/";

/// Verified claims extracted from a Firebase ID token. Subset of the
/// fields Firebase emits — only what we use.
#[derive(Debug, Clone)]
pub struct FirebaseClaims {
    /// JWT `sub` — Firebase's stable user id.
    pub uid: String,
    pub email: String,
    pub email_verified: bool,
    pub name: Option<String>,
    pub picture: Option<String>,
    /// e.g. `"password"`, `"google.com"`. From `firebase.sign_in_provider`.
    pub sign_in_provider: String,
}

#[derive(Debug, Error)]
pub enum VerifyError {
    #[error("token expired")]
    Expired,
    #[error("wrong issuer")]
    WrongIssuer,
    #[error("wrong audience")]
    WrongAudience,
    #[error("bad signature")]
    BadSignature,
    #[error("malformed token: {0}")]
    MalformedToken(String),
    #[error("missing required claim: {0}")]
    MissingClaim(&'static str),
    #[error("jwks fetch failed: {0}")]
    JwksFetch(String),
}

/// Cache of Google's public keys, keyed by `kid` (key id from the JWT
/// header). Fetched lazily on first use; refreshed when an unknown `kid`
/// is encountered or when the cache is older than `JWKS_REFRESH_INTERVAL`.
///
/// Tests can construct a pre-populated cache with `for_test` to inject
/// their own keypair without hitting the network.
pub struct JwksCache {
    inner: RwLock<JwksCacheInner>,
}

struct JwksCacheInner {
    keys: HashMap<String, DecodingKey>,
    fetched_at: Option<Instant>,
}

impl JwksCache {
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(JwksCacheInner {
                keys: HashMap::new(),
                fetched_at: None,
            }),
        }
    }

    /// Build a cache pre-populated with a known keyset. For tests only.
    #[cfg(any(test, feature = "test-helpers"))]
    pub fn for_test(keys: HashMap<String, DecodingKey>) -> Self {
        Self {
            inner: RwLock::new(JwksCacheInner {
                keys,
                fetched_at: Some(Instant::now()),
            }),
        }
    }

    /// Force a fetch (used at boot to surface JWKs-fetch errors early).
    pub async fn warm(&self) -> Result<(), VerifyError> {
        self.refresh().await
    }

    /// Look up a decoding key by `kid`. If absent and the cache is older
    /// than 1 hour OR was never fetched, re-fetch and try once more.
    pub(crate) async fn get(&self, kid: &str) -> Option<DecodingKey> {
        {
            let guard = self.inner.read().await;
            if let Some(k) = guard.keys.get(kid) {
                return Some(k.clone());
            }
            if guard
                .fetched_at
                .map(|t| t.elapsed() < JWKS_REFRESH_INTERVAL)
                .unwrap_or(false)
            {
                return None;
            }
        }
        // Cache miss + stale (or empty) → refresh and look again.
        if self.refresh().await.is_err() {
            return None;
        }
        let guard = self.inner.read().await;
        guard.keys.get(kid).cloned()
    }

    async fn refresh(&self) -> Result<(), VerifyError> {
        let resp = reqwest::get(GOOGLE_JWKS_URL)
            .await
            .map_err(|e| VerifyError::JwksFetch(format!("{e}")))?
            .error_for_status()
            .map_err(|e| VerifyError::JwksFetch(format!("{e}")))?;
        let body: HashMap<String, String> = resp
            .json()
            .await
            .map_err(|e| VerifyError::JwksFetch(format!("{e}")))?;
        // Google's secure-token endpoint returns `{ kid: x509-pem-string }`.
        let mut keys = HashMap::with_capacity(body.len());
        for (kid, pem) in body {
            match DecodingKey::from_rsa_pem(pem.as_bytes()) {
                Ok(k) => {
                    keys.insert(kid, k);
                }
                Err(e) => {
                    tracing::warn!(kid = %kid, error = %e, "jwks: failed to parse pem; skipping");
                }
            }
        }
        if keys.is_empty() {
            return Err(VerifyError::JwksFetch("no usable keys in response".into()));
        }
        let mut guard = self.inner.write().await;
        guard.keys = keys;
        guard.fetched_at = Some(Instant::now());
        Ok(())
    }
}

impl Default for JwksCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Re-exported for callers (handlers + tests) that need to construct a
/// shared cache.
pub type SharedJwks = Arc<JwksCache>;

/// Verify a Firebase ID token and return its claims. Implemented in Task 5.
pub async fn verify_id_token(
    _token: &str,
    _project_id: &str,
    _jwks: &JwksCache,
) -> Result<FirebaseClaims, VerifyError> {
    Err(VerifyError::MalformedToken("not implemented".into()))
}
```

- [ ] **Step 3: Register the module in lib.rs**

Edit `engine/crates/api/src/lib.rs`. Add (alphabetical with the existing modules):

```rust
pub mod firebase_auth;
```

- [ ] **Step 4: Confirm api crate compiles**

Run: `cd engine && cargo check -p physics-api`
Expected: builds with one warning about the unused `Deserialize` import (that's used in Task 5).

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/Cargo.toml engine/Cargo.lock \
        engine/crates/api/src/firebase_auth.rs \
        engine/crates/api/src/lib.rs
git commit -m "$(cat <<'EOF'
api: firebase_auth scaffold (types, JwksCache, deps)

JwksCache lazy-fetches Google's secure-token public keys, refreshes
hourly, supports test injection via for_test. verify_id_token stub
returns MalformedToken; real implementation in the next commit.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Implement `verify_id_token` + comprehensive unit tests

**Files:**
- Modify: `engine/crates/api/src/firebase_auth.rs`
- Create: `engine/crates/api/tests/firebase_verify.rs`

- [ ] **Step 1: Implement `verify_id_token`**

Edit `engine/crates/api/src/firebase_auth.rs`. Replace the stub `verify_id_token` and add the wire-claim helper struct. The full module file becomes (only the changes shown — keep everything else from Task 4):

Add this private wire-struct above `verify_id_token`:

```rust
/// Wire shape of the JWT claims, before mapping into `FirebaseClaims`.
/// Standard JWT claims (iss, aud, exp, iat) are validated by jsonwebtoken
/// itself; we only deserialize the fields we need to expose.
#[derive(Deserialize)]
struct WireClaims {
    sub: String,
    email: Option<String>,
    email_verified: Option<bool>,
    name: Option<String>,
    picture: Option<String>,
    firebase: WireFirebaseExt,
}

#[derive(Deserialize)]
struct WireFirebaseExt {
    sign_in_provider: String,
}
```

Then replace the stub with:

```rust
pub async fn verify_id_token(
    token: &str,
    project_id: &str,
    jwks: &JwksCache,
) -> Result<FirebaseClaims, VerifyError> {
    use jsonwebtoken::{Algorithm, Validation, decode, decode_header};

    // 1. Parse header → grab kid.
    let header =
        decode_header(token).map_err(|e| VerifyError::MalformedToken(format!("{e}")))?;
    if header.alg != Algorithm::RS256 {
        // Algorithm-confusion defense: refuse anything that's not RS256.
        return Err(VerifyError::BadSignature);
    }
    let kid = header
        .kid
        .ok_or_else(|| VerifyError::MalformedToken("missing kid".into()))?;

    // 2. Look up the public key (refreshes JWKs if needed).
    let key = jwks
        .get(&kid)
        .await
        .ok_or(VerifyError::BadSignature)?;

    // 3. Validate signature + standard claims.
    let mut validation = Validation::new(Algorithm::RS256);
    validation.set_audience(&[project_id]);
    validation.set_issuer(&[format!("{ISS_PREFIX}{project_id}")]);
    validation.leeway = 60; // small clock-skew tolerance on iat / nbf
    validation.validate_exp = true;
    validation.required_spec_claims =
        std::collections::HashSet::from(["exp".into(), "iat".into(), "aud".into(), "iss".into()]);

    let data = match decode::<WireClaims>(token, &key, &validation) {
        Ok(d) => d,
        Err(e) => {
            return Err(match e.kind() {
                jsonwebtoken::errors::ErrorKind::ExpiredSignature => VerifyError::Expired,
                jsonwebtoken::errors::ErrorKind::InvalidIssuer => VerifyError::WrongIssuer,
                jsonwebtoken::errors::ErrorKind::InvalidAudience => VerifyError::WrongAudience,
                jsonwebtoken::errors::ErrorKind::InvalidSignature
                | jsonwebtoken::errors::ErrorKind::InvalidAlgorithm => VerifyError::BadSignature,
                _ => VerifyError::MalformedToken(format!("{e}")),
            });
        }
    };

    let wire = data.claims;
    if wire.sub.is_empty() {
        return Err(VerifyError::MissingClaim("sub"));
    }
    let email = wire.email.ok_or(VerifyError::MissingClaim("email"))?;

    Ok(FirebaseClaims {
        uid: wire.sub,
        email,
        email_verified: wire.email_verified.unwrap_or(false),
        name: wire.name,
        picture: wire.picture,
        sign_in_provider: wire.firebase.sign_in_provider,
    })
}
```

- [ ] **Step 2: Confirm api crate compiles**

Run: `cd engine && cargo check -p physics-api`
Expected: builds cleanly.

- [ ] **Step 3: Write the unit-style integration test**

Create `engine/crates/api/tests/firebase_verify.rs`:

```rust
//! Unit tests for `firebase_auth::verify_id_token`.
//!
//! Generates a fresh RSA keypair per test, mints test tokens with it,
//! injects the public key into a JwksCache via `for_test`, and verifies.
//! No network access; no Firebase emulator required.

use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use jsonwebtoken::{Algorithm, DecodingKey, EncodingKey, Header, encode};
use rsa::{
    RsaPrivateKey,
    pkcs1::EncodeRsaPrivateKey,
    pkcs8::{EncodePublicKey, LineEnding},
};
use serde::Serialize;

use physics_api::firebase_auth::{JwksCache, VerifyError, verify_id_token};

const TEST_PROJECT_ID: &str = "test-project";
const TEST_KID: &str = "test-kid-1";

#[derive(Serialize)]
struct WireClaims {
    sub: String,
    email: String,
    email_verified: bool,
    name: Option<String>,
    iss: String,
    aud: String,
    exp: usize,
    iat: usize,
    firebase: WireFirebase,
}

#[derive(Serialize)]
struct WireFirebase {
    sign_in_provider: String,
}

struct Keypair {
    encoding: EncodingKey,
    decoding: DecodingKey,
}

fn gen_keypair() -> Keypair {
    let mut rng = rand::thread_rng();
    let priv_key = RsaPrivateKey::new(&mut rng, 2048).expect("rsa keygen");
    let priv_pem = priv_key
        .to_pkcs1_pem(LineEnding::LF)
        .expect("priv pem")
        .to_string();
    let pub_pem = priv_key
        .to_public_key()
        .to_public_key_pem(LineEnding::LF)
        .expect("pub pem");
    let encoding = EncodingKey::from_rsa_pem(priv_pem.as_bytes()).expect("decode priv");
    let decoding = DecodingKey::from_rsa_pem(pub_pem.as_bytes()).expect("decode pub");
    Keypair { encoding, decoding }
}

fn make_jwks(decoding: DecodingKey) -> JwksCache {
    let mut keys = HashMap::new();
    keys.insert(TEST_KID.to_owned(), decoding);
    JwksCache::for_test(keys)
}

fn now_secs() -> usize {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs() as usize
}

fn default_claims() -> WireClaims {
    let now = now_secs();
    WireClaims {
        sub: "fb-uid-1".into(),
        email: "alice@example.test".into(),
        email_verified: true,
        name: Some("Alice".into()),
        iss: format!("https://securetoken.google.com/{TEST_PROJECT_ID}"),
        aud: TEST_PROJECT_ID.into(),
        exp: now + 3600,
        iat: now - 10,
        firebase: WireFirebase {
            sign_in_provider: "password".into(),
        },
    }
}

fn header_with_kid(alg: Algorithm) -> Header {
    let mut h = Header::new(alg);
    h.kid = Some(TEST_KID.into());
    h
}

fn sign(claims: &WireClaims, encoding: &EncodingKey) -> String {
    encode(&header_with_kid(Algorithm::RS256), claims, encoding).unwrap()
}

#[tokio::test]
async fn accepts_valid_token() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let token = sign(&default_claims(), &kp.encoding);
    let claims = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap();
    assert_eq!(claims.uid, "fb-uid-1");
    assert_eq!(claims.email, "alice@example.test");
    assert!(claims.email_verified);
    assert_eq!(claims.sign_in_provider, "password");
    assert_eq!(claims.name.as_deref(), Some("Alice"));
}

#[tokio::test]
async fn rejects_expired_token() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let mut c = default_claims();
    c.exp = now_secs() - 60;
    c.iat = now_secs() - 3600;
    let token = sign(&c, &kp.encoding);
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::Expired));
}

#[tokio::test]
async fn rejects_wrong_audience() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let mut c = default_claims();
    c.aud = "another-project".into();
    let token = sign(&c, &kp.encoding);
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::WrongAudience));
}

#[tokio::test]
async fn rejects_wrong_issuer() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let mut c = default_claims();
    c.iss = "https://evil.example.com/test-project".into();
    let token = sign(&c, &kp.encoding);
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::WrongIssuer));
}

#[tokio::test]
async fn rejects_token_signed_with_wrong_key() {
    let kp_real = gen_keypair();
    let kp_attacker = gen_keypair();
    // JWKs cache holds the *real* public key.
    let jwks = make_jwks(kp_real.decoding);
    // Token signed with the *attacker's* private key.
    let token = sign(&default_claims(), &kp_attacker.encoding);
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::BadSignature));
}

#[tokio::test]
async fn rejects_malformed_token() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let err = verify_id_token("not.a.jwt", TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::MalformedToken(_)));
}

#[tokio::test]
async fn rejects_kid_not_in_jwks() {
    let kp_real = gen_keypair();
    let kp_other = gen_keypair();
    // JWKs cache only knows about the real key.
    let jwks = make_jwks(kp_real.decoding);
    // Token claims to be signed by an unknown kid.
    let mut header = Header::new(Algorithm::RS256);
    header.kid = Some("unknown-kid".into());
    let token = encode(&header, &default_claims(), &kp_other.encoding).unwrap();
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::BadSignature));
}

#[tokio::test]
async fn rejects_missing_kid_in_header() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let header_no_kid = Header::new(Algorithm::RS256);
    let token = encode(&header_no_kid, &default_claims(), &kp.encoding).unwrap();
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::MalformedToken(_)));
}
```

- [ ] **Step 4: Run the tests**

Run: `cd engine && cargo test -p physics-api --test firebase_verify -- --test-threads=1`
Expected: all eight tests pass.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/firebase_auth.rs \
        engine/crates/api/tests/firebase_verify.rs
git commit -m "$(cat <<'EOF'
api: firebase_auth — verify_id_token + 8 unit tests

Verifies RS256-signed Firebase ID tokens against an injected JwksCache.
Rejects: expired, wrong issuer, wrong audience, wrong signing key,
malformed tokens, unknown kid, missing kid, non-RS256 algorithm.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: Update `AuthUser` for firebase_uid; neutralize `Backend::authenticate`

**Files:**
- Modify: `engine/crates/api/src/auth.rs`

- [ ] **Step 1: Replace `AuthUser`**

Edit `engine/crates/api/src/auth.rs`. Replace the entire `AuthUser` struct + `from_model` + `axum_login::AuthUser` impl with:

```rust
/// Wrapper around the pg `users::Model` that implements `axum_login::AuthUser`.
#[derive(Debug, Clone, Serialize)]
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
    /// Firebase UID — the source-of-truth identity link. Never serialised
    /// (Firebase tokens already carry it; we expose it via /api/auth/me only
    /// because the frontend may want to assert "this is the user I think it
    /// is" before issuing API calls).
    pub firebase_uid: String,
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
        }
    }
}

impl axum_login::AuthUser for AuthUser {
    type Id = Uuid;

    fn id(&self) -> Uuid {
        self.id
    }

    fn session_auth_hash(&self) -> &[u8] {
        // Stable per-user secret. The firebase_uid never changes for a given
        // user; if it ever does (provider unlink + relink edge case), all
        // existing sessions invalidate, which is the correct behavior.
        self.firebase_uid.as_bytes()
    }
}
```

- [ ] **Step 2: Replace `Backend::authenticate` with a no-op**

In the same file, find `impl AuthnBackend for Backend` and replace its `authenticate` method:

```rust
    async fn authenticate(
        &self,
        _creds: Self::Credentials,
    ) -> Result<Option<Self::User>, Self::Error> {
        // axum-login's AuthnBackend trait requires authenticate, but our
        // session-issue path is firebase_session, which doesn't go through
        // axum_login::AuthSession::authenticate(). We never call this
        // method; return None to make accidental calls fail closed.
        Ok(None)
    }
```

`get_user` is unchanged.

- [ ] **Step 3: Drop the `password_auth` import + `Credentials` struct (if no longer used)**

In `engine/crates/api/src/auth.rs`, the `Credentials` struct and `password_auth::*` imports were only used by the old `register`/`login` handlers (deleted in Task 9). Leave them in place for now — the file still compiles. They get cleaned up in Task 10.

- [ ] **Step 4: Confirm compile**

Run: `cd engine && cargo check -p physics-api`
Expected: builds (warnings about unused imports / `Credentials` are fine — Task 10 cleans up).

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/auth.rs
git commit -m "$(cat <<'EOF'
api: AuthUser is firebase-shaped; Backend::authenticate is a no-op

session_auth_hash returns firebase_uid bytes (stable per user).
authenticate() returns Ok(None) — we never call it; sessions are issued
exclusively via the upcoming firebase_session handler.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Update AppState — drop `oauth_github`, add Firebase fields; update test harness

**Files:**
- Modify: `engine/crates/api/src/state.rs`
- Modify: `engine/crates/api/tests/test_app/mod.rs`

- [ ] **Step 1: Update `state.rs`**

Edit `engine/crates/api/src/state.rs`.

Remove the `GithubOAuthConfig` struct + `impl from_env` block (everything from `/// GitHub OAuth credentials.` through the closing `}` of `impl GithubOAuthConfig`).

In the `AppState` struct, remove the field:

```rust
    pub oauth_github: Option<GithubOAuthConfig>,
```

Add the Firebase fields:

```rust
    /// Firebase project id (e.g. `"nasrudin"`). When `None`,
    /// `/api/auth/firebase-session` returns 503 and email/Google sign-in
    /// is unavailable. Other endpoints work normally.
    pub firebase_project_id: Option<String>,
    /// Lazily-fetched Google JWKs, used to verify Firebase ID tokens.
    pub firebase_jwks: Arc<crate::firebase_auth::JwksCache>,
```

- [ ] **Step 2: Update `test_app/mod.rs` AppState construction**

Edit `engine/crates/api/tests/test_app/mod.rs`. Find the `AppState { ... }` literal and replace `oauth_github: None,` with:

```rust
        firebase_project_id: Some("test-project".into()),
        firebase_jwks: Arc::new(physics_api::firebase_auth::JwksCache::new()),
```

- [ ] **Step 3: Confirm compile**

Run: `cd engine && cargo check -p physics-api --tests`
Expected: builds. There will be errors in `auth_oauth.rs` referencing `GithubOAuthConfig` — that's fine, it's deleted in Task 10.

Wait — actually `auth_oauth.rs` references `state::GithubOAuthConfig`, so the api crate **won't** build at this step. Adjust: delete the import line in `auth_oauth.rs` to keep the file compilable for now.

Edit `engine/crates/api/src/auth_oauth.rs`. Find:

```rust
use crate::state::{AppState, GithubOAuthConfig};
```

Replace with:

```rust
#![allow(dead_code, unused_imports)]
use crate::state::AppState;
```

And in `auth_oauth.rs` find any `state.oauth_github` reference and replace with a `let cfg: Option<()> = None;` so the file compiles trivially. Actually — simpler: replace the **entire body** of `auth_oauth.rs` with a stub:

```rust
//! GitHub OAuth handlers — DEPRECATED, removed in this round. The whole
//! file is deleted in Task 10; this stub keeps the crate compiling
//! between Task 7 and Task 10.

#![allow(dead_code)]
```

- [ ] **Step 4: Confirm compile (again, with the stub)**

Run: `cd engine && cargo check -p physics-api --tests`
Expected: builds. `main.rs` still references `physics_api::auth_oauth::start` and `::callback` — fix those by stubbing them out too:

Edit `engine/crates/api/src/main.rs`. Find the `auth_strict` Router block (around line 720) and **temporarily** delete the two GitHub routes:

```rust
        let auth_strict = Router::new()
            .route("/api/auth/register", axum::routing::post(auth::register))
            .route("/api/auth/login", axum::routing::post(auth::login))
            .layer(GovernorLayer::new(rate_limit::auth_strict()));
```

(The `register` + `login` routes will themselves be deleted in Task 9. We are only doing the minimal edit here to compile.)

Now the `oauth_github` field is no longer referenced in `main.rs`, so delete its loading too. Find and remove:

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

And in the `AppState { ... }` literal, replace `oauth_github,` with the new pair:

```rust
        firebase_project_id: std::env::var("FIREBASE_PROJECT_ID").ok().filter(|s| !s.is_empty()),
        firebase_jwks: Arc::new(physics_api::firebase_auth::JwksCache::new()),
```

(The warm-on-boot call goes in Task 9.)

Run: `cd engine && cargo check -p physics-api --tests`
Expected: clean build.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/state.rs \
        engine/crates/api/src/auth_oauth.rs \
        engine/crates/api/src/main.rs \
        engine/crates/api/tests/test_app/mod.rs
git commit -m "$(cat <<'EOF'
api: AppState — drop oauth_github, add firebase_project_id + jwks

auth_oauth.rs is stubbed out to keep the crate compiling between this
commit and the full deletion in a follow-up. main.rs loads
FIREBASE_PROJECT_ID from env (None when unset).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8: Implement `POST /api/auth/firebase-session` handler

**Files:**
- Modify: `engine/crates/api/src/auth.rs`

- [ ] **Step 1: Add the handler**

Edit `engine/crates/api/src/auth.rs`. Append after the existing handlers (`register`, `login`, `logout`, `me` — these still exist; `register` + `login` are deleted in Task 9):

```rust
// ---------------------------------------------------------------------------
// Firebase session-exchange
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
pub struct FirebaseSessionInput {
    pub id_token: String,
}

/// `POST /api/auth/firebase-session`
///
/// Verifies a Firebase ID token (RS256 JWT against Google's JWKs),
/// find-or-creates the matching `users` row keyed by `firebase_uid`, and
/// issues an axum-login session cookie. The Firebase ID token is consumed
/// once and not stored.
///
/// Strict-verification policy: rejects `email_verified == false` for the
/// `password` provider only. Google-provider sign-ins pass through (Google
/// guarantees the email is verified).
pub async fn firebase_session(
    State(state): State<std::sync::Arc<crate::state::AppState>>,
    mut auth_session: AuthSess,
    Json(body): Json<FirebaseSessionInput>,
) -> impl IntoResponse {
    let Some(ref project_id) = state.firebase_project_id else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "firebase_not_configured" })),
        );
    };

    // 1. Verify the token.
    let claims = match crate::firebase_auth::verify_id_token(
        &body.id_token,
        project_id,
        &state.firebase_jwks,
    )
    .await
    {
        Ok(c) => c,
        Err(e) => {
            let (code, msg) = match e {
                crate::firebase_auth::VerifyError::Expired => ("token_expired", "id token expired"),
                crate::firebase_auth::VerifyError::WrongAudience => {
                    ("wrong_audience", "id token aud mismatch")
                }
                crate::firebase_auth::VerifyError::WrongIssuer => {
                    ("wrong_issuer", "id token iss mismatch")
                }
                crate::firebase_auth::VerifyError::BadSignature => {
                    ("bad_signature", "id token signature invalid")
                }
                crate::firebase_auth::VerifyError::MalformedToken(_) => {
                    ("malformed_token", "id token malformed")
                }
                crate::firebase_auth::VerifyError::MissingClaim(c) => {
                    tracing::warn!(claim = c, "firebase id token missing required claim");
                    ("missing_claim", "id token missing required claim")
                }
                crate::firebase_auth::VerifyError::JwksFetch(_) => {
                    return (
                        StatusCode::BAD_GATEWAY,
                        Json(serde_json::json!({ "error": "jwks_unavailable" })),
                    );
                }
            };
            tracing::info!(error = msg, "firebase_session verify failed");
            return (
                StatusCode::UNAUTHORIZED,
                Json(serde_json::json!({ "error": code })),
            );
        }
    };

    // 2. Strict email-verification policy: only enforce for password provider.
    if !claims.email_verified && claims.sign_in_provider == "password" {
        return (
            StatusCode::FORBIDDEN,
            Json(serde_json::json!({ "error": "email_not_verified" })),
        );
    }

    // 3. Find or create user.
    let db = auth_session.backend.db.clone();
    let user_model = match nasrudin_pg::query::users::find_by_firebase_uid(&db, &claims.uid).await
    {
        Ok(Some(m)) => m,
        Ok(None) => match nasrudin_pg::query::users::create_firebase_user(
            &db,
            &claims.uid,
            &claims.email,
            claims.name.as_deref(),
        )
        .await
        {
            Ok(m) => m,
            Err(e) => {
                tracing::error!(error = %e, "create_firebase_user failed");
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(serde_json::json!({ "error": "user_create_failed" })),
                );
            }
        },
        Err(e) => {
            tracing::error!(error = %e, "find_by_firebase_uid failed");
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": "db_lookup_failed" })),
            );
        }
    };

    let auth_user = AuthUser::from_model(user_model);

    // 4. Issue session cookie.
    if let Err(e) = auth_session.login(&auth_user).await {
        tracing::error!(error = %e, "axum-login session create failed");
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": "session_create_failed" })),
        );
    }

    (StatusCode::OK, Json(serde_json::to_value(&auth_user).unwrap()))
}
```

- [ ] **Step 2: Confirm compile**

Run: `cd engine && cargo check -p physics-api`
Expected: builds.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/auth.rs
git commit -m "$(cat <<'EOF'
api: POST /api/auth/firebase-session handler

Verifies the Firebase ID token, applies strict email-verification policy
for the password provider, find-or-creates the users row by firebase_uid,
issues an axum-login session cookie. Returns the AuthUser body matching
GET /api/auth/me.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: Wire `/api/auth/firebase-session` route; delete register/login routes; pre-warm JWKs

**Files:**
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/api/src/auth.rs`

- [ ] **Step 1: Pre-warm JWKs at boot in `main.rs`**

Edit `engine/crates/api/src/main.rs`. After the `let admin_token = ...;` block (~line 141), before the `AppState { ... }` literal, add:

```rust
    let firebase_project_id = std::env::var("FIREBASE_PROJECT_ID")
        .ok()
        .filter(|s| !s.is_empty());
    let firebase_jwks = Arc::new(physics_api::firebase_auth::JwksCache::new());
    if firebase_project_id.is_some() {
        // Pre-warm the JWKs cache so the first sign-in doesn't pay a
        // ~200ms HTTP round-trip latency. Failure here is non-fatal —
        // the cache will lazily retry on first /api/auth/firebase-session
        // call. We just log and continue.
        let jwks_for_warm = Arc::clone(&firebase_jwks);
        tokio::spawn(async move {
            match jwks_for_warm.warm().await {
                Ok(_) => tracing::info!("firebase JWKs pre-warmed"),
                Err(e) => tracing::warn!(error = %e, "firebase JWKs pre-warm failed; will lazy-fetch"),
            }
        });
        tracing::info!("Firebase Auth configured");
    } else {
        tracing::info!("FIREBASE_PROJECT_ID unset — /api/auth/firebase-session returns 503");
    }
```

In the `AppState { ... }` literal, replace the temporary inline `firebase_project_id: std::env::var(...)...` from Task 7 with the variables defined above:

```rust
        firebase_project_id,
        firebase_jwks,
```

- [ ] **Step 2: Replace the `auth_strict` router block**

In `main.rs`, find the `auth_strict` Router block (added in Task 7) and replace it with:

```rust
        let auth_strict = Router::new()
            .route(
                "/api/auth/firebase-session",
                axum::routing::post(auth::firebase_session),
            )
            .layer(GovernorLayer::new(rate_limit::auth_strict()));
```

The `register` and `login` routes are gone. `logout` and `me` remain in `auth_session` block (unchanged from current state — verify by searching for `auth::logout` and `auth::me`).

- [ ] **Step 3: Delete the `register` and `login` handlers from `auth.rs`**

Edit `engine/crates/api/src/auth.rs`. Delete:

- The `RegisterInput` struct.
- The `register` function (entire `pub async fn register(...)`).
- The `login` function (entire `pub async fn login(...)`).
- The `Credentials` struct (no longer used).
- The `use password_auth::...;` import if present.

Keep: `Backend`, `AuthUser`, `AuthError`, `AuthnBackend` impl, `AuthSess` type alias, `logout`, `me`, `firebase_session`, `AuthOrApiKey`, `WorkerAuth`.

- [ ] **Step 4: Confirm compile**

Run: `cd engine && cargo check -p physics-api`
Expected: builds. There may be unused-import warnings — fine.

- [ ] **Step 5: Run the existing auth-extractor tests to confirm no regression**

Run:
```bash
cd engine && cargo test -p physics-api --test auth_or_apikey --test worker_auth -- --nocapture
```
Expected: passes.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/main.rs engine/crates/api/src/auth.rs
git commit -m "$(cat <<'EOF'
api: route /api/auth/firebase-session; delete register + login

main.rs loads FIREBASE_PROJECT_ID, pre-warms JWKs cache in a background
task. Old register and login routes + handlers are deleted; the new
auth_strict bucket holds only firebase-session.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 10: Delete `auth_oauth.rs` + drop `oauth2` dep + clean `.env.example` GitHub block

**Files:**
- Delete: `engine/crates/api/src/auth_oauth.rs`
- Modify: `engine/crates/api/src/lib.rs`
- Modify: `engine/crates/api/Cargo.toml`

- [ ] **Step 1: Delete the file and remove the module declaration**

```bash
rm engine/crates/api/src/auth_oauth.rs
```

Edit `engine/crates/api/src/lib.rs`. Remove the line:

```rust
pub mod auth_oauth;
```

- [ ] **Step 2: Remove the `oauth2` dependency**

Edit `engine/crates/api/Cargo.toml`. Find and delete:

```toml
oauth2 = { version = "4", default-features = false, features = ["reqwest", "rustls-tls"] }
```

Also revert the `axum-extra` cookie feature added in the GitHub round (cookie support isn't needed by the Firebase flow). Find:

```toml
axum-extra = { workspace = true, features = ["typed-header", "cookie"] }
```

Replace with:

```toml
axum-extra = { workspace = true }
```

- [ ] **Step 3: Confirm compile**

Run: `cd engine && cargo check -p physics-api`
Expected: builds cleanly.

- [ ] **Step 4: Confirm full workspace still builds**

Run: `cd engine && cargo build --workspace`
Expected: clean build (may take ~2 min).

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/lib.rs engine/crates/api/Cargo.toml engine/Cargo.lock
git rm engine/crates/api/src/auth_oauth.rs
git commit -m "$(cat <<'EOF'
api: delete auth_oauth.rs (GitHub OAuth) + drop oauth2 dep

Drops the GitHub-OAuth-on-axum-login work from the previous round; that
flow is now served by Firebase. Reverts axum-extra cookie feature; the
Firebase flow uses bearer tokens, not cookies, in the request body.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11: Integration test for `POST /api/auth/firebase-session`

**Files:**
- Modify: `engine/crates/api/tests/test_app/mod.rs`
- Create: `engine/crates/api/tests/firebase_session.rs`

- [ ] **Step 1: Expose a JWKs-injecting builder in the test harness**

Edit `engine/crates/api/tests/test_app/mod.rs`. Find the route registration block, find the existing `/api/me/stats` route, and add the new route nearby:

```rust
        .route(
            "/api/auth/firebase-session",
            axum::routing::post(physics_api::auth::firebase_session),
        )
```

Below `pub async fn build()`, add a new public helper that builds a TestApp with a pre-populated JwksCache and a known project id:

```rust
/// Like `build()` but with a JwksCache pre-populated with the supplied
/// (kid → DecodingKey) entries. Used by `firebase_session.rs` to inject
/// a test keypair.
pub async fn build_with_jwks(
    project_id: &str,
    jwks: std::collections::HashMap<String, jsonwebtoken::DecodingKey>,
) -> Option<TestApp> {
    let mut app = build().await?;
    let new_jwks = std::sync::Arc::new(
        physics_api::firebase_auth::JwksCache::for_test(jwks),
    );
    // Replace AppState.firebase_project_id + firebase_jwks. Because
    // AppState is owned by the Router via with_state, we rebuild the
    // router using the same pieces but a new AppState. To keep this
    // minimal, the test harness re-runs `build()` and patches the state
    // — but Arc<AppState> means we can't mutate in place. Easiest path:
    // construct a fresh AppState here. But we don't expose AppState
    // construction publicly. Instead, expose firebase_project_id +
    // firebase_jwks as inputs to a build_inner the harness can call.
    //
    // Implementation: refactor build() to delegate to build_inner(opts).
    // See Step 2 below.
    let _ = (project_id, new_jwks, &mut app);
    unimplemented!("see Step 2: refactor build() to take options");
}
```

(Yes, this is a forward-reference. Implement it properly in Step 2.)

- [ ] **Step 2: Refactor `build()` to accept overrides**

In `tests/test_app/mod.rs`, refactor as follows:

Add at the top of the file (next to other helper definitions):

```rust
/// Per-test overrides for the harness.
#[derive(Default)]
pub struct BuildOpts {
    pub firebase_project_id: Option<String>,
    pub firebase_jwks: Option<std::sync::Arc<physics_api::firebase_auth::JwksCache>>,
}
```

Rename the existing `build()` to `build_with_opts(opts: BuildOpts)`. Inside it, replace these two AppState fields:

```rust
        firebase_project_id: Some("test-project".into()),
        firebase_jwks: Arc::new(physics_api::firebase_auth::JwksCache::new()),
```

with:

```rust
        firebase_project_id: opts
            .firebase_project_id
            .or_else(|| Some("test-project".into())),
        firebase_jwks: opts
            .firebase_jwks
            .unwrap_or_else(|| Arc::new(physics_api::firebase_auth::JwksCache::new())),
```

Add a new `build()` shim for back-compat:

```rust
pub async fn build() -> Option<TestApp> {
    build_with_opts(BuildOpts::default()).await
}
```

Replace the placeholder `build_with_jwks` with a real one:

```rust
pub async fn build_with_jwks(
    project_id: &str,
    jwks: std::collections::HashMap<String, jsonwebtoken::DecodingKey>,
) -> Option<TestApp> {
    build_with_opts(BuildOpts {
        firebase_project_id: Some(project_id.into()),
        firebase_jwks: Some(std::sync::Arc::new(
            physics_api::firebase_auth::JwksCache::for_test(jwks),
        )),
    })
    .await
}
```

- [ ] **Step 3: Confirm compile**

Run: `cd engine && cargo check -p physics-api --tests`
Expected: builds cleanly.

- [ ] **Step 4: Write the integration test**

Create `engine/crates/api/tests/firebase_session.rs`:

```rust
//! End-to-end test: POST /api/auth/firebase-session creates a user, issues
//! a session cookie, and subsequent /api/auth/me returns the user.

mod test_app;

use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use axum::body::{Body, to_bytes};
use axum::http::{Request, StatusCode, header};
use jsonwebtoken::{Algorithm, DecodingKey, EncodingKey, Header, encode};
use rsa::{
    RsaPrivateKey,
    pkcs1::EncodeRsaPrivateKey,
    pkcs8::{EncodePublicKey, LineEnding},
};
use serde::Serialize;
use tower::util::ServiceExt;

const TEST_PROJECT: &str = "test-project";
const TEST_KID: &str = "kid-test-1";

#[derive(Serialize)]
struct WireClaims {
    sub: String,
    email: String,
    email_verified: bool,
    name: Option<String>,
    iss: String,
    aud: String,
    exp: usize,
    iat: usize,
    firebase: WireFirebase,
}
#[derive(Serialize)]
struct WireFirebase {
    sign_in_provider: String,
}

struct Kp {
    enc: EncodingKey,
    dec: DecodingKey,
}

fn gen_kp() -> Kp {
    let mut rng = rand::thread_rng();
    let pk = RsaPrivateKey::new(&mut rng, 2048).expect("rsa keygen");
    let priv_pem = pk.to_pkcs1_pem(LineEnding::LF).unwrap().to_string();
    let pub_pem = pk.to_public_key().to_public_key_pem(LineEnding::LF).unwrap();
    Kp {
        enc: EncodingKey::from_rsa_pem(priv_pem.as_bytes()).unwrap(),
        dec: DecodingKey::from_rsa_pem(pub_pem.as_bytes()).unwrap(),
    }
}

fn now() -> usize {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs() as usize
}

fn mint(uid: &str, email: &str, provider: &str, verified: bool, kp: &Kp) -> String {
    let claims = WireClaims {
        sub: uid.into(),
        email: email.into(),
        email_verified: verified,
        name: Some("Test User".into()),
        iss: format!("https://securetoken.google.com/{TEST_PROJECT}"),
        aud: TEST_PROJECT.into(),
        exp: now() + 3600,
        iat: now() - 5,
        firebase: WireFirebase { sign_in_provider: provider.into() },
    };
    let mut h = Header::new(Algorithm::RS256);
    h.kid = Some(TEST_KID.into());
    encode(&h, &claims, &kp.enc).unwrap()
}

#[tokio::test]
async fn google_user_creates_row_and_session() {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let Some(app) = test_app::build_with_jwks(TEST_PROJECT, jwks).await else { return };

    let token = mint("fb-uid-google-1", "google.user@example.test", "google.com", true, &kp);

    // 1. POST → expect 200 + user JSON.
    let req = Request::builder()
        .method("POST")
        .uri("/api/auth/firebase-session")
        .header(header::CONTENT_TYPE, "application/json")
        .body(Body::from(format!(r#"{{"id_token":"{token}"}}"#)))
        .unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);

    // Capture the Set-Cookie header for the second request.
    let cookie = resp
        .headers()
        .get(header::SET_COOKIE)
        .expect("set-cookie present")
        .to_str()
        .unwrap()
        .split(';')
        .next()
        .unwrap()
        .to_owned();

    let body = to_bytes(resp.into_body(), 1 << 16).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(v["email"], "google.user@example.test");
    assert_eq!(v["firebase_uid"], "fb-uid-google-1");

    // 2. GET /api/auth/me with the cookie → 200 + same user.
    let me = Request::builder()
        .uri("/api/auth/me")
        .header(header::COOKIE, &cookie)
        .body(Body::empty())
        .unwrap();
    let me_resp = app.router.clone().oneshot(me).await.unwrap();
    assert_eq!(me_resp.status(), StatusCode::OK);
    let body = to_bytes(me_resp.into_body(), 1 << 16).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(v["firebase_uid"], "fb-uid-google-1");
}

#[tokio::test]
async fn returning_user_reuses_existing_row() {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let Some(app) = test_app::build_with_jwks(TEST_PROJECT, jwks).await else { return };

    let token = mint("fb-uid-returning", "ret@example.test", "google.com", true, &kp);
    // First call → create.
    let r1 = app.router.clone().oneshot(
        Request::builder()
            .method("POST")
            .uri("/api/auth/firebase-session")
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from(format!(r#"{{"id_token":"{token}"}}"#)))
            .unwrap(),
    ).await.unwrap();
    assert_eq!(r1.status(), StatusCode::OK);
    let v1: serde_json::Value = serde_json::from_slice(&to_bytes(r1.into_body(), 1<<16).await.unwrap()).unwrap();

    // Second call (same token) → return existing.
    let r2 = app.router.clone().oneshot(
        Request::builder()
            .method("POST")
            .uri("/api/auth/firebase-session")
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from(format!(r#"{{"id_token":"{token}"}}"#)))
            .unwrap(),
    ).await.unwrap();
    assert_eq!(r2.status(), StatusCode::OK);
    let v2: serde_json::Value = serde_json::from_slice(&to_bytes(r2.into_body(), 1<<16).await.unwrap()).unwrap();

    assert_eq!(v1["id"], v2["id"], "same users.id reused on second call");
}

#[tokio::test]
async fn rejects_unverified_password_user() {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let Some(app) = test_app::build_with_jwks(TEST_PROJECT, jwks).await else { return };

    let token = mint("fb-uid-unverified", "noverify@example.test", "password", false, &kp);
    let resp = app.router.clone().oneshot(
        Request::builder()
            .method("POST")
            .uri("/api/auth/firebase-session")
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from(format!(r#"{{"id_token":"{token}"}}"#)))
            .unwrap(),
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::FORBIDDEN);
    let v: serde_json::Value = serde_json::from_slice(&to_bytes(resp.into_body(), 1<<16).await.unwrap()).unwrap();
    assert_eq!(v["error"], "email_not_verified");
}

#[tokio::test]
async fn rejects_invalid_token() {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let Some(app) = test_app::build_with_jwks(TEST_PROJECT, jwks).await else { return };

    let resp = app.router.clone().oneshot(
        Request::builder()
            .method("POST")
            .uri("/api/auth/firebase-session")
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from(r#"{"id_token":"not.a.real.jwt"}"#))
            .unwrap(),
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
}
```

- [ ] **Step 5: Run the integration test**

Run:
```bash
PGPASSWORD=physics_dev psql -h 127.0.0.1 -U physics -d postgres -c "DROP DATABASE IF EXISTS physics_generator_test;"
PGPASSWORD=physics_dev psql -h 127.0.0.1 -U physics -d postgres -c "CREATE DATABASE physics_generator_test;"
TEST_DATABASE_URL="postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test" \
  cargo test -p physics-api --test firebase_session -- --test-threads=1
```
Expected: all 4 tests pass.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/tests/test_app/mod.rs \
        engine/crates/api/tests/firebase_session.rs
git commit -m "$(cat <<'EOF'
api: integration tests for /api/auth/firebase-session

Test harness gains build_with_jwks(project_id, jwks_map) for injecting
a test keypair. Four scenarios covered: create-new (Google), reuse-row,
reject-unverified-password, reject-invalid-token.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12: Frontend — install `firebase` + add `VITE_FIREBASE_*` env vars

**Files:**
- Modify: `nasrudin-frontend/package.json`
- Modify: `nasrudin-frontend/pnpm-lock.yaml` (auto-updated)

- [ ] **Step 1: Install `firebase`**

Run:
```bash
pnpm -C nasrudin-frontend add firebase
```
Expected: `firebase ^10.x` (or current major) added to `dependencies`.

- [ ] **Step 2: Confirm tsc still passes**

Run: `pnpm -C nasrudin-frontend exec tsc --noEmit`
Expected: no new errors.

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/package.json nasrudin-frontend/pnpm-lock.yaml
git commit -m "$(cat <<'EOF'
frontend: add firebase dependency

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 13: Create `nasrudin-frontend/src/lib/firebase.ts`

**Files:**
- Create: `nasrudin-frontend/src/lib/firebase.ts`

- [ ] **Step 1: Write the module**

Write `nasrudin-frontend/src/lib/firebase.ts`:

```ts
/**
 * Firebase Web SDK wrapper. Lazy-init so SSR (TanStack Start) doesn't try
 * to construct the Firebase app on the server. All exports are
 * browser-only — call them from inside event handlers or mutations, not
 * from route loaders.
 *
 * Env vars (all required, all public per Firebase's threat model):
 *   VITE_FIREBASE_API_KEY
 *   VITE_FIREBASE_AUTH_DOMAIN
 *   VITE_FIREBASE_PROJECT_ID
 *   VITE_FIREBASE_STORAGE_BUCKET
 *   VITE_FIREBASE_MESSAGING_SENDER_ID
 *   VITE_FIREBASE_APP_ID
 */

import { type FirebaseApp, getApps, initializeApp } from 'firebase/app';
import {
  GoogleAuthProvider,
  type Auth,
  type UserCredential,
  createUserWithEmailAndPassword,
  getAuth,
  sendEmailVerification,
  sendPasswordResetEmail,
  signInWithEmailAndPassword,
  signInWithPopup,
  signOut as fbSignOut,
} from 'firebase/auth';

let appSingleton: FirebaseApp | undefined;

function envVar(name: string): string {
  const v = import.meta.env[name] as string | undefined;
  if (!v) throw new Error(`Missing env var: ${name}`);
  return v;
}

function getFirebaseApp(): FirebaseApp {
  if (typeof window === 'undefined') {
    throw new Error('Firebase Web SDK is browser-only');
  }
  if (appSingleton) return appSingleton;
  const existing = getApps();
  if (existing.length > 0) {
    appSingleton = existing[0];
    return appSingleton;
  }
  appSingleton = initializeApp({
    apiKey: envVar('VITE_FIREBASE_API_KEY'),
    authDomain: envVar('VITE_FIREBASE_AUTH_DOMAIN'),
    projectId: envVar('VITE_FIREBASE_PROJECT_ID'),
    storageBucket: envVar('VITE_FIREBASE_STORAGE_BUCKET'),
    messagingSenderId: envVar('VITE_FIREBASE_MESSAGING_SENDER_ID'),
    appId: envVar('VITE_FIREBASE_APP_ID'),
  });
  return appSingleton;
}

function getFirebaseAuth(): Auth {
  return getAuth(getFirebaseApp());
}

export async function signInWithEmail(
  email: string,
  password: string,
): Promise<UserCredential> {
  return signInWithEmailAndPassword(getFirebaseAuth(), email, password);
}

export async function signUpWithEmail(
  email: string,
  password: string,
): Promise<UserCredential> {
  return createUserWithEmailAndPassword(getFirebaseAuth(), email, password);
}

export async function signInWithGoogle(): Promise<UserCredential> {
  const provider = new GoogleAuthProvider();
  return signInWithPopup(getFirebaseAuth(), provider);
}

export async function sendPasswordReset(email: string): Promise<void> {
  return sendPasswordResetEmail(getFirebaseAuth(), email);
}

export async function sendVerificationEmail(): Promise<void> {
  const user = getFirebaseAuth().currentUser;
  if (!user) throw new Error('Not signed in');
  return sendEmailVerification(user);
}

export async function firebaseSignOut(): Promise<void> {
  return fbSignOut(getFirebaseAuth());
}

/**
 * Returns a fresh ID token (refreshed if near expiry). Throws if no user
 * is signed in.
 */
export async function getCurrentIdToken(): Promise<string> {
  const user = getFirebaseAuth().currentUser;
  if (!user) throw new Error('Not signed in');
  return user.getIdToken(/* forceRefresh */ false);
}

/**
 * Map Firebase error codes to user-facing messages. Used by hooks /
 * forms to render inline errors.
 */
export function firebaseErrorMessage(err: unknown): string {
  // Firebase throws errors with a `code` field like 'auth/invalid-credential'.
  const code = (err as { code?: string } | null)?.code;
  switch (code) {
    case 'auth/invalid-credential':
    case 'auth/wrong-password':
    case 'auth/user-not-found':
      return 'Email or password is incorrect.';
    case 'auth/email-already-in-use':
      return 'That email already has an account. Try signing in instead.';
    case 'auth/weak-password':
      return 'Password is too weak. Use at least 8 characters.';
    case 'auth/invalid-email':
      return 'That email address looks invalid.';
    case 'auth/too-many-requests':
      return 'Too many attempts. Try again in a few minutes.';
    case 'auth/popup-closed-by-user':
    case 'auth/cancelled-popup-request':
      return 'Sign-in cancelled.';
    case 'auth/network-request-failed':
      return 'Network error. Check your connection and try again.';
    default:
      return (err as Error)?.message ?? 'Sign-in failed.';
  }
}
```

- [ ] **Step 2: Type-check**

Run: `pnpm -C nasrudin-frontend exec tsc --noEmit`
Expected: no errors.

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/lib/firebase.ts
git commit -m "$(cat <<'EOF'
frontend: lib/firebase.ts — Web SDK wrapper

Lazy-init keeps SSR safe. Exports signIn/signUp/Google/reset/verify/signOut
helpers + getCurrentIdToken + firebaseErrorMessage code mapping.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 14: Frontend — rewrite auth hooks in `lib/queries.ts`

**Files:**
- Modify: `nasrudin-frontend/src/lib/queries.ts`

- [ ] **Step 1: Update imports**

Edit `nasrudin-frontend/src/lib/queries.ts`. Replace the `import { apiFetch, isApiError } from './api';` line and the auth-related types in the type-import block. The new top of the file:

```ts
import { useMutation, useQuery, useQueryClient } from '@tanstack/react-query';
import { apiFetch, isApiError } from './api';
import {
  firebaseSignOut,
  getCurrentIdToken,
  sendPasswordReset,
  sendVerificationEmail,
  signInWithEmail,
  signInWithGoogle,
  signUpWithEmail,
} from './firebase';
import type {
  // ... keep all the existing imports unchanged ...
} from './types';
```

(The exact `import type` block depends on what's currently imported; leave it untouched and just add the firebase imports above.)

- [ ] **Step 2: Replace `useLogin`, `useRegister`, `useLogout`; add new hooks**

In `lib/queries.ts`, find the `// --- auth ---` section and replace it (delete `useLogin`, `useRegister`, `useLogout` and add the new hooks):

```ts
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

/**
 * Sign in with email + password. Calls Firebase, then exchanges the ID
 * token for a session cookie via POST /api/auth/firebase-session. The
 * `useMe` query is invalidated so the new identity propagates.
 */
export function useLogin() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async (creds: { email: string; password: string }) => {
      await signInWithEmail(creds.email, creds.password);
      const idToken = await getCurrentIdToken();
      return apiFetch<AuthUser>('/api/auth/firebase-session', {
        method: 'POST',
        body: JSON.stringify({ id_token: idToken }),
      });
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

/**
 * Create a new account with email + password. Sends the verification
 * email automatically. The session-exchange call will return 403
 * `email_not_verified` (correct behavior — the form catches this and
 * tells the user to verify their email before they can sign in).
 */
export function useRegister() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async (input: { email: string; password: string }) => {
      await signUpWithEmail(input.email, input.password);
      await sendVerificationEmail();
      // Try to exchange — backend will 403 because email isn't verified
      // yet. We let the form surface that to the user.
      const idToken = await getCurrentIdToken();
      try {
        return await apiFetch<AuthUser>('/api/auth/firebase-session', {
          method: 'POST',
          body: JSON.stringify({ id_token: idToken }),
        });
      } catch (e) {
        if (
          isApiError(e) &&
          e.status === 403 &&
          (e.body as { error?: string } | null)?.error === 'email_not_verified'
        ) {
          // Expected — frontend renders the verification alert.
          return null;
        }
        throw e;
      }
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

/** Sign in with Google (popup). Same exchange pattern as useLogin. */
export function useGoogleLogin() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async () => {
      await signInWithGoogle();
      const idToken = await getCurrentIdToken();
      return apiFetch<AuthUser>('/api/auth/firebase-session', {
        method: 'POST',
        body: JSON.stringify({ id_token: idToken }),
      });
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

/** Sign out from both Firebase and the backend session. */
export function useLogout() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async () => {
      // Sign out of Firebase first; even if the backend logout fails,
      // the user has been disconnected client-side.
      await firebaseSignOut();
      try {
        await apiFetch<{ logged_out: true }>('/api/auth/logout', { method: 'POST' });
      } catch (e) {
        // 401 is expected if the session was already cleared.
        if (!isApiError(e) || e.status !== 401) throw e;
      }
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

/** Trigger Firebase to send a password-reset email. Server is not involved. */
export function useResetPassword() {
  return useMutation({
    mutationFn: (email: string) => sendPasswordReset(email),
  });
}

/** Re-send the verification email to the currently signed-in Firebase user. */
export function useResendVerification() {
  return useMutation({
    mutationFn: () => sendVerificationEmail(),
  });
}
```

- [ ] **Step 3: Update `AuthUser` type to match the new backend shape**

Edit `nasrudin-frontend/src/lib/types.ts`. Find the `AuthUser` interface and update it to drop `password_hash` (was never in the type but kept for completeness) and add `firebase_uid`:

```ts
export interface AuthUser {
  id: string;
  email: string;
  display_name: string | null;
  created_at: string;
  firebase_uid: string;
}
```

(If the existing `AuthUser` already has different fields, keep what's there but add `firebase_uid: string` and remove any `password_hash` field if present.)

- [ ] **Step 4: Type-check**

Run: `pnpm -C nasrudin-frontend exec tsc --noEmit`
Expected: no errors.

- [ ] **Step 5: Commit**

```bash
git add nasrudin-frontend/src/lib/queries.ts nasrudin-frontend/src/lib/types.ts
git commit -m "$(cat <<'EOF'
frontend: auth hooks via Firebase Web SDK

useLogin/useRegister/useLogout call Firebase, then exchange the resulting
ID token for a session cookie via POST /api/auth/firebase-session.
Adds useGoogleLogin, useResetPassword, useResendVerification. AuthUser
type gains firebase_uid.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 15: Frontend — rewrite `AuthForm.tsx` for Google + Forgot-password + Verification alert

**Files:**
- Modify: `nasrudin-frontend/src/components/auth/AuthForm.tsx`
- Modify: `nasrudin-frontend/src/styles/platform.css`

- [ ] **Step 1: Swap `.oauth-primary` button to look Google-style**

Edit `nasrudin-frontend/src/styles/platform.css`. Find `.oauth-primary` (added in the previous round) and replace its color tokens to match Google's white-on-dark recommended button:

```css
.oauth-primary {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 10px;
  width: 100%;
  padding: 12px 16px;
  border-radius: var(--radius-md);
  border: 1px solid var(--ink-200);
  background: var(--paper-50);
  color: var(--ink-900);
  font-size: 15px;
  font-weight: 500;
  text-decoration: none;
  cursor: pointer;
  transition: background 120ms ease, border-color 120ms ease;
  font-family: var(--font-sans);
}
.oauth-primary:hover {
  background: var(--paper-100);
  border-color: var(--ink-300);
}
.oauth-primary:disabled {
  opacity: 0.6;
  cursor: not-allowed;
}
.oauth-primary svg {
  width: 18px;
  height: 18px;
}
```

(If `--ink-300` doesn't exist as a token, fall back to `--ink-200`.)

- [ ] **Step 2: Rewrite `AuthForm.tsx`**

Replace the entire contents of `nasrudin-frontend/src/components/auth/AuthForm.tsx` with:

```tsx
import { useNavigate } from '@tanstack/react-router';
import { type FormEvent, useState } from 'react';
import { firebaseErrorMessage } from '~/lib/firebase';
import {
  useGoogleLogin,
  useLogin,
  useRegister,
  useResetPassword,
} from '~/lib/queries';

type Mode = 'signin' | 'signup' | 'forgot' | 'reset-sent' | 'verify-sent';

export function AuthForm() {
  const [mode, setMode] = useState<Mode>('signin');
  const [email, setEmail] = useState('');
  const [password, setPassword] = useState('');
  const [error, setError] = useState<string | null>(null);

  const login = useLogin();
  const register = useRegister();
  const google = useGoogleLogin();
  const reset = useResetPassword();
  const navigate = useNavigate();

  async function onGoogle() {
    setError(null);
    try {
      await google.mutateAsync();
      await navigate({ to: '/profile' });
    } catch (e) {
      setError(firebaseErrorMessage(e));
    }
  }

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    try {
      if (mode === 'signin') {
        await login.mutateAsync({ email, password });
        await navigate({ to: '/profile' });
      } else if (mode === 'signup') {
        const result = await register.mutateAsync({ email, password });
        if (result === null) {
          // Registration succeeded but email isn't verified yet — show alert.
          setMode('verify-sent');
        } else {
          await navigate({ to: '/profile' });
        }
      } else if (mode === 'forgot') {
        await reset.mutateAsync(email);
        setMode('reset-sent');
      }
    } catch (err) {
      setError(firebaseErrorMessage(err));
    }
  }

  const submitting =
    login.isPending || register.isPending || reset.isPending || google.isPending;

  return (
    <form className="auth-form-wrap" onSubmit={onSubmit}>
      <h1>
        {mode === 'signin' && 'Welcome back.'}
        {mode === 'signup' && 'Join the corpus.'}
        {mode === 'forgot' && 'Reset your password.'}
        {mode === 'reset-sent' && 'Check your inbox.'}
        {mode === 'verify-sent' && 'Verify your email.'}
      </h1>
      <p className="lede">
        {mode === 'signin' && 'Sign in to your library, citations, and targeted searches.'}
        {mode === 'signup' && 'Free for individual academics. No card required.'}
        {mode === 'forgot' && "We'll email you a link to set a new password."}
        {mode === 'reset-sent' &&
          `We sent a password-reset link to ${email}. The link expires in 1 hour.`}
        {mode === 'verify-sent' &&
          `We sent a verification link to ${email}. Click it, then sign in.`}
      </p>

      {(mode === 'signin' || mode === 'signup') && (
        <>
          <button
            type="button"
            className="oauth-primary"
            onClick={onGoogle}
            disabled={submitting}
          >
            <GoogleSvg />
            Continue with Google
          </button>
          <div className="divider">or</div>
          <div className="auth-tabs">
            <button
              type="button"
              className={`auth-tab ${mode === 'signin' ? 'active' : ''}`}
              onClick={() => {
                setMode('signin');
                setError(null);
              }}
            >
              Sign in
            </button>
            <button
              type="button"
              className={`auth-tab ${mode === 'signup' ? 'active' : ''}`}
              onClick={() => {
                setMode('signup');
                setError(null);
              }}
            >
              Create account
            </button>
          </div>
        </>
      )}

      {(mode === 'signin' || mode === 'signup' || mode === 'forgot') && (
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
      )}

      {(mode === 'signin' || mode === 'signup') && (
        <div className="field">
          <label htmlFor="password">Password</label>
          <input
            id="password"
            type="password"
            required
            autoComplete={mode === 'signin' ? 'current-password' : 'new-password'}
            minLength={8}
            value={password}
            onChange={(e) => setPassword(e.target.value)}
            placeholder="••••••••••••"
          />
          {mode === 'signin' && (
            <button
              type="button"
              onClick={() => {
                setMode('forgot');
                setError(null);
              }}
              style={{
                background: 'none',
                border: 'none',
                color: 'var(--ink-500)',
                fontSize: 12,
                cursor: 'pointer',
                marginTop: 6,
                padding: 0,
              }}
            >
              Forgot password?
            </button>
          )}
        </div>
      )}

      {error && (
        <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginBottom: 12 }}>
          {error}
        </div>
      )}

      {(mode === 'signin' || mode === 'signup' || mode === 'forgot') && (
        <button
          className="btn btn-primary"
          type="submit"
          disabled={submitting}
          style={{ width: '100%', justifyContent: 'center', marginTop: 8 }}
        >
          {mode === 'signin' && (submitting ? 'Signing in…' : 'Sign in')}
          {mode === 'signup' && (submitting ? 'Creating…' : 'Create free account')}
          {mode === 'forgot' && (submitting ? 'Sending…' : 'Send reset link')}
        </button>
      )}

      {(mode === 'forgot' || mode === 'reset-sent' || mode === 'verify-sent') && (
        <button
          type="button"
          onClick={() => {
            setMode('signin');
            setError(null);
          }}
          style={{
            background: 'none',
            border: 'none',
            color: 'var(--ink-500)',
            fontSize: 13,
            cursor: 'pointer',
            marginTop: 16,
          }}
        >
          ← Back to sign in
        </button>
      )}

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
}

function GoogleSvg() {
  return (
    <svg viewBox="0 0 18 18" aria-hidden="true">
      <path
        fill="#4285F4"
        d="M17.64 9.205c0-.639-.057-1.252-.164-1.841H9v3.481h4.844a4.14 4.14 0 0 1-1.796 2.716v2.259h2.908c1.702-1.567 2.684-3.875 2.684-6.615z"
      />
      <path
        fill="#34A853"
        d="M9 18c2.43 0 4.467-.806 5.956-2.18l-2.908-2.259c-.806.54-1.837.86-3.048.86-2.344 0-4.328-1.584-5.036-3.711H.957v2.332A8.997 8.997 0 0 0 9 18z"
      />
      <path
        fill="#FBBC05"
        d="M3.964 10.71A5.41 5.41 0 0 1 3.682 9c0-.593.102-1.17.282-1.71V4.958H.957A8.996 8.996 0 0 0 0 9c0 1.452.348 2.827.957 4.042l3.007-2.332z"
      />
      <path
        fill="#EA4335"
        d="M9 3.58c1.321 0 2.508.454 3.44 1.345l2.582-2.58C13.463.891 11.426 0 9 0A8.997 8.997 0 0 0 .957 4.958L3.964 7.29C4.672 5.163 6.656 3.58 9 3.58z"
      />
    </svg>
  );
}
```

- [ ] **Step 3: Type-check**

Run: `pnpm -C nasrudin-frontend exec tsc --noEmit`
Expected: no errors.

- [ ] **Step 4: Manual smoke test**

Run: `pnpm -C nasrudin-frontend dev`
Open: `http://localhost:3000/signin`

Confirm visually:
- "Continue with Google" button at the top (white background, full width, Google G mark on the left).
- `or` divider.
- Sign in / Create account tabs.
- Email + password fields.
- "Forgot password?" small link below the password field.
- No GitHub button anywhere.
- No "Coming soon" disabled buttons.

(Buttons won't actually work until `VITE_FIREBASE_*` env vars are populated — Task 16.)

- [ ] **Step 5: Commit**

```bash
git add nasrudin-frontend/src/components/auth/AuthForm.tsx \
        nasrudin-frontend/src/styles/platform.css
git commit -m "$(cat <<'EOF'
frontend: AuthForm rewrite for Firebase (Google + forgot-password + verify alert)

Mode state machine (signin/signup/forgot/reset-sent/verify-sent) drives
the form. Continue-with-Google is the primary CTA above email/password.
Forgot password triggers Firebase reset email; signup triggers
verification email and shows an inline alert.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 16: Update `.env.example` — remove GitHub OAuth, add Firebase

**Files:**
- Modify: `.env.example`

- [ ] **Step 1: Replace the GitHub OAuth block**

Edit `.env.example`. Find the `# ── GitHub OAuth ──` block (added in the previous round) and replace it entirely with:

```sh
# ── Firebase Auth ─────────────────────────────────────────
# Backend: only the project ID is needed to verify Firebase ID tokens.
# When unset, /api/auth/firebase-session returns 503 and the rest of the
# API works (sign-in is unavailable, but worker keys and live API keys
# continue to function).
FIREBASE_PROJECT_ID=nasrudin

# Frontend (VITE_*): public per Firebase's threat model — safe in the bundle.
# Get them from console.firebase.google.com → Project settings → General →
# Your apps → Web → Firebase SDK snippet → Config.
VITE_FIREBASE_API_KEY=
VITE_FIREBASE_AUTH_DOMAIN=
VITE_FIREBASE_PROJECT_ID=
VITE_FIREBASE_STORAGE_BUCKET=
VITE_FIREBASE_MESSAGING_SENDER_ID=
VITE_FIREBASE_APP_ID=
```

- [ ] **Step 2: Commit**

```bash
git add .env.example
git commit -m "$(cat <<'EOF'
config: .env.example — Firebase replaces GitHub OAuth

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 17: Update `deploy/README.md` with Firebase setup instructions

**Files:**
- Modify: `deploy/README.md`

- [ ] **Step 1: Replace the GitHub OAuth section**

Edit `deploy/README.md`. Find the `## GitHub OAuth (sign-in)` section and replace the entire section with:

```markdown
## Firebase Auth (sign-in)

Sign-in is powered by Firebase Authentication. To bring up a fresh
environment:

1. Visit <https://console.firebase.google.com> → **Add project** → name it
   (e.g. `nasrudin`, `nasrudin-staging`).
2. **Authentication → Get started** → enable two providers:
   - **Email/Password** — leave "Email link (passwordless sign-in)" off.
   - **Google** — pick a support email from the dropdown.
3. **Project settings → General → Your apps → Add app → Web** → register
   the web app. Copy the Firebase SDK config snippet — populate the
   `VITE_FIREBASE_*` env vars from it.
4. **Project settings → General → Project ID** — copy → set
   `FIREBASE_PROJECT_ID` on the backend.
5. **Authentication → Settings → Authorized domains** — add the production
   domain (e.g. `nasrudin.app`) and `localhost` for dev.
6. **Authentication → Templates → Email address verification** and
   **Password reset** — customize subject and body so emails read "Nasrudin"
   rather than the default Firebase project name.

The API logs `Firebase Auth configured` at startup when `FIREBASE_PROJECT_ID`
is set; otherwise `/api/auth/firebase-session` returns 503 and the rest of
the API works (worker keys and live API keys continue to function).

The first sign-in attempt after `FIREBASE_PROJECT_ID` is set fetches
Google's signing keys (one HTTP round-trip, ~200ms). The API pre-warms
the cache at boot in the background; failures are logged and recovery is
automatic on next sign-in.
```

- [ ] **Step 2: Commit**

```bash
git add deploy/README.md
git commit -m "$(cat <<'EOF'
docs: deploy README — Firebase setup replaces GitHub OAuth

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Final verification

- [ ] **Build everything**

Run: `cd engine && cargo build --workspace`
Expected: clean build.

- [ ] **Type-check the frontend**

Run: `pnpm -C nasrudin-frontend exec tsc --noEmit`
Expected: no errors.

- [ ] **Run all new tests on a fresh test DB**

Run:
```bash
PGPASSWORD=physics_dev psql -h 127.0.0.1 -U physics -d postgres -c "DROP DATABASE IF EXISTS physics_generator_test;"
PGPASSWORD=physics_dev psql -h 127.0.0.1 -U physics -d postgres -c "CREATE DATABASE physics_generator_test;"
TEST_DATABASE_URL="postgres://physics:physics_dev@127.0.0.1:5432/physics_generator_test" \
  cargo test -p physics-api --test firebase_verify --test firebase_session -- --test-threads=1
```
Expected: all 12 tests pass.

- [ ] **Manual end-to-end test (requires a Firebase project)**

If the user has populated `FIREBASE_PROJECT_ID` and `VITE_FIREBASE_*` env vars:

1. Start the API (`cd engine && DATABASE_URL=... FIREBASE_PROJECT_ID=nasrudin cargo run -p physics-api`) and the frontend (`pnpm -C nasrudin-frontend dev`).
2. Visit `/signin`.
3. Click "Continue with Google" → consent → land on `/profile` authenticated.
4. Sign out → confirm `/api/auth/me` returns 401.
5. Click Create account → enter `dev+1@example.com` and a password → see "verify your email" alert → check inbox → click link.
6. Return, sign in with the same email + password → land on `/profile`.
7. Sign out → click Forgot password? → enter email → see "check your inbox" → click reset link → set new password → sign in.

If everything works: ship it.

- [ ] **Push and (optional) PR**

```bash
git push origin main
```

(Or if you'd rather review the diff first, push to a feature branch.)
