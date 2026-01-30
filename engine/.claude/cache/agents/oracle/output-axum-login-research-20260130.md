# Research Report: axum-login Crate

Generated: 2026-01-30

## Summary

`axum-login` v0.18.0 provides session-based authentication and authorization as tower middleware for Axum. It uses `tower-sessions` for session management and requires implementing two traits (`AuthUser`, `AuthnBackend`) to integrate with any user backend. A SeaORM session store exists as a separate community crate (`tower-sessions-seaorm-store`), making it viable for your `engine/crates/pg/` SeaORM-based architecture.

---

## Questions Answered

### Q1: Current Latest Version Number

**Answer:** `0.18.0`, released 2025-07-20. This version added support for Axum 0.8 and the new `Require` builder API.

**Source:** [crates.io/crates/axum-login](https://crates.io/crates/axum-login), [docs.rs/axum-login/0.18.0](https://docs.rs/crate/axum-login/latest)

**Confidence:** High

---

### Q2: How the `AuthnBackend` Trait Works

**Answer:** Two traits must be implemented: `AuthUser` and `AuthnBackend`.

#### `AuthUser` Trait

```rust
pub trait AuthUser: Debug + Clone + Send + Sync {
    /// The ID type (e.g., i64, Uuid)
    type Id: Debug + Display + Clone + Send + Sync + Serialize + for<'de> Deserialize<'de>;

    /// Return the user's unique identifier
    fn id(&self) -> Self::Id;

    /// Return a hash used to validate the session.
    /// Changing this value (e.g., password change) invalidates the session.
    fn session_auth_hash(&self) -> &[u8];
}
```

#### `AuthnBackend` Trait

```rust
#[async_trait]
pub trait AuthnBackend {
    /// The user type (must implement AuthUser)
    type User: AuthUser;

    /// The credentials type (your login form struct)
    type Credentials: Send + Sync;

    /// The error type
    type Error: Send + Sync;

    /// Authenticate credentials against the backend.
    /// Returns Ok(Some(user)) on success, Ok(None) on bad credentials.
    async fn authenticate(
        &self,
        creds: Self::Credentials,
    ) -> Result<Option<Self::User>, Self::Error>;

    /// Load a user by their ID (called on each request to rehydrate from session).
    async fn get_user(
        &self,
        user_id: &UserId<Self>,
    ) -> Result<Option<Self::User>, Self::Error>;
}
```

#### Optional: `AuthzBackend` Trait

For authorization (permissions), implement `AuthzBackend` which supports both user-level and group-level permissions.

**Source:** [docs.rs/axum-login](https://docs.rs/axum-login), [AuthUser trait](https://docs.rs/axum-login/latest/axum_login/trait.AuthUser.html)

**Confidence:** High

---

### Q3: Session Backend

**Answer:** `axum-login` uses `tower-sessions` for session management. It re-exports tower-sessions types under `axum_login::tower_sessions`, so you often don't need to add `tower-sessions` as a separate direct dependency.

Built-in session stores from `tower-sessions`:
- `MemoryStore` (built-in, for development)
- Redis
- SQLite
- PostgreSQL
- MySQL

Session store crates:
- `tower-sessions-sqlx-store` (uses SQLx directly) - features: `sqlite`, `postgres`, `mysql`
- `tower-sessions-seaorm-store` (uses SeaORM) - features: `postgres`, `sqlite`

**Source:** [tower-sessions GitHub](https://github.com/maxcountryman/tower-sessions), [tower-sessions-seaorm-store docs](https://docs.rs/tower-sessions-seaorm-store/latest/tower_sessions_seaorm_store/)

**Confidence:** High

---

### Q4: Setting Up the Middleware Layer

**Answer:** The setup follows this pattern:

```rust
use axum::{routing::get, Router};
use axum_login::{
    login_required,
    tower_sessions::{MemoryStore, SessionManagerLayer},
    AuthManagerLayerBuilder,
};

// 1. Create session store (MemoryStore for dev, SqlxStore/SeaOrmStore for prod)
let session_store = MemoryStore::default();

// 2. Create session management layer
let session_layer = SessionManagerLayer::new(session_store);

// 3. Create your auth backend (e.g., wrapping a DB pool)
let backend = Backend::new(db_pool);

// 4. Build the auth layer
let auth_layer = AuthManagerLayerBuilder::new(backend, session_layer).build();

// 5. Build the router with protected routes
let app = Router::new()
    // Protected routes (above the login_required layer)
    .route("/dashboard", get(dashboard_handler))
    .route("/settings", get(settings_handler))
    .route_layer(login_required!(Backend, login_url = "/login"))
    // Public routes (below the login_required layer)
    .route("/login", get(login_page).post(login_handler))
    .route("/", get(index_handler))
    // Apply the auth layer to everything
    .layer(auth_layer);
```

**Key points:**
- Use `.route_layer()` (not `.layer()`) for `login_required!` so it only applies to routes defined above it
- The `auth_layer` must wrap all routes that need `AuthSession`
- Layer ordering matters: `auth_layer` is outermost

#### New in v0.18: `Require` Builder (alternative to macros)

```rust
use axum_login::require::Require;
use axum_login::require::handler::RedirectHandler;

let guard = Require::<Backend>::builder()
    .unauthenticated(RedirectHandler::new().login_url("/login"))
    .build();

let app = Router::new()
    .route("/protected", get(handler))
    .route_layer(guard)
    .layer(auth_layer);
```

Enable with: `axum-login = { version = "0.18.0", features = ["require-builder"] }`

**Source:** [docs.rs/axum-login](https://docs.rs/axum-login), [GitHub discussions #154](https://github.com/maxcountryman/axum-login/discussions/154)

**Confidence:** High

---

### Q5: Complete Working Example (Email/Password Auth with DB Backend)

**Answer:** Based on the official SQLite example, adapted for PostgreSQL:

#### Cargo.toml

```toml
[dependencies]
axum = "0.8"
axum-login = "0.18"
password-auth = "1.0"
serde = { version = "1", features = ["derive"] }
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres"] }
tokio = { version = "1", features = ["full"] }
tower-sessions = { version = "0.14", default-features = false }
tower-sessions-sqlx-store = { version = "0.15", features = ["postgres"] }
# OR for SeaORM:
# tower-sessions-seaorm-store = { version = "0.1", features = ["postgres", "migration"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
```

#### User Model (`users.rs`)

```rust
use axum_login::{AuthUser, AuthnBackend, UserId};
use password_auth::verify_password;
use serde::{Deserialize, Serialize};
use sqlx::{FromRow, PgPool};
use tokio::task;

// ---------- User ----------

#[derive(Clone, Serialize, Deserialize, FromRow)]
pub struct User {
    pub id: i64,
    pub email: String,
    password_hash: String,
}

// Avoid leaking password hash in logs
impl std::fmt::Debug for User {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("User")
            .field("id", &self.id)
            .field("email", &self.email)
            .field("password_hash", &"[redacted]")
            .finish()
    }
}

impl AuthUser for User {
    type Id = i64;

    fn id(&self) -> Self::Id {
        self.id
    }

    /// Changing the password invalidates existing sessions.
    fn session_auth_hash(&self) -> &[u8] {
        self.password_hash.as_bytes()
    }
}

// ---------- Credentials ----------

#[derive(Debug, Clone, Deserialize)]
pub struct Credentials {
    pub email: String,
    pub password: String,
    /// Where to redirect after login
    pub next: Option<String>,
}

// ---------- Backend ----------

#[derive(Debug, Clone)]
pub struct Backend {
    db: PgPool,
}

impl Backend {
    pub fn new(db: PgPool) -> Self {
        Self { db }
    }
}

#[axum_login::async_trait]
impl AuthnBackend for Backend {
    type User = User;
    type Credentials = Credentials;
    type Error = sqlx::Error;

    async fn authenticate(
        &self,
        creds: Self::Credentials,
    ) -> Result<Option<Self::User>, Self::Error> {
        let user: Option<User> = sqlx::query_as(
            "SELECT id, email, password_hash FROM users WHERE email = $1"
        )
        .bind(&creds.email)
        .fetch_optional(&self.db)
        .await?;

        // Argon2 verification is CPU-intensive; run off the async runtime
        task::spawn_blocking(|| {
            Ok(user.filter(|user| {
                verify_password(creds.password, &user.password_hash).is_ok()
            }))
        })
        .await
        .expect("panic in verify_password")
    }

    async fn get_user(
        &self,
        user_id: &UserId<Self>,
    ) -> Result<Option<Self::User>, Self::Error> {
        sqlx::query_as("SELECT id, email, password_hash FROM users WHERE id = $1")
            .bind(user_id)
            .fetch_optional(&self.db)
            .await
    }
}

/// Convenience alias
pub type AuthSession = axum_login::AuthSession<Backend>;
```

#### Auth Handlers (`auth.rs`)

```rust
use axum::{
    http::StatusCode,
    response::{IntoResponse, Redirect},
    Form,
};

use crate::users::{AuthSession, Credentials};

pub async fn login_page() -> impl IntoResponse {
    // Return your login HTML/template here
    axum::response::Html(r#"
        <form method="post" action="/login">
            <input type="email" name="email" placeholder="Email" required />
            <input type="password" name="password" placeholder="Password" required />
            <input type="hidden" name="next" value="/dashboard" />
            <button type="submit">Log In</button>
        </form>
    "#)
}

pub async fn login_handler(
    mut auth_session: AuthSession,
    Form(creds): Form<Credentials>,
) -> impl IntoResponse {
    let user = match auth_session.authenticate(creds.clone()).await {
        Ok(Some(user)) => user,
        Ok(None) => {
            return StatusCode::UNAUTHORIZED.into_response();
        }
        Err(_) => {
            return StatusCode::INTERNAL_SERVER_ERROR.into_response();
        }
    };

    if auth_session.login(&user).await.is_err() {
        return StatusCode::INTERNAL_SERVER_ERROR.into_response();
    }

    let next = creds.next.unwrap_or_else(|| "/dashboard".to_string());
    Redirect::to(&next).into_response()
}

pub async fn logout_handler(mut auth_session: AuthSession) -> impl IntoResponse {
    match auth_session.logout().await {
        Ok(_) => Redirect::to("/login").into_response(),
        Err(_) => StatusCode::INTERNAL_SERVER_ERROR.into_response(),
    }
}
```

#### Registration Helper

```rust
use password_auth::generate_hash;

pub async fn register_user(
    pool: &PgPool,
    email: &str,
    password: &str,
) -> Result<User, sqlx::Error> {
    // generate_hash defaults to Argon2 with OWASP-recommended params
    let password_hash = generate_hash(password);

    sqlx::query_as(
        "INSERT INTO users (email, password_hash) VALUES ($1, $2) RETURNING id, email, password_hash"
    )
    .bind(email)
    .bind(&password_hash)
    .fetch_one(pool)
    .await
}
```

#### Application Setup (`main.rs`)

```rust
use axum::{routing::{get, post}, Router};
use axum_login::{
    login_required,
    tower_sessions::SessionManagerLayer,
    AuthManagerLayerBuilder,
};
use sqlx::postgres::PgPoolOptions;
use tower_sessions_sqlx_store::PostgresStore;

mod auth;
mod users;

use users::Backend;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. Database pool
    let pool = PgPoolOptions::new()
        .max_connections(5)
        .connect("postgres://user:pass@localhost/mydb")
        .await?;

    // 2. Session store (PostgreSQL-backed)
    let session_store = PostgresStore::new(pool.clone());
    session_store.migrate().await?;

    let session_layer = SessionManagerLayer::new(session_store)
        .with_secure(false); // set true in production with HTTPS

    // 3. Auth backend
    let backend = Backend::new(pool);

    // 4. Auth middleware layer
    let auth_layer = AuthManagerLayerBuilder::new(backend, session_layer).build();

    // 5. Router
    let app = Router::new()
        // Protected routes
        .route("/dashboard", get(|| async { "Welcome to the dashboard!" }))
        .route("/logout", post(auth::logout_handler))
        .route_layer(login_required!(Backend, login_url = "/login"))
        // Public routes
        .route("/login", get(auth::login_page).post(auth::login_handler))
        .route("/", get(|| async { "Home page" }))
        // Apply auth layer
        .layer(auth_layer);

    // 6. Serve
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    axum::serve(listener, app).await?;

    Ok(())
}
```

**Source:** [Official SQLite example users.rs](https://github.com/maxcountryman/axum-login/blob/main/examples/sqlite/src/users.rs), [Official SQLite example main.rs](https://github.com/maxcountryman/axum-login/blob/main/examples/sqlite/src/main.rs)

**Confidence:** High (adapted from official example, PostgreSQL substituted for SQLite)

---

### Q6: Companion Crates Needed

**Answer:**

| Crate | Version | Purpose |
|-------|---------|---------|
| `axum-login` | 0.18.0 | Auth middleware (re-exports tower-sessions) |
| `tower-sessions` | 0.14.x | Session management (often not needed as direct dep) |
| `tower-sessions-sqlx-store` | 0.15.0 | SQLx-backed session store (sqlite/postgres/mysql) |
| `tower-sessions-seaorm-store` | 0.1.x | SeaORM-backed session store (postgres/sqlite) |
| `password-auth` | 1.0.0 | Argon2 password hashing (generate + verify) |
| `tokio` | 1.x | Async runtime (with `full` feature) |
| `sqlx` | 0.8.x | Database driver (if using sqlx backend) |

**Note on version compatibility:** `axum-login` 0.18.0 re-exports `tower-sessions` types. The exact version of `tower-sessions` and `tower-sessions-sqlx-store` you need depends on what `axum-login` 0.18 depends on internally. Check `axum-login`'s `Cargo.toml` for the pinned `tower-sessions` version. The example used `tower-sessions = "0.10"` and `tower-sessions-sqlx-store = "0.10"`, but newer versions of these crates exist (0.14 and 0.15 respectively). You may need to match versions.

**Source:** [crates.io](https://crates.io/crates/axum-login), [tower-sessions-sqlx-store](https://crates.io/crates/tower-sessions-sqlx-store)

**Confidence:** Medium (version pinning between axum-login and tower-sessions-sqlx-store needs verification at compile time)

---

### Q7: SeaORM Compatibility

**Answer:** YES, it works with SeaORM. The `tower-sessions-seaorm-store` crate provides a `PostgresStore` (and SQLite store) that uses `sea_orm::DbConn` instead of `sqlx::PgPool`.

#### Setup with SeaORM

```toml
[dependencies]
tower-sessions-seaorm-store = { version = "0.1", features = ["postgres", "migration"] }
sea-orm = { version = "1", features = ["sqlx-postgres", "runtime-tokio-rustls"] }
```

```rust
use sea_orm::Database;
use time::Duration;
use tower_sessions::Expiry;
use tower_sessions_seaorm_store::PostgresStore;

// Connect via SeaORM
let conn = Database::connect("postgres://user:pass@localhost/mydb").await?;

// Create session store
let session_store = PostgresStore::new(conn.clone());
session_store.migrate().await?; // requires "migration" feature

let session_layer = SessionManagerLayer::new(session_store)
    .with_expiry(Expiry::OnInactivity(Duration::days(7)));

// Then use with AuthManagerLayerBuilder as normal
let auth_layer = AuthManagerLayerBuilder::new(backend, session_layer).build();
```

**Important:** The `tower-sessions-seaorm-store` is a community crate (not by the same author as axum-login). It implements the `SessionStore` trait from `tower-sessions`, so it plugs in seamlessly.

**Known issue with sqlx-store + Postgres:** There is a reported deserialization bug with `tower-sessions-sqlx-store` and PostgreSQL where MessagePack encoding causes errors like `"invalid type: sequence, expected u8"`. Workarounds include using `serde_json` instead of `rmp-serde`, or using the SeaORM store which may not have this issue.

**Source:** [tower-sessions-seaorm-store docs](https://docs.rs/tower-sessions-seaorm-store/latest/tower_sessions_seaorm_store/), [crates.io](https://crates.io/crates/tower-sessions-seaorm-store), [GitHub Issue #53](https://github.com/maxcountryman/tower-sessions-stores/issues/53)

**Confidence:** High (for existence and API), Medium (for version compatibility -- verify at compile time)

---

### Q8: The `password-auth` Crate

**Answer:** `password-auth` v1.0.0 from the RustCrypto organization provides a deliberately simple two-function API for password hashing.

#### API

```rust
// Generate a hash (defaults to Argon2 with OWASP-recommended parameters)
let hash: String = password_auth::generate_hash("my_password");

// Verify a password against a stored hash
match password_auth::verify_password("my_password", &stored_hash) {
    Ok(()) => println!("Password correct"),
    Err(_) => println!("Password incorrect"),
}
```

#### Features

| Feature | Default | Description |
|---------|---------|-------------|
| `argon2` | Yes | Argon2 hashing (recommended) |
| `std` | Yes | Standard library support |
| `pbkdf2` | No | PBKDF2 support for legacy hashes |
| `scrypt` | No | Scrypt support for legacy hashes |

#### Key properties:
- `generate_hash` always uses Argon2 (when the `argon2` feature is enabled, which is default)
- `verify_password` can verify hashes from any enabled algorithm (useful for migrating hash algorithms)
- The hash output is a PHC string format (e.g., `$argon2id$v=19$m=19456,t=2,p=1$...`)
- Thread-safe, no global state
- CPU-intensive: always run in `task::spawn_blocking` in async contexts

#### Cargo.toml

```toml
[dependencies]
password-auth = "1.0"
```

**Source:** [docs.rs/password-auth](https://docs.rs/password-auth/latest/password_auth/), [crates.io/crates/password-auth](https://crates.io/crates/password-auth), [GitHub](https://github.com/RustCrypto/password-hashes/tree/master/password-auth)

**Confidence:** High

---

## Comparison Matrix: Session Store Options

| Store | Crate | Backend | Pros | Cons | Use Case |
|-------|-------|---------|------|------|----------|
| `MemoryStore` | built-in (tower-sessions) | In-memory | Zero setup, fast | Lost on restart, no horizontal scaling | Development |
| `PostgresStore` (sqlx) | `tower-sessions-sqlx-store` | PostgreSQL via sqlx | Official, well-tested | Known MessagePack bug with Postgres | SQLx-based apps |
| `SqliteStore` | `tower-sessions-sqlx-store` | SQLite via sqlx | Official, lightweight | Single-node only | Small apps |
| `PostgresStore` (SeaORM) | `tower-sessions-seaorm-store` | PostgreSQL via SeaORM | Works with SeaORM stack | Community crate, less battle-tested | SeaORM-based apps |
| `RedisStore` | `tower-sessions-redis-store` | Redis | Fast, scalable | Extra infrastructure | Production at scale |
| Custom | implement `SessionStore` | Anything | Full control | Must implement yourself | Special needs |

---

## Recommendations

### For This Codebase (`engine/crates/pg/` uses SeaORM)

1. **Use `tower-sessions-seaorm-store`** for session storage since your `pg` crate already uses SeaORM. This avoids adding a parallel sqlx dependency just for sessions. Share the same `sea_orm::DbConn`.

2. **Implement `AuthnBackend` in `engine/crates/api/`** (or a new `auth` crate) with your SeaORM user model. The `authenticate` method queries your `users` table via SeaORM instead of raw sqlx.

3. **Use `password-auth = "1.0"`** for Argon2 hashing. Its two-function API is ideal.

4. **Wrap password verification in `tokio::task::spawn_blocking`** as shown in the official example. Argon2 is deliberately CPU-intensive and will block the async runtime otherwise.

5. **Start with `MemoryStore`** for development, then swap to SeaORM PostgresStore for production. The only change is the store construction.

### Implementation Notes

- `session_auth_hash()` should return the password hash bytes. Changing a password automatically invalidates all sessions for that user.
- The `login_required!` macro uses `.route_layer()`, NOT `.layer()`. Using `.layer()` would also apply to 404 fallbacks and cause confusing errors.
- The `AuthManagerLayerBuilder` auth layer must be the outermost layer wrapping all routes that use `AuthSession`.
- The `Credentials` struct is yours to define -- it just needs `Send + Sync`. You can include `email`, `password`, `next` (redirect URL), or anything else.
- For the known Postgres MessagePack bug with `tower-sessions-sqlx-store`, the SeaORM store may avoid this since it uses a different serialization path. Verify at integration time.
- Version pinning: `axum-login` 0.18 depends on a specific `tower-sessions` version. Let Cargo resolve it, but if you get version conflicts between `tower-sessions-seaorm-store` and `axum-login`'s re-exported `tower-sessions`, you may need to check compatibility.

---

## Sources

1. [axum-login on crates.io](https://crates.io/crates/axum-login) - version info, downloads
2. [axum-login docs.rs](https://docs.rs/axum-login) - API documentation
3. [axum-login GitHub](https://github.com/maxcountryman/axum-login) - source code, examples, README
4. [AuthUser trait docs](https://docs.rs/axum-login/latest/axum_login/trait.AuthUser.html) - trait definition
5. [Official SQLite example users.rs](https://github.com/maxcountryman/axum-login/blob/main/examples/sqlite/src/users.rs) - reference implementation
6. [Official SQLite example main.rs](https://github.com/maxcountryman/axum-login/blob/main/examples/sqlite/src/main.rs) - app setup
7. [tower-sessions GitHub](https://github.com/maxcountryman/tower-sessions) - session middleware
8. [tower-sessions-seaorm-store docs](https://docs.rs/tower-sessions-seaorm-store/latest/tower_sessions_seaorm_store/) - SeaORM session store
9. [tower-sessions-seaorm-store crates.io](https://crates.io/crates/tower-sessions-seaorm-store) - version info
10. [tower-sessions-sqlx-store crates.io](https://crates.io/crates/tower-sessions-sqlx-store) - SQLx session stores
11. [password-auth docs.rs](https://docs.rs/password-auth/latest/password_auth/) - Argon2 hashing API
12. [password-auth crates.io](https://crates.io/crates/password-auth) - version info
13. [password-auth GitHub](https://github.com/RustCrypto/password-hashes/tree/master/password-auth) - source
14. [GitHub Discussion #154](https://github.com/maxcountryman/axum-login/discussions/154) - route protection patterns
15. [GitHub Issue #53 (tower-sessions-stores)](https://github.com/maxcountryman/tower-sessions-stores/issues/53) - Postgres MessagePack bug
16. [Authentication with Axum blog post](https://mattrighetti.com/2025/05/03/authentication-with-axum) - tutorial

## Open Questions

- Exact `tower-sessions` version that `axum-login` 0.18.0 pins to (check its Cargo.toml at build time)
- Whether `tower-sessions-seaorm-store` 0.1.x is compatible with the tower-sessions version that axum-login 0.18 re-exports (may need version bumps)
- Whether the MessagePack deserialization bug affects the SeaORM store or only the sqlx store
