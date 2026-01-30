//! PostgreSQL storage backend for user accounts, sessions, and worker state.
//!
//! This crate manages the relational data that complements the RocksDB theorem store:
//! user accounts, authentication sessions, saved searches, user preferences,
//! and distributed worker coordination.
//!
//! Uses SeaORM 2 as the PostgreSQL ORM layer.

pub mod entity;
pub mod migrator;
pub mod query;

use anyhow::{Context, Result};
use sea_orm::{ConnectOptions, Database, DatabaseConnection};
use sea_orm_migration::MigratorTrait;
use std::time::Duration;

// Re-export key types for convenience.
pub use entity::workers::WorkerStatus;
pub use migrator::Migrator;
pub use sea_orm;
pub use sea_orm::DatabaseConnection as DbConn;

/// Configuration for the PostgreSQL connection pool.
#[derive(Debug, Clone)]
pub struct PgConfig {
    /// PostgreSQL connection URL (e.g. `postgres://user:pass@localhost:5432/physics_generator`).
    pub database_url: String,
    /// Maximum number of connections in the pool.
    pub max_connections: u32,
    /// Minimum number of idle connections maintained.
    pub min_connections: u32,
    /// Timeout for acquiring a connection from the pool.
    pub connect_timeout: Duration,
    /// Maximum lifetime of a connection before it is recycled.
    pub max_lifetime: Duration,
    /// Enable SQL statement logging.
    pub sql_logging: bool,
}

impl Default for PgConfig {
    fn default() -> Self {
        Self {
            database_url: String::new(),
            max_connections: 10,
            min_connections: 2,
            connect_timeout: Duration::from_secs(5),
            max_lifetime: Duration::from_secs(30 * 60),
            sql_logging: false,
        }
    }
}

impl PgConfig {
    /// Create a config from just a database URL with default pool settings.
    pub fn new(database_url: impl Into<String>) -> Self {
        Self {
            database_url: database_url.into(),
            ..Default::default()
        }
    }
}

/// Create a SeaORM database connection with pool configuration.
pub async fn connect(config: &PgConfig) -> Result<DatabaseConnection> {
    let mut opts = ConnectOptions::new(&config.database_url);
    opts.max_connections(config.max_connections)
        .min_connections(config.min_connections)
        .connect_timeout(config.connect_timeout)
        .max_lifetime(config.max_lifetime)
        .sqlx_logging(config.sql_logging);

    let db = Database::connect(opts)
        .await
        .context("Failed to connect to PostgreSQL")?;

    tracing::info!("Connected to PostgreSQL");
    Ok(db)
}

/// Create a connection from a URL string with default pool settings.
pub async fn connect_simple(database_url: &str) -> Result<DatabaseConnection> {
    connect(&PgConfig::new(database_url)).await
}

/// Run all pending migrations.
pub async fn run_migrations(db: &DatabaseConnection) -> Result<()> {
    Migrator::up(db, None)
        .await
        .context("Failed to run database migrations")?;
    tracing::info!("Database migrations complete");
    Ok(())
}

/// Roll back the last applied migration.
pub async fn rollback_last(db: &DatabaseConnection) -> Result<()> {
    Migrator::down(db, Some(1))
        .await
        .context("Failed to roll back migration")?;
    Ok(())
}

/// Connect to PostgreSQL and run pending migrations in one call.
pub async fn connect_and_migrate(config: &PgConfig) -> Result<DatabaseConnection> {
    let db = connect(config).await?;
    run_migrations(&db).await?;
    Ok(db)
}
