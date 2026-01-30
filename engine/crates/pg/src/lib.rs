//! PostgreSQL storage backend for user accounts, sessions, and worker state.
//!
//! This crate manages the relational data that complements the RocksDB theorem store:
//! user accounts, authentication, worker coordination, and analytics.
//!
//! Uses SeaORM 2 as the PostgreSQL ORM layer.

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use sea_orm::{Database, DatabaseConnection};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// Create a SeaORM database connection.
pub async fn create_connection(database_url: &str) -> Result<DatabaseConnection> {
    let db = Database::connect(database_url)
        .await
        .context("Failed to connect to PostgreSQL via SeaORM")?;
    Ok(db)
}

/// User account.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub username: String,
    pub email: String,
    pub password_hash: String,
    pub created_at: DateTime<Utc>,
    pub last_login: Option<DateTime<Utc>>,
}

/// Active session.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Session {
    pub id: Uuid,
    pub user_id: Uuid,
    pub token: String,
    pub created_at: DateTime<Utc>,
    pub expires_at: DateTime<Utc>,
}

/// GA worker status.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Worker {
    pub id: Uuid,
    pub name: String,
    pub status: WorkerStatus,
    pub generation: u64,
    pub theorems_produced: u64,
    pub last_heartbeat: DateTime<Utc>,
}

/// Worker status enum.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WorkerStatus {
    Idle,
    Running,
    Paused,
    Error(String),
}

/// Register a new user (stub).
pub async fn register_user(
    _db: &DatabaseConnection,
    _username: &str,
    _email: &str,
    _password_hash: &str,
) -> Result<User> {
    anyhow::bail!("User registration not yet implemented")
}

/// Authenticate a user (stub).
pub async fn login_user(
    _db: &DatabaseConnection,
    _username: &str,
    _password_hash: &str,
) -> Result<Session> {
    anyhow::bail!("User login not yet implemented")
}

/// Get worker status (stub).
pub async fn get_workers(_db: &DatabaseConnection) -> Result<Vec<Worker>> {
    anyhow::bail!("Worker listing not yet implemented")
}
