//! Standalone migration runner. Loads `.env`, connects to Postgres,
//! and applies pending migrations (or rolls back the last one).
//!
//! Usage:
//!   migrate            # apply all pending migrations (default: up)
//!   migrate up         # apply all pending migrations
//!   migrate down       # roll back the most recently applied migration

use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with(tracing_subscriber::fmt::layer())
        .init();

    // Load .env from project root
    let env_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../.env");
    let _ = dotenvy::from_path(&env_path);

    let url =
        std::env::var("DATABASE_URL").map_err(|_| anyhow::anyhow!("DATABASE_URL is not set"))?;

    let cmd = std::env::args().nth(1).unwrap_or_else(|| "up".into());
    let db = nasrudin_pg::connect_simple(&url).await?;

    match cmd.as_str() {
        "up" => {
            nasrudin_pg::run_migrations(&db).await?;
            println!("migrations complete");
        }
        "down" => {
            nasrudin_pg::rollback_last(&db).await?;
            println!("rollback complete");
        }
        other => {
            anyhow::bail!("unknown command '{other}', expected 'up' or 'down'");
        }
    }
    Ok(())
}
