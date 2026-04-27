//! Standalone migration runner. Loads `.env`, connects to Postgres,
//! and applies all pending migrations.

use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with(tracing_subscriber::fmt::layer())
        .init();

    // Load .env from project root
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
