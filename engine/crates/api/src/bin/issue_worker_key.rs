//! `issue_worker_key` — generate and persist a worker bearer key.
//!
//! Bootstrap utility for fresh deploys (no human user has logged in yet
//! to mint one through `/api/api-keys`). Inserts an api_keys row with
//! kind="worker" and `user_id=NULL`, then prints the full bearer token
//! to stdout — capture it once, store it in the worker process's
//! `NASRUDIN_WORKER_KEY` env var.
//!
//!     DATABASE_URL=postgres://... cargo run --bin issue_worker_key -- pool-worker-1

use anyhow::Result;
use physics_api::keygen;

#[tokio::main]
async fn main() -> Result<()> {
    let env_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.env");
    let _ = dotenvy::from_path(&env_path);

    let name = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "default-worker".to_string());

    let database_url = std::env::var("DATABASE_URL")
        .map_err(|_| anyhow::anyhow!("DATABASE_URL env var required"))?;
    let conn =
        nasrudin_pg::connect_and_migrate(&nasrudin_pg::PgConfig::new(&database_url)).await?;

    let key = keygen::generate("worker")?;
    nasrudin_pg::query::api_keys::create(
        &conn,
        None,
        "worker",
        &name,
        &key.prefix,
        &key.hash,
        None,
    )
    .await?;

    eprintln!("✓ Issued worker key '{name}' (prefix {})", key.prefix);
    eprintln!("  Use it in NASRUDIN_WORKER_KEY:");
    println!("{}", key.full);
    Ok(())
}
