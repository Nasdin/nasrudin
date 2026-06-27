//! `nasrudin-embed-build`: scan the engine's RocksDB, embed every
//! verified theorem's `canonical + latex + domain`, and write
//! `corpus.embed` + `corpus.embed.hnsw` to the configured output dir.
//!
//! Usage:
//!
//! ```bash
//! NASRUDIN_EMBED_OUT=$HOME/.nasrudin/embed/corpus.embed \
//!   ROCKS_DB_PATH=./data/theorems.db \
//!   cargo run --release --bin embed_build
//! ```

use std::path::PathBuf;

use anyhow::{Context, Result};
use nasrudin_core::{Theorem, VerificationStatus};
use nasrudin_embed::{Embedder, IndexBuilder};
use nasrudin_rocks::TheoremDb;

fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let db_path = std::env::var("ROCKS_DB_PATH").unwrap_or_else(|_| "./data/theorems.db".into());
    let out_path: PathBuf = std::env::var("NASRUDIN_EMBED_OUT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
            PathBuf::from(home).join(".nasrudin/embed/corpus.embed")
        });
    let batch_size: usize = std::env::var("NASRUDIN_EMBED_BATCH")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(64);

    if let Some(parent) = out_path.parent() {
        std::fs::create_dir_all(parent).with_context(|| format!("mkdir -p {parent:?}"))?;
    }

    let db = TheoremDb::new(&db_path).with_context(|| format!("open RocksDB at {db_path}"))?;
    tracing::info!("scanning theorems from {db_path}");
    let all = db.list_theorems()?;

    let verified: Vec<&Theorem> = all
        .iter()
        .filter(|t| matches!(t.verified, VerificationStatus::Verified { .. }))
        .collect();
    tracing::info!(
        "found {} verified theorems (of {} total)",
        verified.len(),
        all.len()
    );

    let texts: Vec<(nasrudin_core::TheoremId, String)> = verified
        .iter()
        .map(|t| {
            let body = format!("{}\n{}\n{}", t.canonical, t.latex, domain_string(&t.domain));
            (t.id, body)
        })
        .collect();

    let embedder = Embedder::new().context("init Embedder")?;
    let mut builder = IndexBuilder::new();
    builder
        .add_batch(&embedder, texts, batch_size)
        .context("embed corpus")?;
    builder.save(&out_path).context("save index")?;

    tracing::info!("wrote {} records to {out_path:?}", builder.len());
    Ok(())
}

fn domain_string(d: &nasrudin_core::Domain) -> String {
    format!("{:?}", d)
}
