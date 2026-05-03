//! One-shot migration: populate `LineageRecord.axiom_ancestors` and
//! `CF_REVERSE_DEPS` for every theorem in the production RocksDB.
//!
//! Usage: `cargo run --bin backfill_lineage -- <rocksdb_path>`
//! Idempotent: safe to re-run.

use anyhow::{Context, Result};
use nasrudin_rocks::TheoremDb;

fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let path = std::env::args()
        .nth(1)
        .context("usage: backfill_lineage <rocksdb_path>")?;

    let db = TheoremDb::new(&path).context("Failed to open RocksDB at given path")?;

    let started = std::time::Instant::now();
    let processed = db
        .backfill_lineage_and_reverse_deps()
        .context("Backfill failed")?;
    let elapsed = started.elapsed();

    println!(
        "Backfill complete: {processed} theorems processed in {:.2}s",
        elapsed.as_secs_f64()
    );
    Ok(())
}
