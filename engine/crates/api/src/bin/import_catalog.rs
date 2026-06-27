//! One-shot: open the dev RocksDB and run
//! `physlean_import::load_catalog_split` against a catalog. Lands the
//! derived-theorem half (entries with non-empty axiom_dependencies)
//! into CF_THEOREMS — populating LineageRecord.axiom_ancestors and
//! CF_REVERSE_DEPS at write time.
//!
//! Usage: `cargo run --bin import_catalog -- <rocksdb_path> <catalog_path>`
//! Idempotent: re-running on an already-imported store overwrites each
//! theorem in-place (same id from `axiom_id_from_name`).

use anyhow::{Context, Result};
use nasrudin_derive::AxiomStore;
use nasrudin_derive::physlean_import::load_catalog_split;
use nasrudin_rocks::TheoremDb;
use std::path::Path;

fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let mut args = std::env::args().skip(1);
    let db_path = args
        .next()
        .context("usage: import_catalog <rocksdb_path> <catalog_path>")?;
    let catalog_path = args
        .next()
        .context("usage: import_catalog <rocksdb_path> <catalog_path>")?;

    let db = TheoremDb::new(&db_path).context("open rocksdb")?;
    let mut store = AxiomStore::new();
    let started = std::time::Instant::now();
    let (axioms, theorems) = load_catalog_split(Path::new(&catalog_path), &mut store, &db)?;
    println!(
        "Imported in {:.2}s: {axioms} axioms (AxiomStore-only, in-process), {theorems} derived theorems written to {db_path}",
        started.elapsed().as_secs_f64(),
    );
    Ok(())
}
