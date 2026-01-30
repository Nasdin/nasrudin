//! CLI tool to generate `.lean` axiom files from a PhysLean catalog.
//!
//! Usage:
//!   cargo run --bin generate_lean -- \
//!     --catalog ../physlean-extract/output/catalog.json \
//!     --output ../prover/PhysicsGenerator/Generated/

use std::path::PathBuf;

use anyhow::{Context, Result};
use physics_importer::{generate_all, load_catalog};

fn main() -> Result<()> {
    // Parse args manually (no clap dependency needed for this simple CLI)
    let args: Vec<String> = std::env::args().collect();

    let catalog_path = get_arg(&args, "--catalog")
        .unwrap_or_else(|| PathBuf::from("../physlean-extract/output/catalog.json"));

    let output_dir = get_arg(&args, "--output")
        .unwrap_or_else(|| PathBuf::from("../prover/PhysicsGenerator/Generated"));

    eprintln!("PhysLean → Lean4 Code Generator");
    eprintln!("================================");
    eprintln!("Catalog: {}", catalog_path.display());
    eprintln!("Output:  {}", output_dir.display());
    eprintln!();

    let catalog = load_catalog(&catalog_path)
        .with_context(|| "Failed to load catalog")?;

    eprintln!(
        "Loaded catalog: {} theorems across {} domains",
        catalog.theorem_count(),
        catalog.domains().len(),
    );

    let count = generate_all(&catalog, &output_dir)
        .with_context(|| "Failed to generate Lean files")?;

    eprintln!("Generated {count} files in {}", output_dir.display());
    Ok(())
}

fn get_arg(args: &[String], flag: &str) -> Option<PathBuf> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
}
