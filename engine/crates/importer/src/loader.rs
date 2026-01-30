//! Catalog loading and validation.

use std::path::Path;

use anyhow::{Context, Result};

use crate::catalog::PhysLeanCatalog;

/// Load and validate a PhysLean catalog from a JSON file.
pub fn load_catalog(path: &Path) -> Result<PhysLeanCatalog> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read catalog file: {}", path.display()))?;

    let catalog: PhysLeanCatalog = serde_json::from_str(&content)
        .with_context(|| format!("Failed to parse catalog JSON: {}", path.display()))?;

    validate_catalog(&catalog)?;

    tracing::info!(
        "Loaded PhysLean catalog: {} theorems, {} types, {} constants (PhysLean {})",
        catalog.theorems.len(),
        catalog.types.len(),
        catalog.constants.len(),
        catalog.physlean_version,
    );

    Ok(catalog)
}

/// Validate catalog consistency.
fn validate_catalog(catalog: &PhysLeanCatalog) -> Result<()> {
    // Check that all theorem domains have corresponding import mappings
    for theorem in &catalog.theorems {
        if !catalog.domain_imports.contains_key(&theorem.domain) {
            tracing::warn!(
                "Theorem '{}' has domain '{}' with no import mapping — will be skipped",
                theorem.name,
                theorem.domain,
            );
        }
    }

    // Check for duplicate theorem names
    let mut seen = std::collections::HashSet::new();
    for theorem in &catalog.theorems {
        if !seen.insert(&theorem.name) {
            anyhow::bail!("Duplicate theorem name in catalog: '{}'", theorem.name);
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn load_catalog_from_fixture() {
        // Test with the vendored catalog
        let catalog_path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("physlean-extract/output/catalog.json");

        if catalog_path.exists() {
            let catalog = load_catalog(&catalog_path).unwrap();
            assert!(!catalog.theorems.is_empty());
            assert!(!catalog.domain_imports.is_empty());
        }
    }
}
