//! PhysLean catalog data types.
//!
//! Mirrors the JSON schema produced by `physlean-extract`.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Top-level catalog of PhysLean extractions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PhysLeanCatalog {
    /// PhysLean git revision or tag.
    pub physlean_version: String,
    /// Lean version used for extraction.
    pub lean_version: String,
    /// Extracted theorems.
    pub theorems: Vec<CatalogTheorem>,
    /// Extracted types (structures, inductives).
    #[serde(default)]
    pub types: Vec<CatalogType>,
    /// Physical constants.
    #[serde(default)]
    pub constants: Vec<CatalogConstant>,
    /// Map from domain name to Lean import path.
    #[serde(default)]
    pub domain_imports: HashMap<String, String>,
}

/// A theorem extracted from PhysLean.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CatalogTheorem {
    /// Short name used in generated code.
    pub name: String,
    /// Fully qualified PhysLean name.
    pub physlean_name: String,
    /// Physics domain.
    pub domain: String,
    /// Pretty-printed Lean type signature.
    pub type_signature: String,
    /// Source identifier (always "physlean").
    pub source: String,
    /// Documentation string from PhysLean.
    pub doc_string: Option<String>,
}

/// A type (structure/inductive) extracted from PhysLean.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CatalogType {
    /// Short name.
    pub name: String,
    /// Fully qualified PhysLean name.
    pub physlean_name: String,
    /// Kind: "structure" or "inductive".
    pub kind: String,
    /// Pretty-printed type signature.
    #[serde(default)]
    pub type_signature: String,
    /// Field names (for structures).
    #[serde(default)]
    pub fields: Vec<String>,
}

/// A physical constant.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CatalogConstant {
    /// Constant name (e.g., "c", "G").
    pub name: String,
    /// Lean type (e.g., "ℝ").
    #[serde(rename = "type")]
    pub lean_type: String,
    /// Positivity assertion (e.g., "0 < c").
    #[serde(default)]
    pub positivity: Option<String>,
}

impl PhysLeanCatalog {
    /// Get the Lean import path for a domain, if it exists in the catalog.
    pub fn import_for_domain(&self, domain: &str) -> Option<&str> {
        self.domain_imports.get(domain).map(|s| s.as_str())
    }

    /// Get all theorems for a given domain.
    pub fn theorems_for_domain(&self, domain: &str) -> Vec<&CatalogTheorem> {
        self.theorems
            .iter()
            .filter(|t| t.domain == domain)
            .collect()
    }

    /// Get all known domain names.
    pub fn domains(&self) -> Vec<&str> {
        self.domain_imports.keys().map(|s| s.as_str()).collect()
    }

    /// Total number of theorems.
    pub fn theorem_count(&self) -> usize {
        self.theorems.len()
    }
}
