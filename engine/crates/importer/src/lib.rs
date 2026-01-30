//! PhysLean catalog importer for the Physics Generator.
//!
//! Reads the `catalog.json` produced by the `physlean-extract` tool and:
//! 1. Deserializes it into typed Rust structs ([`catalog`] module)
//! 2. Validates and loads the catalog ([`loader`] module)
//! 3. Generates `.lean` files for the prover ([`codegen`] module)
//!
//! The generated Lean files re-axiomatize PhysLean theorems in our prover's
//! Lean version (4.27), since `.olean` files are not cross-compatible between
//! Lean versions.

pub mod catalog;
pub mod codegen;
pub mod loader;

pub use catalog::PhysLeanCatalog;
pub use codegen::generate_all;
pub use loader::load_catalog;
