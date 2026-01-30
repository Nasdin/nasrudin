//! Integration test: full derivation → Lean4 export → lake build verification.
//!
//! This test requires a working Lean4 toolchain with Mathlib.
//! Run with: cargo test -p nasrudin-derive -- --include-ignored

use nasrudin_derive::DerivationEngine;

/// Full integration: derive E=mc², emit Lean4, verify via lake build.
#[test]
#[ignore = "requires Lean4 toolchain + Mathlib (run with --include-ignored)"]
fn test_full_derivation_and_lean_verification() {
    let engine = DerivationEngine::with_sr_axioms();

    // Derive and verify
    let prover_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("prover");

    let result = engine.derive_and_verify(&prover_root);

    match result {
        Ok(r) => {
            println!("Derivation succeeded!");
            println!("Theorem: {}", r.theorem.to_canonical());
            println!("Steps: {}", r.steps.len());
            for step in &r.steps {
                println!("  - {step}");
            }
            if let Some(dim) = &r.dimension {
                println!("Dimension: {dim}");
            }
        }
        Err(e) => {
            panic!("Derivation or verification failed: {e}");
        }
    }
}

/// Derive E=mc² without Lean verification (no toolchain needed).
#[test]
fn test_derivation_without_lean() {
    let engine = DerivationEngine::with_sr_axioms();
    let result = engine.derive_rest_energy();

    assert!(result.is_ok(), "derivation should succeed: {:?}", result.err());

    let r = result.unwrap();
    println!("Theorem: {}", r.theorem.to_canonical());
    println!("Steps:");
    for step in &r.steps {
        println!("  - {step}");
    }
    println!("Lean source length: {} chars", r.lean_source.len());
    assert!(!r.lean_source.is_empty());
}
