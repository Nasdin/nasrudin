//! Derive E = mc² from **truly upstream** SR axioms — no `mass_shell_condition`.
//!
//! This is the no-cheating analogue of `derive_emc2`. The axiom set comes from
//! `AxiomStore::load_special_relativity_upstream()` which registers only the
//! Minkowski-invariant + four-momentum / invariant-mass / rest-frame
//! postulates — none of which contain `mc²` as a sub-expression. Mass-shell
//! becomes a derivable theorem.
//!
//! Usage:
//!   derive_emc2_upstream                    # derive + print summary
//!   derive_emc2_upstream --emit <path>      # emit .lean file to path
//!   derive_emc2_upstream --verify <prover>  # derive + verify via lake build

use nasrudin_derive::axiom_store::AxiomStore;
use nasrudin_derive::derivation::DerivationEngine;
use nasrudin_derive::lean_emitter::{LeanEmitConfig, emit_lean_file};
use nasrudin_derive::lean_verify::{LeanVerifier, LeanVerifyResult};
use nasrudin_derive::strategies::DeriveRestEnergyFromUpstream;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    println!("═══════════════════════════════════════════════════════");
    println!("  Physics Derivation Engine — E = mc² (UPSTREAM)");
    println!("  No mass_shell_condition; only fundamental SR postulates.");
    println!("═══════════════════════════════════════════════════════");
    println!();

    // Build engine with upstream axiom set only.
    let mut engine = DerivationEngine::new();
    engine.store_mut().load_special_relativity_upstream();
    let store = engine.store();
    println!("▶ Upstream axiom set ({} axioms):", store.len());
    for name in store.names() {
        let ax = store.get(&name).unwrap();
        println!("    • {} — {}", ax.name, ax.description);
    }
    println!();

    // Sanity check: confirm `mass_shell_condition` is NOT in the store.
    if store.get("mass_shell_condition").is_some() {
        eprintln!("  ✗ FAIL: mass_shell_condition is in the upstream store. That's cheating.");
        std::process::exit(2);
    }
    println!("  ✓ mass_shell_condition is NOT an axiom (no cheating).");
    println!();

    // Run the upstream strategy.
    println!("▶ Deriving E = mc² from upstream postulates...");
    println!();
    let strategy = DeriveRestEnergyFromUpstream;
    let (theorem, ctx) = match engine.derive_by_strategy(&strategy) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("  ✗ Derivation FAILED: {e}");
            std::process::exit(1);
        }
    };

    println!("  Derivation steps:");
    for (i, step) in ctx.steps().iter().enumerate() {
        println!("    Step {}: {} [{}]", i + 1, step.description, step.rule);
    }
    println!();
    println!("  ✓ Result: {}", theorem.to_canonical());
    println!();

    // Emit Lean source.
    let config = LeanEmitConfig {
        namespace: "PhysicsGenerator.Derived".into(),
        theorem_name: "rest_energy_upstream".into(),
        use_mathlib: true,
    };
    let lean_source = emit_lean_file(&ctx, &config);
    println!("▶ Generated {} bytes of Lean4 source.", lean_source.len());
    println!();

    // --emit
    if let Some(pos) = args.iter().position(|a| a == "--emit") {
        if let Some(path) = args.get(pos + 1) {
            println!("▶ Writing Lean4 proof to {path}...");
            match std::fs::write(path, &lean_source) {
                Ok(()) => println!("  ✓ Written successfully"),
                Err(e) => {
                    eprintln!("  ✗ Write failed: {e}");
                    std::process::exit(1);
                }
            }
            println!();
        }
    }

    // --verify
    if let Some(pos) = args.iter().position(|a| a == "--verify") {
        if let Some(prover_root) = args.get(pos + 1) {
            println!("▶ Verifying with Lean4 (lake build)...");
            let verifier = LeanVerifier::new(prover_root);
            let module = "PhysicsGenerator.Derived.AutoRestEnergyUpstream";
            match verifier.verify_file(&lean_source, module) {
                LeanVerifyResult::Success => {
                    println!("  ✓ Lean4 kernel VERIFIED the upstream proof!");
                }
                LeanVerifyResult::Failed { stderr } => {
                    eprintln!("  ✗ Lean4 REJECTED:");
                    eprintln!("{stderr}");
                    std::process::exit(1);
                }
                LeanVerifyResult::ProcessError { message } => {
                    eprintln!("  ✗ Could not run lake build: {message}");
                    std::process::exit(1);
                }
            }
            println!();
        }
    }

    if !args.iter().any(|a| a == "--emit") && !args.iter().any(|a| a == "--verify") {
        println!("── Generated Lean4 Proof ──────────────────────────────");
        println!("{lean_source}");
        println!("───────────────────────────────────────────────────────");
    }

    // Suppress unused-import if AxiomStore re-export wasn't used elsewhere.
    let _ = std::any::type_name::<AxiomStore>();
}
