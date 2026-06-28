use std::path::PathBuf;
use std::time::Instant;

use nasrudin_derive::{AxiomStore, Chain, DerivationContext, RuleStep, strategies::DerivationStrategy};
use nasrudin_ga::{
    chain_ga::{verify_chain, ChainVerifyOutcome},
    target::TargetSpec,
};

fn main() -> anyhow::Result<()> {
    println!("═══════════════════════════════════════════════════════");
    println!("  Nasrudin End-to-End Test: Deriving Quantum Speed Limit");
    println!("═══════════════════════════════════════════════════════\n");

    // 1. Load the AxiomStore with foundational QM postulates
    let mut store = AxiomStore::new();
    store.load_quantum_mechanics_postulates();
    println!("▶ AxiomStore loaded: {} QM postulates", store.len());

    // 2. Define the target spec for qm_quantum_speed_limit
    let target = TargetSpec::lookup("qm_quantum_speed_limit").unwrap();
    println!("▶ Target spec loaded: {}", target.name);
    println!("  Final target canonical: {}", target.final_target.to_canonical());

    // 3. Define the proposed derivation chain (manual steering)
    let chain = Chain(vec![
        RuleStep::IntroduceAxiom {
            axiom_name: "qm_schrodinger_evolution".into(),
        },
        RuleStep::IntroduceAxiom {
            axiom_name: "qm_eigenvalue_equation".into(),
        },
        RuleStep::IntroduceAxiom {
            axiom_name: "qm_hbar_positive".into(),
        },
        RuleStep::AlgebraicSimplify,
    ]);

    println!("▶ Executing derivation chain locally...");
    let mut ctx = DerivationContext::new();
    match chain.execute(&store, &mut ctx) {
        Ok(final_expr) => {
            println!("  ✓ Chain executed successfully!");
            println!("  Final derived expression: {}", final_expr.to_canonical());
            
            // Calculate shape similarity to the target
            let similarity = nasrudin_ga::target::shape_similarity(&final_expr, &target.final_target);
            println!("  Shape similarity to target: {:.4}", similarity);
        }
        Err(e) => {
            anyhow::bail!("Chain execution failed: {e}");
        }
    }

    // 4. Verify the chain using the Lean4 verifier
    let prover_root = PathBuf::from("../prover");
    println!("\n▶ Verifying derivation chain using Lean4 verifier...");
    let t0 = Instant::now();
    
    match verify_chain(
        &chain,
        &store,
        &prover_root,
        "DeriveQsl",
        "derive_qsl",
    ) {
        ChainVerifyOutcome::Verified {
            lean_source,
            module_path,
        } => {
            println!("  ✓ Chain successfully verified by Lean4 kernel in {:.2}s!", t0.elapsed().as_secs_f64());
            println!("\n=== Generated Lean4 Source Code ===");
            println!("{lean_source}");
            println!("===================================\n");
            println!("Module path: {:?}", module_path);
        }
        ChainVerifyOutcome::LeanRejected { stderr, .. } => {
            println!("  ✗ Lean rejected the derivation:");
            println!("{stderr}");
        }
        ChainVerifyOutcome::PreFilterFailed { reason } => {
            println!("  ✗ Pre-filter failed: {reason}");
        }
        ChainVerifyOutcome::ToolchainError { message } => {
            println!("  ! Toolchain error: {message}");
        }
    }

    Ok(())
}
