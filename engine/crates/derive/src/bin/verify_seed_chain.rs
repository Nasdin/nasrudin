//! Run `Chain::rest_energy_from_upstream()` end-to-end and verify the
//! emitted Lean source against the local prover via `lake build`.
//!
//! Sister binary to `derive_emc2_upstream` — that one drives the
//! `DeriveRestEnergyFromUpstream` *strategy*. This one drives the
//! hand-coded *chain* that the GA worker actually seeds with, so we
//! can prove or disprove that the seed chain produces a Lake-clean
//! proof on a fast machine.
//!
//! Usage:
//!   verify_seed_chain --verify <prover_root>

use nasrudin_derive::{
    Chain, DerivationContext, DerivationEngine, DerivationStrategy,
    emit_lean_file,
    lean_verify::{LeanVerifier, LeanVerifyResult},
    LeanEmitConfig,
};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut engine = DerivationEngine::new();
    engine.store_mut().load_special_relativity_upstream();

    let chain = Chain::rest_energy_from_upstream();
    let mut ctx = DerivationContext::new();

    println!("▶ Running Chain::rest_energy_from_upstream() against upstream axioms...");
    if let Err(e) = chain.execute(engine.store(), &mut ctx) {
        eprintln!("  ✗ Chain execute FAILED: {e}");
        std::process::exit(1);
    }
    println!("  ✓ Chain executed; {} steps recorded.", ctx.steps().len());

    let cfg = LeanEmitConfig {
        namespace: "PhysicsGenerator.Derived".into(),
        theorem_name: "rest_energy_seed_chain_local".into(),
        use_mathlib: true,
    };
    let lean_source = emit_lean_file(&ctx, &cfg);
    println!("▶ Emitted {} bytes of Lean source.", lean_source.len());

    if let Some(pos) = args.iter().position(|a| a == "--verify") {
        if let Some(prover_root) = args.get(pos + 1) {
            println!("▶ Running lake build via LeanVerifier({prover_root})...");
            let verifier = LeanVerifier::new(prover_root);
            let module = "PhysicsGenerator.Derived.SeedReproducer";
            match verifier.verify_file(&lean_source, module) {
                LeanVerifyResult::Success => {
                    println!("  ✓ Lake/Lean ACCEPTED the seed-chain proof.");
                }
                LeanVerifyResult::Failed { stderr } => {
                    eprintln!("  ✗ Lake/Lean REJECTED the seed-chain proof:");
                    eprintln!("─── stderr ───────────────────────────");
                    eprintln!("{stderr}");
                    eprintln!("──────────────────────────────────────");
                    std::process::exit(1);
                }
                LeanVerifyResult::ProcessError { message } => {
                    eprintln!("  ✗ Could not run lake build: {message}");
                    std::process::exit(2);
                }
            }
        } else {
            eprintln!("--verify requires a prover root path");
            std::process::exit(2);
        }
    } else {
        println!("── Generated Lean ──────────────────────");
        println!("{lean_source}");
    }
}
