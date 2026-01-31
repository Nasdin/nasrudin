//! Derives E = mc² from first principles, stores in RocksDB, and optionally verifies via Lean4.
//!
//! Usage:
//!   derive_emc2                                    # derive + print summary
//!   derive_emc2 --db ./physics_data                # derive + store in RocksDB
//!   derive_emc2 --db ./physics_data --dump         # dump RocksDB contents
//!   derive_emc2 --emit <path>                      # emit .lean file to path
//!   derive_emc2 --verify <prover_root>             # derive + verify via lake build
//!   derive_emc2 --db ./physics_data --verify <pr>  # full pipeline: derive → store → verify

use nasrudin_core::{
    compute_theorem_id, Domain, Expr, FitnessScore, ProofTree, Theorem, TheoremOrigin,
    VerificationStatus,
};
use nasrudin_derive::derivation::DerivationEngine;
use nasrudin_derive::dimension_checker::{check_equation_dimensions, sr_variable_dimensions};
use nasrudin_derive::lean_emitter::{emit_lean_file, LeanEmitConfig};
use nasrudin_derive::lean_verify::{LeanVerifier, LeanVerifyResult};
use nasrudin_rocks::TheoremDb;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    println!("═══════════════════════════════════════════════════════");
    println!("  Physics Derivation Engine — E = mc²");
    println!("═══════════════════════════════════════════════════════");
    println!();

    // Parse --db flag
    let db_path = args
        .iter()
        .position(|a| a == "--db")
        .and_then(|pos| args.get(pos + 1))
        .map(|s| s.as_str());

    // Handle --dump mode (just show DB contents)
    if args.iter().any(|a| a == "--dump") {
        let path = db_path.unwrap_or("./physics_data");
        println!("▶ Dumping RocksDB at '{path}'...");
        println!();
        match TheoremDb::new(path) {
            Ok(db) => {
                if let Err(e) = dump_database(&db) {
                    eprintln!("  ✗ Dump failed: {e}");
                    std::process::exit(1);
                }
            }
            Err(e) => {
                eprintln!("  ✗ Failed to open RocksDB: {e}");
                std::process::exit(1);
            }
        }
        return;
    }

    // Step 1: Load axioms from PhysLean catalog (falls back to legacy SR)
    println!("▶ Loading axioms from PhysLean catalog...");
    let engine = DerivationEngine::with_catalog_axioms();
    let store = engine.store();
    println!("  Loaded {} axioms:", store.len());
    for name in store.names() {
        let ax = store.get(name).unwrap();
        println!("    • {} — {}", ax.name, ax.description);
    }
    println!();

    // Step 2: Derive E = mc²
    println!("▶ Deriving E = mc² from mass-shell condition...");
    println!();

    let result = match engine.derive_rest_energy() {
        Ok(r) => r,
        Err(e) => {
            eprintln!("  ✗ Derivation FAILED: {e}");
            std::process::exit(1);
        }
    };

    // Print derivation steps
    println!("  Derivation steps:");
    for (i, step) in result.steps.iter().enumerate() {
        println!("    Step {}: {}", i + 1, step);
    }
    println!();

    // Step 3: Show result
    let canonical = result.theorem.to_canonical();
    println!("  ✓ Result: {}", canonical);
    println!();

    // Step 4: Dimensional analysis
    print!("▶ Checking dimensional consistency... ");
    let var_dims = sr_variable_dimensions();
    let dim_result = check_equation_dimensions(&result.theorem, &var_dims);
    match &dim_result {
        Ok(dim) => println!("✓ Homogeneous (dimension: {dim})"),
        Err(e) => println!("✗ {e}"),
    }
    println!();

    // Step 5: Generate Lean4 proof
    println!("▶ Generating Lean4 proof...");
    let config = LeanEmitConfig::default();
    let (_, ctx) = engine
        .derive_by_strategy(&nasrudin_derive::strategies::DeriveRestEnergy)
        .unwrap();
    let lean_source = emit_lean_file(&ctx, &config);
    println!("  Generated {} bytes of Lean4 source", lean_source.len());
    println!();

    // Step 6: Lean4 verification (if --verify)
    let mut verified = false;
    let mut tactic_used = String::new();
    if let Some(pos) = args.iter().position(|a| a == "--verify") {
        if let Some(prover_root) = args.get(pos + 1) {
            println!("▶ Verifying with Lean4 (lake build)...");
            let verifier = LeanVerifier::new(prover_root);
            let module = "PhysicsGenerator.Derived.AutoRestEnergy";
            let verify_result = verifier.verify_file(&lean_source, module);

            match verify_result {
                LeanVerifyResult::Success => {
                    println!("  ✓ Lean4 kernel VERIFIED the proof!");
                    verified = true;
                    tactic_used = "linarith + simp + positivity".to_string();
                }
                LeanVerifyResult::Failed { stderr } => {
                    eprintln!("  ✗ Lean4 REJECTED the proof:");
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

    // Step 7: Store in RocksDB (if --db)
    if let Some(path) = db_path {
        println!("▶ Opening RocksDB at '{path}'...");
        let db = match TheoremDb::new(path) {
            Ok(db) => db,
            Err(e) => {
                eprintln!("  ✗ Failed to open RocksDB: {e}");
                std::process::exit(1);
            }
        };
        println!("  ✓ Database opened (9 column families)");
        println!();

        // First store the mass-shell axiom
        println!("▶ Storing axioms in RocksDB...");
        let axiom_names = store.names();
        for name in &axiom_names {
            let ax = store.get(name).unwrap();
            let ax_canonical = ax.statement.to_canonical();
            let axiom_theorem = Theorem {
                id: compute_theorem_id(&ax_canonical),
                statement: ax.statement.clone(),
                canonical: ax_canonical,
                latex: expr_to_latex(&ax.statement),
                proof: ProofTree::Axiom(compute_theorem_id(&ax.name)),
                depth: 0,
                complexity: expr_complexity(&ax.statement),
                domain: Domain::SpecialRelativity,
                dimension: None,
                parents: vec![],
                children: vec![],
                verified: VerificationStatus::Verified {
                    proof_term: vec![],
                    tactic_used: "axiom".to_string(),
                },
                fitness: FitnessScore::default(),
                generation: 0,
                created_at: now_epoch(),
                origin: TheoremOrigin::Axiom,
            };

            match db.put_theorem(&axiom_theorem) {
                Ok(()) => println!(
                    "    ✓ Stored axiom '{}' [id: {}]",
                    ax.name,
                    hex::encode(axiom_theorem.id)
                ),
                Err(e) => eprintln!("    ✗ Failed to store axiom '{}': {e}", ax.name),
            }
        }
        println!();

        // Now store the derived E = mc²
        println!("▶ Storing derived theorem E = mc² in RocksDB...");
        let theorem_id = compute_theorem_id(&canonical);

        let verification_status = if verified {
            VerificationStatus::Verified {
                proof_term: lean_source.as_bytes().to_vec(),
                tactic_used,
            }
        } else {
            VerificationStatus::Pending
        };

        // The parent is the mass-shell axiom
        let mass_shell_ax = store.get("mass_shell_condition").unwrap();
        let parent_id = compute_theorem_id(&mass_shell_ax.statement.to_canonical());

        let emc2_theorem = Theorem {
            id: theorem_id,
            statement: result.theorem.clone(),
            canonical: canonical.clone(),
            latex: "E = mc^2".to_string(),
            proof: ProofTree::Algebraic {
                source: Box::new(ProofTree::Axiom(parent_id)),
                operations: vec![
                    nasrudin_core::AlgebraicOp::Expand,
                    nasrudin_core::AlgebraicOp::CollectTerms("p".to_string()),
                    nasrudin_core::AlgebraicOp::TakeSquareRoot,
                ],
            },
            depth: result.steps.len() as u32,
            complexity: expr_complexity(&result.theorem),
            domain: Domain::SpecialRelativity,
            dimension: result.dimension.clone(),
            parents: vec![parent_id],
            children: vec![],
            verified: verification_status,
            fitness: FitnessScore {
                novelty: 1.0,
                complexity: 1.0 / (1.0 + expr_complexity(&result.theorem) as f64),
                depth: 1.0 / (1.0 + result.steps.len() as f64),
                dimensional: if dim_result.is_ok() { 1.0 } else { 0.0 },
                symmetry: 0.8, // Lorentz invariant
                connectivity: 1.0,
                nasrudin_relevance: 1.0,
            },
            generation: 1,
            created_at: now_epoch(),
            origin: TheoremOrigin::Simplification { parent: parent_id },
        };

        match db.put_theorem(&emc2_theorem) {
            Ok(()) => {
                println!(
                    "    ✓ Stored theorem [id: {}]",
                    hex::encode(emc2_theorem.id)
                );
                println!("      canonical: {}", emc2_theorem.canonical);
                println!("      domain:    SpecialRelativity");
                println!("      depth:     {}", emc2_theorem.depth);
                println!("      verified:  {}", verified);
            }
            Err(e) => {
                eprintln!("    ✗ Failed to store theorem: {e}");
                std::process::exit(1);
            }
        }
        println!();

        // Dump final DB state
        println!("▶ RocksDB column family summary:");
        if let Err(e) = db.dump_all() {
            eprintln!("  ✗ Dump failed: {e}");
        }
        println!();

        // Show stats
        match db.get_stats() {
            Ok(stats) => {
                println!("▶ Database statistics:");
                println!("    Total theorems:  {}", stats.total_theorems);
                println!("    Verified:        {}", stats.total_verified);
                println!("    Axioms:          {}", stats.total_axioms);
                println!("    Max depth:       {}", stats.max_depth);
                println!("    Max generation:  {}", stats.max_generation);
            }
            Err(e) => eprintln!("  ✗ Failed to read stats: {e}"),
        }
        println!();
    }

    // Handle --emit flag
    if let Some(pos) = args.iter().position(|a| a == "--emit") {
        if let Some(path) = args.get(pos + 1) {
            println!("▶ Writing Lean4 proof to {path}...");
            match std::fs::write(path, &lean_source) {
                Ok(()) => println!("  ✓ Written successfully"),
                Err(e) => {
                    eprintln!("  ✗ Failed to write: {e}");
                    std::process::exit(1);
                }
            }
            println!();
        }
    }

    // Final banner
    if verified {
        println!("═══════════════════════════════════════════════════════");
        println!("  E = mc²  — DERIVED AND FORMALLY VERIFIED");
        if db_path.is_some() {
            println!("  Stored in RocksDB with full lineage & indexes");
        }
        println!("═══════════════════════════════════════════════════════");
    } else if !args.iter().any(|a| a == "--verify") {
        // No --verify: print the Lean source
        println!("── Generated Lean4 Proof ──────────────────────────────");
        println!("{lean_source}");
        println!("───────────────────────────────────────────────────────");
        println!();
        println!("To verify: derive_emc2 --verify <path-to-prover>");
    }
}

fn dump_database(db: &TheoremDb) -> Result<(), Box<dyn std::error::Error>> {
    // Column family counts
    println!("── Column Family Summary ─────────────────────────────");
    db.dump_all()?;
    println!();

    // List all theorems
    let theorems = db.list_theorems()?;
    println!("── Theorems ({}) ─────────────────────────────────────", theorems.len());
    for t in &theorems {
        let status = match &t.verified {
            VerificationStatus::Verified { tactic_used, .. } => {
                format!("✓ verified ({})", tactic_used)
            }
            VerificationStatus::Pending => "⏳ pending".to_string(),
            VerificationStatus::Rejected { reason } => format!("✗ rejected: {reason}"),
            VerificationStatus::Timeout => "⏱ timeout".to_string(),
        };
        let origin = match &t.origin {
            TheoremOrigin::Axiom => "axiom".to_string(),
            TheoremOrigin::Simplification { .. } => "derived (simplification)".to_string(),
            TheoremOrigin::Crossover { .. } => "derived (crossover)".to_string(),
            TheoremOrigin::Mutation { .. } => "derived (mutation)".to_string(),
            TheoremOrigin::Imported { source } => format!("imported ({source})"),
            TheoremOrigin::DomainTransfer { from, to, .. } => {
                format!("domain transfer ({from:?} → {to:?})")
            }
        };

        println!();
        println!("  ID:        {}", hex::encode(t.id));
        println!("  Canonical: {}", t.canonical);
        if !t.latex.is_empty() {
            println!("  LaTeX:     {}", t.latex);
        }
        println!("  Domain:    {:?}", t.domain);
        println!("  Depth:     {}", t.depth);
        println!("  Origin:    {}", origin);
        println!("  Status:    {}", status);
        println!("  Gen:       {}", t.generation);
        if !t.parents.is_empty() {
            let parent_ids: Vec<String> = t.parents.iter().map(hex::encode).collect();
            println!("  Parents:   [{}]", parent_ids.join(", "));
        }
    }
    println!();

    // Show stats
    let stats = db.get_stats()?;
    println!("── Statistics ────────────────────────────────────────");
    println!("  Total theorems:  {}", stats.total_theorems);
    println!("  Verified:        {}", stats.total_verified);
    println!("  Rejected:        {}", stats.total_rejected);
    println!("  Pending:         {}", stats.total_pending);
    println!("  Axioms:          {}", stats.total_axioms);
    println!("  Max depth:       {}", stats.max_depth);
    println!("  Max generation:  {}", stats.max_generation);

    Ok(())
}

/// Simple LaTeX rendering of expressions.
fn expr_to_latex(expr: &Expr) -> String {
    match expr {
        Expr::Var(s) => s.clone(),
        Expr::Lit(n, 1) => format!("{n}"),
        Expr::Lit(n, d) => format!("\\frac{{{n}}}{{{d}}}"),
        Expr::BinOp(op, left, right) => {
            let l = expr_to_latex(left);
            let r = expr_to_latex(right);
            match op {
                nasrudin_core::BinOp::Add => format!("{l} + {r}"),
                nasrudin_core::BinOp::Sub => format!("{l} - {r}"),
                nasrudin_core::BinOp::Mul => format!("{l} \\cdot {r}"),
                nasrudin_core::BinOp::Div => format!("\\frac{{{l}}}{{{r}}}"),
                nasrudin_core::BinOp::Pow => format!("{l}^{{{r}}}"),
                nasrudin_core::BinOp::Eq => format!("{l} = {r}"),
                _ => format!("{l} \\mathbin{{{op:?}}} {r}"),
            }
        }
        Expr::UnOp(op, operand) => {
            let inner = expr_to_latex(operand);
            match op {
                nasrudin_core::UnOp::Neg => format!("-{inner}"),
                nasrudin_core::UnOp::Sqrt => format!("\\sqrt{{{inner}}}"),
                nasrudin_core::UnOp::Abs => format!("|{inner}|"),
                _ => format!("\\mathrm{{{op:?}}}({inner})"),
            }
        }
        Expr::Const(c) => match c {
            nasrudin_core::PhysConst::SpeedOfLight => "c".to_string(),
            nasrudin_core::PhysConst::PlanckConst => "h".to_string(),
            _ => format!("{c:?}"),
        },
        Expr::App(func, arg) => {
            let f = expr_to_latex(func);
            let a = expr_to_latex(arg);
            format!("{f}({a})")
        }
        _ => format!("{expr:?}"),
    }
}

/// Count expression nodes as a complexity measure.
fn expr_complexity(expr: &Expr) -> u32 {
    match expr {
        Expr::Var(_) | Expr::Lit(..) | Expr::Const(_) => 1,
        Expr::BinOp(_, left, right) => 1 + expr_complexity(left) + expr_complexity(right),
        Expr::UnOp(_, operand) => 1 + expr_complexity(operand),
        Expr::App(func, arg) => 1 + expr_complexity(func) + expr_complexity(arg),
        Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) => {
            1 + expr_complexity(ty) + expr_complexity(body)
        }
        Expr::Deriv(body, _) | Expr::PartialDeriv(body, _) => 1 + expr_complexity(body),
        _ => 1,
    }
}

/// Get current epoch seconds.
fn now_epoch() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}
