//! One-shot inspector: report stats on how many theorems carry
//! non-empty `axiom_ancestors` after the backfill ran. Sanity check
//! that the migration actually populated the indexes.

use anyhow::{Context, Result};
use nasrudin_rocks::TheoremDb;

fn main() -> Result<()> {
    let path = std::env::args()
        .nth(1)
        .context("usage: inspect_lineage <rocksdb_path>")?;
    let db = TheoremDb::new(&path)?;
    let theorems = db.list_theorems()?;
    let total = theorems.len();
    let mut with_ancestors = 0usize;
    let mut total_edges = 0usize;
    let mut max_a = 0usize;
    let mut sample_id = None;
    use std::collections::HashMap;
    let mut by_origin: HashMap<&'static str, usize> = HashMap::new();
    let mut by_proof_shape: HashMap<&'static str, usize> = HashMap::new();
    let mut with_parents = 0usize;
    for t in &theorems {
        let origin_kind: &'static str = match &t.origin {
            nasrudin_core::TheoremOrigin::Axiom => "Axiom",
            nasrudin_core::TheoremOrigin::Imported { .. } => "Imported",
            nasrudin_core::TheoremOrigin::Crossover { .. } => "Crossover",
            nasrudin_core::TheoremOrigin::Mutation { .. } => "Mutation",
            nasrudin_core::TheoremOrigin::Simplification { .. } => "Simplification",
            nasrudin_core::TheoremOrigin::DomainTransfer { .. } => "DomainTransfer",
        };
        *by_origin.entry(origin_kind).or_insert(0) += 1;
        let shape: &'static str = match &t.proof {
            nasrudin_core::ProofTree::Axiom(_) => "Axiom",
            nasrudin_core::ProofTree::ModusPonens { .. } => "ModusPonens",
            nasrudin_core::ProofTree::UnivInst { .. } => "UnivInst",
            nasrudin_core::ProofTree::Substitute { .. } => "Substitute",
            nasrudin_core::ProofTree::Rewrite { .. } => "Rewrite",
            nasrudin_core::ProofTree::EqChain(_) => "EqChain",
            nasrudin_core::ProofTree::TacticProof { .. } => "TacticProof",
            nasrudin_core::ProofTree::Algebraic { .. } => "Algebraic",
        };
        *by_proof_shape.entry(shape).or_insert(0) += 1;
        if !t.parents.is_empty() {
            with_parents += 1;
        }
    }
    println!("By origin:       {by_origin:?}");
    println!("By proof shape:  {by_proof_shape:?}");
    println!("With parents:    {with_parents}");
    for t in &theorems {
        if let Some(lin) = db.get_lineage(&t.id)? {
            if !lin.axiom_ancestors.is_empty() {
                with_ancestors += 1;
                total_edges += lin.axiom_ancestors.len();
                if lin.axiom_ancestors.len() > max_a {
                    max_a = lin.axiom_ancestors.len();
                    sample_id = Some((t.id, t.canonical.clone()));
                }
            }
        }
    }
    println!("Total theorems:                    {total}");
    println!("Theorems with axiom_ancestors:     {with_ancestors}");
    println!("Total dependency edges:            {total_edges}");
    println!("Max ancestors on a single theorem: {max_a}");
    if let Some((id, canon)) = sample_id {
        let deps = db.list_dependents(&id)?;
        println!("Densest theorem ({}…): {deps_n} dependents", &hex::encode(id)[..8], deps_n = deps.len());
        let preview: String = canon.chars().take(80).collect();
        println!("  canonical: {preview}");
    }
    Ok(())
}
