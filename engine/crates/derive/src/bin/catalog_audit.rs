//! Audit how many PhysLean catalog entries deserialize into the Rust
//! `Expr` enum vs fall back to the `Var(name)` placeholder.
//!
//! Reflects the same parse path as
//! `AxiomStore::load_from_catalog` → `parse_catalog_theorem`. Output:
//!
//!   total | structured_ast | placeholder | root variant counts
//!
//! Usage:
//!   catalog_audit <path-to-catalog.json>
//!
//! Run on the droplet:
//!   /opt/nasrudin/bin/catalog_audit /opt/nasrudin/physlean-extract/output/catalog.json
//!
//! Goal context: M2 acceptance asks that ≥ 500 PhysLean theorems
//! expose real Expr trees in the worker store. This binary is the
//! ground-truth count.

use nasrudin_core::Expr;
use std::collections::BTreeMap;

fn main() -> anyhow::Result<()> {
    let path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "physics_data/physlean-extract/output/catalog.json".into());
    let content = std::fs::read_to_string(&path)?;
    let mut deser = serde_json::Deserializer::from_str(&content);
    deser.disable_recursion_limit();
    let deser = serde_stacker::Deserializer::new(&mut deser);
    let catalog: serde_json::Value = serde::Deserialize::deserialize(deser)?;
    let thms = catalog
        .get("theorems")
        .and_then(|v| v.as_array())
        .ok_or_else(|| anyhow::anyhow!("catalog has no theorems array"))?;

    let mut total = 0usize;
    let mut has_ast_field = 0usize;
    let mut parsed_ok = 0usize;
    let mut parsed_into_eq_or_binop = 0usize;
    let mut root_variants: BTreeMap<String, usize> = BTreeMap::new();
    let mut parse_errors: BTreeMap<String, usize> = BTreeMap::new();

    for thm in thms {
        total += 1;
        let Some(ast) = thm.get("expr_ast").filter(|v| !v.is_null()) else {
            continue;
        };
        has_ast_field += 1;

        // Note the root variant tag (the JSON adjacent-tag key).
        if let Some(obj) = ast.as_object() {
            if let Some((tag, _)) = obj.iter().next() {
                *root_variants.entry(tag.clone()).or_default() += 1;
            }
        }

        match serde_json::from_value::<Expr>(ast.clone()) {
            Ok(e) => {
                parsed_ok += 1;
                // A theorem is "GA-composable" when its top-level
                // shape exposes an Eq somewhere reachable by the
                // chain rules — IntroduceAxiom + RearrangeEquation
                // expect an equation, not a Pi/App type expression.
                if expr_contains_eq_or_binop_at_top(&e) {
                    parsed_into_eq_or_binop += 1;
                }
            }
            Err(e) => {
                // Bucket parse errors by first-component / first-50-chars
                let msg = e.to_string();
                let bucket: String = msg.chars().take(60).collect();
                *parse_errors.entry(bucket).or_default() += 1;
            }
        }
    }

    println!("Catalog: {path}");
    println!("  total theorems:       {total}");
    println!("  has expr_ast field:   {has_ast_field}");
    println!(
        "  parsed into Expr:     {parsed_ok}  ({:.1}%)",
        100.0 * parsed_ok as f64 / total as f64
    );
    println!(
        "  Eq/BinOp at top:      {parsed_into_eq_or_binop}  ({:.1}%)",
        100.0 * parsed_into_eq_or_binop as f64 / total as f64
    );
    println!();
    println!("Root variant counts (across all expr_ast):");
    for (k, v) in &root_variants {
        println!("  {k:20} {v}");
    }
    if !parse_errors.is_empty() {
        println!();
        println!("Parse error buckets (top 10):");
        let mut errs: Vec<_> = parse_errors.iter().collect();
        errs.sort_by_key(|(_, c)| std::cmp::Reverse(**c));
        for (k, v) in errs.iter().take(10) {
            println!("  [{v:5}] {k}");
        }
    }
    Ok(())
}

/// Reachable Eq/BinOp scan — does the expression have algebraic
/// shape the GA's chain rules can target?
fn expr_contains_eq_or_binop_at_top(e: &Expr) -> bool {
    use nasrudin_core::BinOp;
    match e {
        Expr::BinOp(BinOp::Eq, _, _) => true,
        // For Pi-rooted theorems (∀ ... → body) recurse into the
        // body. PhysLean axiom statements are almost universally
        // Pi-wrapped over implicit type-class params; the meat is
        // in the body.
        Expr::Pi(_, _, body) => expr_contains_eq_or_binop_at_top(body),
        // Lambdas / Let bindings also commonly wrap the algebraic
        // core.
        Expr::Lam(_, _, body) | Expr::Let(_, _, body) => expr_contains_eq_or_binop_at_top(body),
        _ => false,
    }
}
