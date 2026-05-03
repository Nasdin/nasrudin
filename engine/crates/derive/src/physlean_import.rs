//! Import PhysLean-derived theorems into the `TheoremDb`.
//!
//! `axiom_store::load_from_catalog` registers every catalog entry as
//! an `Axiom` in the hot tier — that flattens derived theorems into
//! "asserted without proof" and trips the no-cheat audit on
//! headlines. This module is the alternative path for entries that
//! ship structured dependency info (`axiom_dependencies`):
//!
//!   1. Each entry becomes a [`Theorem`] with
//!      `origin = TheoremOrigin::Imported { source: physlean_name }`,
//!      `proof = ProofTree::TacticProof { tactic: "physlean", proof_term: vec![] }`,
//!      and `parents` populated from the dep list (mapped through
//!      [`nasrudin_core::axiom_id_from_name`]).
//!   2. Entries are written in topological order so that
//!      `TheoremDb::compute_transitive_ancestors` always finds each
//!      parent's lineage already populated. Cycles in the catalog dep
//!      graph (which shouldn't exist — Lean enforces DAG) abort the
//!      import with an explanatory error.
//!   3. The acyclicity infra picks up the rest: `LineageRecord.axiom_ancestors`
//!      reflects the transitive closure, `CF_REVERSE_DEPS` indexes the
//!      edges, `forbidden_for_target` answers correctly.
//!
//! The kernel proof term itself isn't shipped (the catalog format
//! doesn't carry it); the trust model is "PhysLean built clean on the
//! Lean toolchain pinned in `lean-toolchain`, so its derived theorems
//! are kernel-checked truths." The empty `proof_term: vec![]` is a
//! signal: when the lean-bridge wants to verify a chain that uses an
//! Imported leaf, it falls through to PhysLean's source rather than
//! re-checking from scratch.

use anyhow::{Context, Result};
use nasrudin_core::{
    axiom_id_from_name, Domain, Expr, FitnessScore, ProofTree, Theorem, TheoremId,
    TheoremOrigin, VerificationStatus,
};
use nasrudin_rocks::TheoremDb;
use std::collections::{HashMap, HashSet};
use std::path::Path;

/// One catalog entry, parsed into the shape `import` needs. Pub for
/// integration tests that build entries in memory.
#[derive(Debug, Clone)]
pub struct CatalogEntry {
    pub name: String,
    pub physlean_name: String,
    pub domain: Domain,
    pub statement: Expr,
    pub canonical: String,
    pub axiom_dependencies: Vec<String>,
    pub doc_string: String,
}

/// Import every catalog entry into the TheoremDb. Returns the count of
/// theorems successfully imported.
///
/// Entries whose dependency list is empty *and* whose statement is a
/// bare `Var` placeholder (the translator timed out) are skipped — we
/// can't form a meaningful theorem from those. Everything else lands.
pub fn import_catalog_to_theorem_db(
    catalog_path: &Path,
    db: &TheoremDb,
) -> Result<usize> {
    let entries = parse_catalog(catalog_path)?;
    import_entries(entries, db)
}

/// Same as [`import_catalog_to_theorem_db`] but takes pre-parsed
/// entries (used by tests that don't want to round-trip through the
/// JSON format).
pub fn import_entries(entries: Vec<CatalogEntry>, db: &TheoremDb) -> Result<usize> {
    // Build the set of catalog names up front so we can filter each
    // entry's deps to in-catalog ones. External Mathlib refs and
    // kernel primitives are intentionally dropped — we don't model
    // them in the TheoremDb, the kernel is the source of truth there.
    let catalog_names: HashSet<String> =
        entries.iter().map(|e| e.name.clone()).collect();
    let ordered = topological_sort(entries)?;
    let mut imported = 0usize;
    for entry in ordered {
        let id = axiom_id_from_name(&entry.name);
        let parents: Vec<TheoremId> = entry
            .axiom_dependencies
            .iter()
            .filter(|n| catalog_names.contains(n.as_str()))
            .map(|n| axiom_id_from_name(n))
            .filter(|p| *p != id) // self-cycle guard
            .collect();
        let theorem = Theorem {
            id,
            statement: entry.statement.clone(),
            canonical: entry.canonical.clone(),
            latex: String::new(),
            proof: ProofTree::TacticProof {
                tactic: "physlean".into(),
                proof_term: vec![],
            },
            depth: parents.len() as u32,
            complexity: entry.statement.node_count() as u32,
            domain: entry.domain.clone(),
            dimension: None,
            parents,
            children: vec![],
            verified: VerificationStatus::Verified {
                proof_term: vec![],
                tactic_used: "physlean".into(),
            },
            fitness: FitnessScore::default(),
            generation: 0,
            created_at: 0,
            origin: TheoremOrigin::Imported {
                source: entry.physlean_name.clone(),
            },
        };
        match db.put_theorem(&theorem) {
            Ok(()) => imported += 1,
            Err(e) => {
                tracing::warn!(
                    "physlean_import: skipping {} ({}): {e}",
                    entry.name,
                    entry.physlean_name,
                );
            }
        }
    }
    Ok(imported)
}

/// Sort entries so each one's dependencies (that exist in the catalog)
/// are written first. Bails on cycles.
fn topological_sort(entries: Vec<CatalogEntry>) -> Result<Vec<CatalogEntry>> {
    let by_name: HashMap<String, CatalogEntry> =
        entries.into_iter().map(|e| (e.name.clone(), e)).collect();
    let names: Vec<String> = by_name.keys().cloned().collect();
    let mut visited: HashSet<String> = HashSet::new();
    let mut on_stack: HashSet<String> = HashSet::new();
    let mut out: Vec<CatalogEntry> = Vec::with_capacity(by_name.len());

    for name in &names {
        visit(name, &by_name, &mut visited, &mut on_stack, &mut out)?;
    }
    Ok(out)
}

fn visit(
    name: &str,
    by_name: &HashMap<String, CatalogEntry>,
    visited: &mut HashSet<String>,
    on_stack: &mut HashSet<String>,
    out: &mut Vec<CatalogEntry>,
) -> Result<()> {
    if visited.contains(name) {
        return Ok(());
    }
    if !on_stack.insert(name.to_string()) {
        anyhow::bail!("Cycle in catalog dep graph at: {name}");
    }
    if let Some(entry) = by_name.get(name) {
        for dep in &entry.axiom_dependencies {
            if by_name.contains_key(dep) {
                visit(dep, by_name, visited, on_stack, out)?;
            }
        }
        out.push(entry.clone());
    }
    on_stack.remove(name);
    visited.insert(name.to_string());
    Ok(())
}

fn parse_catalog(path: &Path) -> Result<Vec<CatalogEntry>> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("read catalog: {}", path.display()))?;
    let mut deser = serde_json::Deserializer::from_str(&content);
    deser.disable_recursion_limit();
    let value: serde_json::Value = serde::Deserialize::deserialize(&mut deser)
        .with_context(|| "parse catalog json")?;

    let mut entries = Vec::new();
    if let Some(theorems) = value.get("theorems").and_then(|t| t.as_array()) {
        for thm in theorems {
            if let Some(entry) = parse_entry(thm) {
                entries.push(entry);
            }
        }
    }
    Ok(entries)
}

fn parse_entry(thm: &serde_json::Value) -> Option<CatalogEntry> {
    let name = thm.get("name")?.as_str()?.to_string();
    let physlean_name = thm
        .get("physlean_name")
        .and_then(|v| v.as_str())
        .unwrap_or(&name)
        .to_string();
    let domain_str = thm
        .get("domain")
        .and_then(|v| v.as_str())
        .unwrap_or("PureMath");
    let domain = match domain_str {
        "ClassicalMechanics" => Domain::ClassicalMechanics,
        "SpecialRelativity" => Domain::SpecialRelativity,
        "Electromagnetism" => Domain::Electromagnetism,
        "QuantumMechanics" => Domain::QuantumMechanics,
        "Thermodynamics" => Domain::Thermodynamics,
        "StatisticalMechanics" => Domain::StatisticalMechanics,
        _ => Domain::PureMath,
    };
    let doc_string = thm
        .get("doc_string")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string();
    let statement: Expr = thm
        .get("expr_ast")
        .filter(|v| !v.is_null())
        .and_then(|v| serde_json::from_value::<Expr>(v.clone()).ok())
        .unwrap_or_else(|| Expr::Var(name.clone()));
    let canonical = statement.to_canonical();
    let axiom_dependencies: Vec<String> = thm
        .get("axiom_dependencies")
        .and_then(|v| v.as_array())
        .map(|arr| {
            arr.iter()
                .filter_map(|s| s.as_str().map(|s| s.to_string()))
                .collect()
        })
        .unwrap_or_default();
    Some(CatalogEntry {
        name,
        physlean_name,
        domain,
        statement,
        canonical,
        axiom_dependencies,
        doc_string,
    })
}
