//! Importing PhysLean catalog entries into TheoremDb populates the
//! lineage and reverse-deps indexes correctly, even though the proof
//! tree is opaque (TacticProof). The acyclicity infra works against
//! the explicit `parents` list.

use nasrudin_core::{axiom_id_from_name, Domain, Expr};
use nasrudin_derive::physlean_import::{import_entries, CatalogEntry};
use nasrudin_rocks::TheoremDb;
use tempfile::TempDir;

fn entry(name: &str, deps: &[&str]) -> CatalogEntry {
    let statement = Expr::Var(name.into());
    let canonical = statement.to_canonical();
    CatalogEntry {
        name: name.into(),
        physlean_name: format!("PhysLean::Test::{name}"),
        domain: Domain::SpecialRelativity,
        statement,
        canonical,
        axiom_dependencies: deps.iter().map(|s| s.to_string()).collect(),
        doc_string: String::new(),
    }
}

#[test]
fn import_chain_populates_lineage_and_reverse_deps() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // A → B → C linear chain. Pass entries in REVERSE order so we
    // exercise the topological sort.
    let entries = vec![entry("c", &["b"]), entry("b", &["a"]), entry("a", &[])];
    let count = import_entries(entries, &db).unwrap();
    assert_eq!(count, 3);

    let a_id = axiom_id_from_name("a");
    let b_id = axiom_id_from_name("b");
    let c_id = axiom_id_from_name("c");

    // Lineage on C must include A (transitive) and B (immediate).
    let lin_c = db.get_lineage(&c_id).unwrap().unwrap();
    let ancestors: std::collections::HashSet<_> =
        lin_c.axiom_ancestors.iter().copied().collect();
    assert!(ancestors.contains(&a_id), "C must transitively cite A");
    assert!(ancestors.contains(&b_id), "C must directly cite B");

    // Reverse-deps: A's dependents include both B and C.
    let mut deps_a = db.list_dependents(&a_id).unwrap();
    deps_a.sort();
    let mut expected = vec![b_id, c_id];
    expected.sort();
    assert_eq!(deps_a, expected);

    // forbidden_for_target(A) excludes the target + the whole chain.
    let f = db.forbidden_for_target(&a_id).unwrap();
    assert!(f.contains(&a_id));
    assert!(f.contains(&b_id));
    assert!(f.contains(&c_id));
}

#[test]
fn import_skips_external_deps() {
    // Real catalog entries cite Mathlib lemmas we never extract. The
    // importer must drop those deps silently rather than synthesising
    // ghost theorems.
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let entries = vec![entry(
        "physlean_thm",
        &["physlean_thm_dep", "Real.add_comm", "Mathlib.kernel.eq_refl"],
    )];
    let count = import_entries(entries, &db).unwrap();
    assert_eq!(count, 1);

    // The single imported theorem has no in-store parents (every dep
    // was external). axiom_ancestors should be empty.
    let id = axiom_id_from_name("physlean_thm");
    let lin = db.get_lineage(&id).unwrap().unwrap();
    assert!(
        lin.axiom_ancestors.is_empty(),
        "external deps must not become parent theorems; got {:?}",
        lin.axiom_ancestors,
    );
}

#[test]
fn import_rejects_cycles() {
    // Lean enforces DAG so this shouldn't occur in real catalogs, but
    // we guard against malformed input.
    let entries = vec![
        entry("alpha", &["beta"]),
        entry("beta", &["alpha"]),
    ];
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
    let err = import_entries(entries, &db).unwrap_err();
    let msg = format!("{err:?}");
    assert!(msg.to_lowercase().contains("cycle"), "got: {msg}");
}
