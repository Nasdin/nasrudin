use nasrudin_core::Domain;
use nasrudin_derive::AxiomStore;

#[test]
fn test_load_sr_axioms() {
    let mut store = AxiomStore::new();
    store.load_special_relativity();

    assert_eq!(store.len(), 4);
    assert!(store.get("mass_shell_condition").is_some());
    assert!(store.get("energy_nonneg").is_some());
    assert!(store.get("mass_nonneg").is_some());
    assert!(store.get("c_positive").is_some());
}

#[test]
fn test_axiom_lookup_by_name() {
    let mut store = AxiomStore::new();
    store.load_special_relativity();

    let axiom = store.get("mass_shell_condition").unwrap();
    assert_eq!(axiom.name, "mass_shell_condition");
    assert_eq!(axiom.domain, Domain::SpecialRelativity);
    assert!(axiom.description.contains("mass-shell") || axiom.description.contains("Mass-shell"));
}

#[test]
fn test_axiom_not_found() {
    let store = AxiomStore::new();
    assert!(store.get("nonexistent").is_none());
}

#[test]
fn test_domain_filter() {
    let mut store = AxiomStore::new();
    store.load_special_relativity();

    let sr_axioms = store.by_domain(&Domain::SpecialRelativity);
    assert_eq!(sr_axioms.len(), 4);

    let em_axioms = store.by_domain(&Domain::Electromagnetism);
    assert_eq!(em_axioms.len(), 0);
}

#[test]
fn test_mass_shell_is_equation() {
    use nasrudin_core::{BinOp, Expr};

    let mut store = AxiomStore::new();
    store.load_special_relativity();

    let axiom = store.get("mass_shell_condition").unwrap();
    // The mass-shell condition should be an equation (Eq)
    assert!(
        matches!(&axiom.statement, Expr::BinOp(BinOp::Eq, _, _)),
        "mass_shell_condition should be an equation, got: {:?}",
        axiom.statement
    );
}

#[test]
fn test_names_list() {
    let mut store = AxiomStore::new();
    store.load_special_relativity();

    let names = store.names();
    assert_eq!(names.len(), 4);
    assert!(names.contains(&"mass_shell_condition"));
    assert!(names.contains(&"c_positive"));
}
