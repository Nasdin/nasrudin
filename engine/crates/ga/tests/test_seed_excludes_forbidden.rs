//! GA seed must skip any axiom whose synthetic id appears in the
//! caller-supplied `forbidden` set. Lets target-driven evolution
//! exclude the target itself + every theorem that transitively cites
//! it (the set returned by `TheoremDb::forbidden_for_target`).

use nasrudin_core::{Domain, axiom_id_from_name};
use nasrudin_derive::AxiomStore;
use nasrudin_ga::config::GaConfig;
use nasrudin_ga::island::Island;
use rand::SeedableRng;
use rand::rngs::StdRng;
use std::collections::HashSet;

#[test]
fn seed_from_axioms_excluding_skips_forbidden() {
    let mut store = AxiomStore::new();
    store.load_special_relativity_upstream();

    let mut forbidden = HashSet::new();
    forbidden.insert(axiom_id_from_name("rest_frame_psq_zero"));

    let mut config = GaConfig::default();
    config.population_size = 16;
    let mut island = Island::new(Domain::SpecialRelativity, config);
    let mut rng = StdRng::seed_from_u64(42);
    island.seed_from_axioms_excluding(&store, &mut rng, &forbidden);

    // The forbidden axiom's canonical statement must not appear in the
    // population. We can't index by name on Individuals (they hold
    // Theorems with statements + canonicals, not source-axiom names),
    // so we check by canonical match against the axiom we excluded.
    let excluded_canonical = store
        .get("rest_frame_psq_zero")
        .expect("upstream load registered rest_frame_psq_zero")
        .statement
        .to_canonical();

    let leaked = island
        .population
        .individuals
        .iter()
        .any(|ind| ind.theorem.canonical == excluded_canonical);
    assert!(!leaked, "rest_frame_psq_zero must not appear in seed");
}
