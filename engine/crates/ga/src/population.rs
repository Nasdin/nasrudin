use std::collections::HashSet;

use nasrudin_core::{Domain, TheoremId};

use crate::individual::Individual;

/// A population of theorem candidates for a single island.
#[derive(Debug)]
pub struct Population {
    /// Current individuals in this population.
    pub individuals: Vec<Individual>,
    /// Current generation number.
    pub generation: u64,
    /// Physics domain focus for this island.
    pub domain: Domain,
    /// Canonical hash set for deduplication within this population.
    seen_ids: HashSet<TheoremId>,
}

impl Population {
    /// Create an empty population for a given domain.
    pub fn new(domain: Domain) -> Self {
        Self {
            individuals: Vec::new(),
            generation: 0,
            domain,
            seen_ids: HashSet::new(),
        }
    }

    /// Create a population with pre-allocated capacity.
    pub fn with_capacity(domain: Domain, capacity: usize) -> Self {
        Self {
            individuals: Vec::with_capacity(capacity),
            generation: 0,
            domain,
            seen_ids: HashSet::with_capacity(capacity),
        }
    }

    /// Add an individual if it's not a duplicate.
    /// Returns true if the individual was added.
    pub fn add(&mut self, individual: Individual) -> bool {
        let id = individual.theorem.id;
        if self.seen_ids.contains(&id) {
            return false;
        }
        self.seen_ids.insert(id);
        self.individuals.push(individual);
        true
    }

    /// Replace the population with a new set of individuals (next generation).
    pub fn replace(&mut self, new_individuals: Vec<Individual>) {
        self.seen_ids.clear();
        for ind in &new_individuals {
            self.seen_ids.insert(ind.theorem.id);
        }
        self.individuals = new_individuals;
        self.generation += 1;
    }

    /// Number of individuals in the population.
    pub fn len(&self) -> usize {
        self.individuals.len()
    }

    /// Check if the population is empty.
    pub fn is_empty(&self) -> bool {
        self.individuals.is_empty()
    }

    /// Check if a theorem ID already exists in this population.
    pub fn contains(&self, id: &TheoremId) -> bool {
        self.seen_ids.contains(id)
    }

    /// Get the best individuals by Pareto rank (rank 0 = first front).
    pub fn front(&self, rank: usize) -> Vec<&Individual> {
        self.individuals
            .iter()
            .filter(|ind| ind.pareto_rank == rank)
            .collect()
    }
}
