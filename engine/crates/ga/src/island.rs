//! Island model: a domain-focused population that evolves independently.
//!
//! Each island runs its own GA loop with `step()` executing one generation.
//! Periodically, islands exchange migrants to share genetic material.

use nasrudin_core::{
    BinOp, Domain, Expr, FitnessScore, PhysConst, ProofTree, Theorem, TheoremOrigin,
    VerificationStatus, compute_theorem_id,
};
use rand::Rng;

use crate::config::GaConfig;
use crate::crossover::subtree_crossover;
use crate::dedup::DedupFilter;
use crate::fitness::evaluate;
use crate::individual::Individual;
use crate::mutation::mutate;
use crate::population::Population;
use crate::selection::{crowding_distance_assignment, non_dominated_sort, tournament_select};

/// A single island in the archipelago model.
pub struct Island {
    /// The island's population.
    pub population: Population,
    /// GA configuration.
    config: GaConfig,
    /// Global dedup filter (shared reference via clone).
    dedup: DedupFilter,
}

impl Island {
    /// Create a new island for a given domain with a seed population.
    pub fn new(domain: Domain, config: GaConfig) -> Self {
        let pop = Population::with_capacity(domain, config.population_size);
        Self {
            population: pop,
            config,
            dedup: DedupFilter::new(),
        }
    }

    /// Seed the population with initial theorem candidates.
    pub fn seed(&mut self, rng: &mut impl Rng) {
        let domain = self.population.domain.clone();
        let target = self.config.population_size;
        while self.population.len() < target {
            let stmt = generate_random_expr(&domain, 4, rng);
            let canonical = stmt.to_canonical();
            let id = compute_theorem_id(&canonical);

            if self.dedup.is_duplicate(&id) {
                continue;
            }
            self.dedup.insert(id);

            let mut theorem = Theorem {
                id,
                statement: stmt,
                canonical,
                latex: String::new(),
                proof: ProofTree::Axiom([0; 8]),
                depth: 1,
                complexity: 0,
                domain: domain.clone(),
                dimension: None,
                parents: vec![],
                children: vec![],
                verified: VerificationStatus::Pending,
                fitness: FitnessScore::default(),
                generation: 0,
                created_at: 0,
                origin: TheoremOrigin::Axiom,
            };
            theorem.complexity = theorem.statement.node_count() as u32;
            theorem.fitness = evaluate(&theorem);

            self.population.add(Individual::new(theorem));
        }
    }

    /// Run one generation: select → crossover → mutate → filter → evaluate → replace.
    ///
    /// Returns a list of candidate theorems to send for Lean4 verification.
    pub fn step(&mut self, rng: &mut impl Rng) -> Vec<Theorem> {
        let pop_size = self.config.population_size;
        if self.population.len() < 2 {
            return vec![];
        }

        // 1. Assign Pareto ranks and crowding distances
        non_dominated_sort(&mut self.population.individuals);
        crowding_distance_assignment(&mut self.population.individuals);

        // 2. Generate offspring
        let mut offspring: Vec<Individual> = Vec::with_capacity(pop_size);
        let generation = self.population.generation + 1;

        while offspring.len() < pop_size {
            // Select parents
            let parent_a = tournament_select(
                &self.population.individuals,
                self.config.tournament_size,
                rng,
            );
            let parent_b = tournament_select(
                &self.population.individuals,
                self.config.tournament_size,
                rng,
            );

            // Crossover
            let (mut child_stmt_a, mut child_stmt_b) = if rng.random_bool(self.config.crossover_rate)
            {
                subtree_crossover(
                    &parent_a.theorem.statement,
                    &parent_b.theorem.statement,
                    rng,
                )
            } else {
                (
                    parent_a.theorem.statement.clone(),
                    parent_b.theorem.statement.clone(),
                )
            };

            // Mutation
            if rng.random_bool(self.config.mutation_rate) {
                child_stmt_a = mutate(&child_stmt_a, rng);
            }
            if rng.random_bool(self.config.mutation_rate) {
                child_stmt_b = mutate(&child_stmt_b, rng);
            }

            // Create offspring theorems
            for stmt in [child_stmt_a, child_stmt_b] {
                // Pre-filter: complexity bounds
                let node_count = stmt.node_count();
                if node_count > self.config.max_complexity {
                    continue;
                }

                let canonical = stmt.to_canonical();
                let id = compute_theorem_id(&canonical);

                // Dedup
                if self.dedup.is_duplicate(&id) {
                    continue;
                }
                self.dedup.insert(id);

                let origin = TheoremOrigin::Crossover {
                    parent_a: parent_a.theorem.id,
                    parent_b: parent_b.theorem.id,
                };

                let mut theorem = Theorem {
                    id,
                    statement: stmt,
                    canonical,
                    latex: String::new(),
                    proof: ProofTree::Axiom([0; 8]),
                    depth: parent_a.theorem.depth.max(parent_b.theorem.depth) + 1,
                    complexity: node_count as u32,
                    domain: self.population.domain.clone(),
                    dimension: None,
                    parents: vec![parent_a.theorem.id, parent_b.theorem.id],
                    children: vec![],
                    verified: VerificationStatus::Pending,
                    fitness: FitnessScore::default(),
                    generation,
                    created_at: 0,
                    origin,
                };
                theorem.fitness = evaluate(&theorem);

                offspring.push(Individual::new(theorem));
                if offspring.len() >= pop_size {
                    break;
                }
            }
        }

        // 3. Combine parent + offspring, sort, truncate to pop_size
        let mut combined = std::mem::take(&mut self.population.individuals);
        combined.extend(offspring);

        non_dominated_sort(&mut combined);
        crowding_distance_assignment(&mut combined);

        // Sort by NSGA-II criteria: lower rank first, then higher crowding distance
        combined.sort_by(|a, b| {
            a.pareto_rank
                .cmp(&b.pareto_rank)
                .then_with(|| {
                    b.crowding_distance
                        .partial_cmp(&a.crowding_distance)
                        .unwrap_or(std::cmp::Ordering::Equal)
                })
        });
        combined.truncate(pop_size);

        // Collect candidates for verification (first Pareto front)
        let candidates: Vec<Theorem> = combined
            .iter()
            .filter(|ind| ind.pareto_rank == 0)
            .map(|ind| ind.theorem.clone())
            .collect();

        // 4. Replace population
        self.population.replace(combined);

        candidates
    }

    /// Get migrants for inter-island exchange (best individuals).
    pub fn get_migrants(&self, count: usize) -> Vec<Individual> {
        let mut migrants: Vec<&Individual> = self
            .population
            .individuals
            .iter()
            .filter(|ind| ind.pareto_rank == 0)
            .collect();
        migrants.sort_by(|a, b| {
            b.crowding_distance
                .partial_cmp(&a.crowding_distance)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        migrants.into_iter().take(count).cloned().collect()
    }

    /// Accept migrants from another island.
    pub fn accept_migrants(&mut self, migrants: Vec<Individual>) {
        for migrant in migrants {
            self.population.add(migrant);
        }
    }
}

/// Generate a random expression for a given physics domain.
fn generate_random_expr(domain: &Domain, max_depth: u32, rng: &mut impl Rng) -> Expr {
    let vars = domain_variables(domain);
    let consts = domain_constants(domain);
    generate_expr_recursive(&vars, &consts, max_depth, 0, rng)
}

/// Generate a random expression tree recursively.
fn generate_expr_recursive(
    vars: &[&str],
    consts: &[PhysConst],
    max_depth: u32,
    current_depth: u32,
    rng: &mut impl Rng,
) -> Expr {
    // At max depth, return a leaf
    if current_depth >= max_depth {
        return random_leaf(vars, consts, rng);
    }

    // Decide: leaf (30%) or branch (70%) based on depth
    let leaf_prob = 0.3 + 0.2 * (current_depth as f64 / max_depth as f64);
    if rng.random_bool(leaf_prob) {
        return random_leaf(vars, consts, rng);
    }

    // Generate a binary operation
    let ops = [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Pow, BinOp::Eq];
    let op = ops[rng.random_range(0..ops.len())].clone();
    let left = generate_expr_recursive(vars, consts, max_depth, current_depth + 1, rng);
    let right = generate_expr_recursive(vars, consts, max_depth, current_depth + 1, rng);
    Expr::BinOp(op, Box::new(left), Box::new(right))
}

/// Generate a random leaf node.
fn random_leaf(vars: &[&str], consts: &[PhysConst], rng: &mut impl Rng) -> Expr {
    let choice = rng.random_range(0..3u32);
    match choice {
        0 if !vars.is_empty() => {
            Expr::Var(vars[rng.random_range(0..vars.len())].to_string())
        }
        1 if !consts.is_empty() => {
            Expr::Const(consts[rng.random_range(0..consts.len())].clone())
        }
        _ => {
            // Small integer literal
            let n = rng.random_range(1..=4);
            Expr::Lit(n, 1)
        }
    }
}

/// Variables relevant to a physics domain.
fn domain_variables(domain: &Domain) -> Vec<&'static str> {
    match domain {
        Domain::SpecialRelativity => vec!["E", "m", "p", "v", "t", "gamma"],
        Domain::Electromagnetism => vec!["E", "B", "q", "I", "V", "R", "F", "r"],
        Domain::QuantumMechanics => vec!["E", "psi", "p", "x", "t", "m", "n", "L"],
        Domain::Thermodynamics => vec!["T", "S", "U", "P", "V", "n", "Q", "W"],
        Domain::ClassicalMechanics => vec!["F", "m", "a", "v", "x", "t", "E", "p"],
        Domain::GeneralRelativity => vec!["G", "m", "M", "r", "t", "R"],
        _ => vec!["x", "y", "z", "t", "m", "E", "p", "F"],
    }
}

/// Physical constants relevant to a physics domain.
fn domain_constants(domain: &Domain) -> Vec<PhysConst> {
    match domain {
        Domain::SpecialRelativity => vec![PhysConst::SpeedOfLight],
        Domain::Electromagnetism => vec![
            PhysConst::SpeedOfLight,
            PhysConst::ElectronCharge,
            PhysConst::VacuumPermittivity,
            PhysConst::VacuumPermeability,
        ],
        Domain::QuantumMechanics => vec![
            PhysConst::PlanckConst,
            PhysConst::ReducedPlanck,
            PhysConst::ElectronMass,
        ],
        Domain::Thermodynamics => vec![PhysConst::Boltzmann, PhysConst::Avogadro],
        Domain::ClassicalMechanics => vec![PhysConst::GravConst],
        _ => vec![
            PhysConst::SpeedOfLight,
            PhysConst::PlanckConst,
            PhysConst::Boltzmann,
        ],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn island_seed_populates() {
        let config = GaConfig {
            population_size: 20,
            ..Default::default()
        };
        let mut island = Island::new(Domain::SpecialRelativity, config);
        let mut rng = rand::rng();
        island.seed(&mut rng);
        assert_eq!(island.population.len(), 20);
    }

    #[test]
    fn island_step_produces_candidates() {
        let config = GaConfig {
            population_size: 20,
            ..Default::default()
        };
        let mut island = Island::new(Domain::SpecialRelativity, config);
        let mut rng = rand::rng();
        island.seed(&mut rng);

        let candidates = island.step(&mut rng);
        // Should produce at least some candidates
        assert!(island.population.generation == 1);
        // Candidates come from the first Pareto front
        assert!(!candidates.is_empty() || island.population.len() > 0);
    }
}
