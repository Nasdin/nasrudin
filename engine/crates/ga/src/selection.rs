//! NSGA-II multi-objective selection.
//!
//! Implements non-dominated sorting (Pareto ranking) and crowding distance
//! assignment for maintaining a diverse set of high-quality solutions.

use rand::Rng;

use crate::individual::Individual;

/// Perform NSGA-II non-dominated sorting on a population.
///
/// Assigns `pareto_rank` to each individual: rank 0 is the first Pareto front
/// (non-dominated solutions), rank 1 is the second front, etc.
pub fn non_dominated_sort(individuals: &mut [Individual]) {
    let n = individuals.len();
    if n == 0 {
        return;
    }

    // domination_count[i] = number of individuals that dominate i
    let mut domination_count = vec![0usize; n];
    // dominated_set[i] = set of indices that i dominates
    let mut dominated_set: Vec<Vec<usize>> = vec![Vec::new(); n];

    // Compare all pairs
    for i in 0..n {
        for j in (i + 1)..n {
            if individuals[i].dominates(&individuals[j]) {
                dominated_set[i].push(j);
                domination_count[j] += 1;
            } else if individuals[j].dominates(&individuals[i]) {
                dominated_set[j].push(i);
                domination_count[i] += 1;
            }
        }
    }

    // Identify fronts
    let mut current_front: Vec<usize> = Vec::new();
    for i in 0..n {
        if domination_count[i] == 0 {
            individuals[i].pareto_rank = 0;
            current_front.push(i);
        }
    }

    let mut rank = 0;
    while !current_front.is_empty() {
        let mut next_front = Vec::new();
        for &i in &current_front {
            for &j in &dominated_set[i] {
                domination_count[j] -= 1;
                if domination_count[j] == 0 {
                    individuals[j].pareto_rank = rank + 1;
                    next_front.push(j);
                }
            }
        }
        rank += 1;
        current_front = next_front;
    }
}

/// Assign crowding distances to individuals within the same Pareto front.
///
/// Individuals at the boundary of objective space get infinite distance.
/// Others get distance proportional to their spread in each objective.
pub fn crowding_distance_assignment(individuals: &mut [Individual]) {
    let n = individuals.len();
    if n <= 2 {
        for ind in individuals.iter_mut() {
            ind.crowding_distance = f64::INFINITY;
        }
        return;
    }

    // Reset distances
    for ind in individuals.iter_mut() {
        ind.crowding_distance = 0.0;
    }

    // For each objective, sort and accumulate distance
    for obj_idx in 0..7 {
        // Sort by this objective
        let mut indices: Vec<usize> = (0..n).collect();
        indices.sort_by(|&a, &b| {
            let oa = individuals[a].objectives()[obj_idx];
            let ob = individuals[b].objectives()[obj_idx];
            oa.partial_cmp(&ob).unwrap_or(std::cmp::Ordering::Equal)
        });

        // Boundary individuals get infinite distance
        individuals[indices[0]].crowding_distance = f64::INFINITY;
        individuals[indices[n - 1]].crowding_distance = f64::INFINITY;

        // Range for normalization
        let obj_min = individuals[indices[0]].objectives()[obj_idx];
        let obj_max = individuals[indices[n - 1]].objectives()[obj_idx];
        let range = obj_max - obj_min;

        if range > 0.0 {
            for k in 1..(n - 1) {
                let prev = individuals[indices[k - 1]].objectives()[obj_idx];
                let next = individuals[indices[k + 1]].objectives()[obj_idx];
                individuals[indices[k]].crowding_distance += (next - prev) / range;
            }
        }
    }
}

/// Tournament selection using NSGA-II criteria.
///
/// Selects the better of `tournament_size` random individuals based on:
/// 1. Lower Pareto rank is better
/// 2. If same rank, higher crowding distance is better
pub fn tournament_select<'a>(
    individuals: &'a [Individual],
    tournament_size: usize,
    rng: &mut impl Rng,
) -> &'a Individual {
    let n = individuals.len();
    assert!(n > 0, "Cannot select from empty population");

    let mut best_idx = rng.random_range(0..n);
    for _ in 1..tournament_size {
        let challenger_idx = rng.random_range(0..n);
        if nsga2_compare(&individuals[challenger_idx], &individuals[best_idx])
            == std::cmp::Ordering::Less
        {
            best_idx = challenger_idx;
        }
    }
    &individuals[best_idx]
}

/// NSGA-II comparison: lower rank wins; if equal rank, higher crowding distance wins.
fn nsga2_compare(a: &Individual, b: &Individual) -> std::cmp::Ordering {
    match a.pareto_rank.cmp(&b.pareto_rank) {
        std::cmp::Ordering::Equal => {
            // Higher crowding distance is better (reverse order)
            b.crowding_distance
                .partial_cmp(&a.crowding_distance)
                .unwrap_or(std::cmp::Ordering::Equal)
        }
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_core::*;

    fn make_individual(objectives: [f64; 7]) -> Individual {
        let stmt = Expr::Var("x".into());
        let canonical = stmt.to_canonical();
        let id = compute_theorem_id(&canonical);
        let mut ind = Individual::new(Theorem {
            id,
            statement: stmt,
            canonical,
            latex: String::new(),
            proof: ProofTree::Axiom([0; 8]),
            depth: 1,
            complexity: 1,
            domain: Domain::PureMath,
            dimension: None,
            parents: vec![],
            children: vec![],
            verified: VerificationStatus::Pending,
            fitness: FitnessScore {
                novelty: objectives[0],
                complexity: objectives[1],
                depth: objectives[2],
                dimensional: objectives[3],
                symmetry: objectives[4],
                connectivity: objectives[5],
                nasrudin_relevance: objectives[6],
            },
            generation: 0,
            created_at: 0,
            origin: TheoremOrigin::Axiom,
        });
        ind.pareto_rank = usize::MAX;
        ind
    }

    #[test]
    fn non_dominated_sort_simple() {
        let mut pop = vec![
            make_individual([1.0, 0.0, 0.5, 1.0, 0.5, 0.5, 0.5]), // Pareto front 0
            make_individual([0.0, 1.0, 0.5, 1.0, 0.5, 0.5, 0.5]), // Pareto front 0
            make_individual([0.0, 0.0, 0.5, 1.0, 0.5, 0.5, 0.5]), // dominated by both
        ];
        non_dominated_sort(&mut pop);
        assert_eq!(pop[0].pareto_rank, 0);
        assert_eq!(pop[1].pareto_rank, 0);
        assert_eq!(pop[2].pareto_rank, 1);
    }

    #[test]
    fn crowding_distance_boundary() {
        let mut pop = vec![
            make_individual([0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            make_individual([0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5]),
            make_individual([1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]),
        ];
        crowding_distance_assignment(&mut pop);
        // Boundary individuals should have infinite distance
        assert!(pop[0].crowding_distance.is_infinite());
        assert!(pop[2].crowding_distance.is_infinite());
    }
}
