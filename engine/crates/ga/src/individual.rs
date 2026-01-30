use nasrudin_core::{FitnessScore, Theorem};

/// A single individual in the GA population.
///
/// Wraps a `Theorem` candidate with NSGA-II selection metadata:
/// Pareto rank and crowding distance.
#[derive(Debug, Clone)]
pub struct Individual {
    /// The theorem candidate.
    pub theorem: Theorem,
    /// NSGA-II Pareto front rank (0 = first front, best).
    pub pareto_rank: usize,
    /// NSGA-II crowding distance (higher = more diverse).
    pub crowding_distance: f64,
}

impl Individual {
    /// Create a new individual from a theorem.
    pub fn new(theorem: Theorem) -> Self {
        Self {
            theorem,
            pareto_rank: usize::MAX,
            crowding_distance: 0.0,
        }
    }

    /// Access the fitness scores for this individual.
    pub fn fitness(&self) -> &FitnessScore {
        &self.theorem.fitness
    }

    /// Get the 7 fitness objectives as a fixed-size array for NSGA-II.
    pub fn objectives(&self) -> [f64; 7] {
        let f = &self.theorem.fitness;
        [
            f.novelty,
            f.complexity,
            f.depth,
            f.dimensional,
            f.symmetry,
            f.connectivity,
            f.nasrudin_relevance,
        ]
    }

    /// Returns true if this individual dominates `other` in all objectives.
    /// (Higher is better for all objectives.)
    pub fn dominates(&self, other: &Individual) -> bool {
        let a = self.objectives();
        let b = other.objectives();
        let mut dominated_any = false;
        for i in 0..7 {
            if a[i] < b[i] {
                return false;
            }
            if a[i] > b[i] {
                dominated_any = true;
            }
        }
        dominated_any
    }
}
