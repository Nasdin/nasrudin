use serde::{Deserialize, Serialize};

/// Configuration for the genetic algorithm engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GaConfig {
    /// Number of individuals per island population.
    pub population_size: usize,
    /// Probability of crossover between two parents.
    pub crossover_rate: f64,
    /// Probability of mutating an offspring.
    pub mutation_rate: f64,
    /// Tournament selection size for NSGA-II.
    pub tournament_size: usize,
    /// Maximum AST node count before an individual is rejected.
    pub max_complexity: usize,
    /// Maximum AST depth before an individual is rejected.
    pub max_depth: u32,
    /// Number of islands (one per physics domain).
    pub num_islands: usize,
    /// How many generations between island migration events.
    pub migration_interval: u64,
    /// Number of individuals exchanged during migration.
    pub migration_size: usize,
    /// Number of candidate theorems to batch-send for Lean verification.
    pub verification_batch_size: usize,
    /// How often (in generations) to send candidates for verification.
    pub verification_interval: u64,
    /// Bloom filter capacity per island for deduplication (items).
    pub bloom_capacity: usize,
}

impl Default for GaConfig {
    fn default() -> Self {
        Self {
            population_size: 200,
            crossover_rate: 0.7,
            mutation_rate: 0.3,
            tournament_size: 5,
            max_complexity: 50,
            max_depth: 15,
            num_islands: 6,
            migration_interval: 10,
            migration_size: 5,
            verification_batch_size: 10,
            verification_interval: 5,
            bloom_capacity: 10_000_000,
        }
    }
}
