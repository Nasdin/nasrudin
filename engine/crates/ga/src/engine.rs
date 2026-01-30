//! GA engine: coordinates multiple islands and provides a channel-based interface.
//!
//! The engine runs on a dedicated `std::thread` (CPU-bound) and communicates
//! with the async API server via channels.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use nasrudin_core::{Domain, Theorem};
use nasrudin_rocks::TheoremDb;
use rand::Rng;
use serde::{Deserialize, Serialize};

use crate::config::GaConfig;
use crate::island::Island;

/// An event emitted when the GA discovers an interesting theorem candidate.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiscoveryEvent {
    /// Hex-encoded theorem ID.
    pub theorem_id: String,
    /// Canonical prefix notation.
    pub canonical: String,
    /// LaTeX representation (may be empty).
    pub latex: String,
    /// Physics domain.
    pub domain: String,
    /// AST depth.
    pub depth: u32,
    /// Generation when discovered.
    pub generation: u64,
    /// Fitness scores.
    pub fitness: nasrudin_core::FitnessScore,
    /// Unix timestamp.
    pub timestamp: u64,
}

/// Current status of the GA engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GaStatus {
    /// Total generations across all islands.
    pub total_generations: u64,
    /// Total population across all islands.
    pub total_population: usize,
    /// Number of active islands.
    pub num_islands: usize,
    /// Total candidates sent for verification.
    pub candidates_sent: u64,
    /// Total verified discoveries.
    pub verified_discoveries: u64,
    /// Whether the engine is running.
    pub running: bool,
}

/// The main genetic algorithm engine.
///
/// Coordinates multiple domain-focused islands and communicates results
/// via channels.
pub struct GaEngine {
    islands: Vec<Island>,
    config: GaConfig,
    db: Arc<TheoremDb>,
    candidates_sent: u64,
    verified_discoveries: u64,
}

impl GaEngine {
    /// Create a new GA engine.
    pub fn new(config: GaConfig, db: Arc<TheoremDb>) -> Self {
        let domains = default_domains();
        let islands: Vec<Island> = domains
            .into_iter()
            .take(config.num_islands)
            .map(|domain| Island::new(domain, config.clone()))
            .collect();

        Self {
            islands,
            config,
            db,
            candidates_sent: 0,
            verified_discoveries: 0,
        }
    }

    /// Run the GA engine loop on a dedicated thread.
    ///
    /// - `candidates_tx`: send candidate batches for Lean4 verification
    /// - `verified_rx`: receive verified results back
    /// - `discovery_tx`: broadcast discovery events for SSE
    /// - `shutdown`: set to true to stop the engine
    pub fn run(
        mut self,
        candidates_tx: std::sync::mpsc::Sender<Vec<Theorem>>,
        verified_rx: std::sync::mpsc::Receiver<Vec<Theorem>>,
        discovery_tx: tokio::sync::broadcast::Sender<DiscoveryEvent>,
        shutdown: Arc<AtomicBool>,
    ) {
        tracing::info!("GA engine starting with {} islands", self.islands.len());

        let mut rng = rand::rng();

        // Seed all islands: first load from DB, then fill remainder with random
        for island in &mut self.islands {
            island.seed_from_db(&self.db, &mut rng);
            tracing::info!(
                "Seeded island {:?} with {} individuals",
                island.population.domain,
                island.population.len()
            );
        }

        let mut generation: u64 = 0;

        while !shutdown.load(Ordering::Relaxed) {
            generation += 1;

            // Step each island and collect candidates
            let mut all_candidates: Vec<Theorem> = Vec::new();
            for island in &mut self.islands {
                let candidates = island.step(&mut rng);
                all_candidates.extend(candidates);
            }

            // Send candidates for verification (batch)
            if !all_candidates.is_empty()
                && generation % self.config.verification_interval == 0
            {
                let batch: Vec<Theorem> = all_candidates
                    .into_iter()
                    .take(self.config.verification_batch_size)
                    .collect();
                self.candidates_sent += batch.len() as u64;

                if candidates_tx.send(batch).is_err() {
                    tracing::warn!("Verification channel closed, stopping GA");
                    break;
                }
            }

            // Check for verified results (non-blocking)
            while let Ok(verified_batch) = verified_rx.try_recv() {
                for theorem in verified_batch {
                    self.verified_discoveries += 1;

                    // Store in RocksDB
                    if let Err(e) = self.db.put_theorem(&theorem) {
                        tracing::error!("Failed to store verified theorem: {e}");
                        continue;
                    }

                    // Update lineage: register this theorem as a child of each parent
                    for parent_id in &theorem.parents {
                        let _ = self.db.add_child(parent_id, theorem.id);
                    }

                    // Broadcast discovery event
                    let event = DiscoveryEvent {
                        theorem_id: hex::encode(theorem.id),
                        canonical: theorem.canonical.clone(),
                        latex: theorem.latex.clone(),
                        domain: theorem.domain.to_string(),
                        depth: theorem.depth,
                        generation: theorem.generation,
                        fitness: theorem.fitness.clone(),
                        timestamp: std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .unwrap_or_default()
                            .as_secs(),
                    };

                    // Ignore send errors (no subscribers is ok)
                    let _ = discovery_tx.send(event);
                }
            }

            // Inter-island migration
            if generation % self.config.migration_interval == 0 && self.islands.len() > 1 {
                self.migrate(&mut rng);
            }

            // Log progress periodically
            if generation % 100 == 0 {
                let total_pop: usize = self.islands.iter().map(|i| i.population.len()).sum();
                tracing::info!(
                    "GA generation {generation}: {total_pop} total individuals, {} candidates sent, {} verified",
                    self.candidates_sent,
                    self.verified_discoveries
                );
            }

            // Small yield to prevent busy-spinning
            std::thread::sleep(std::time::Duration::from_millis(1));
        }

        tracing::info!("GA engine shutting down after {generation} generations");
    }

    /// Get the current engine status.
    pub fn status(&self) -> GaStatus {
        GaStatus {
            total_generations: self.islands.iter().map(|i| i.population.generation).sum(),
            total_population: self.islands.iter().map(|i| i.population.len()).sum(),
            num_islands: self.islands.len(),
            candidates_sent: self.candidates_sent,
            verified_discoveries: self.verified_discoveries,
            running: true,
        }
    }

    /// Perform inter-island migration: ring topology.
    fn migrate(&mut self, rng: &mut impl Rng) {
        let n = self.islands.len();
        if n < 2 {
            return;
        }

        let migration_size = self.config.migration_size;

        // Collect migrants from each island
        let all_migrants: Vec<Vec<_>> = self
            .islands
            .iter()
            .map(|island| island.get_migrants(migration_size))
            .collect();

        // Ring topology: island i sends to island (i+1) % n
        for i in 0..n {
            let target = (i + 1) % n;
            let migrants = all_migrants[i].clone();
            if !migrants.is_empty() {
                self.islands[target].accept_migrants(migrants);
                tracing::debug!("Migrated {} individuals from island {i} to {target}", migration_size);
            }
        }

        let _ = rng; // used for future stochastic migration
    }
}

/// Default physics domains for the island model.
fn default_domains() -> Vec<Domain> {
    vec![
        Domain::SpecialRelativity,
        Domain::Electromagnetism,
        Domain::QuantumMechanics,
        Domain::Thermodynamics,
        Domain::ClassicalMechanics,
        Domain::GeneralRelativity,
    ]
}
