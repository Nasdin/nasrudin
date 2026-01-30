//! Genetic algorithm engine for physics theorem discovery.
//!
//! Evolves populations of theorem candidates using crossover, mutation,
//! and NSGA-II multi-objective selection. Domain-focused islands explore
//! different physics areas in parallel.

pub mod config;
pub mod crossover;
pub mod dedup;
pub mod engine;
pub mod fitness;
pub mod individual;
pub mod island;
pub mod mutation;
pub mod population;
pub mod selection;

pub use config::GaConfig;
pub use engine::{DiscoveryEvent, GaEngine};
pub use individual::Individual;
pub use island::Island;
pub use population::Population;
