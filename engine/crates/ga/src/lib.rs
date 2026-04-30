//! Genetic algorithm engine for physics theorem discovery.
//!
//! Evolves populations of theorem candidates using crossover, mutation,
//! and NSGA-II multi-objective selection. Domain-focused islands explore
//! different physics areas in parallel.

pub mod auto_size;
pub mod cache_bundle;
pub mod chain_engine;
pub mod chain_ga;
pub mod clustering;
pub mod config;
pub mod crossover;
pub mod dedup;
pub mod engine;
pub mod fitness;
pub mod individual;
pub mod island;
pub mod mutation;
pub mod beam;
pub mod paid_jobs_client;
pub mod paid_slice;
pub mod population;
pub mod research_client;
pub mod selection;
pub mod steering_knobs;
pub mod target;
pub mod worker_http;
pub mod worker_url;

pub use cache_bundle::CacheBundle;
pub use config::GaConfig;
pub use engine::{DiscoveryEvent, GaEngine, GaStatusSnapshot};
pub use individual::Individual;
pub use island::Island;
pub use population::Population;
