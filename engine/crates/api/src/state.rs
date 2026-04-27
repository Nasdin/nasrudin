//! Shared application state.

use std::sync::{Arc, Mutex};

use nasrudin_derive::AxiomStore;
use nasrudin_ga::{DiscoveryEvent, GaStatusSnapshot};
use nasrudin_rocks::TheoremDb;

pub struct AppState {
    pub db: Arc<TheoremDb>,
    pub pg: Option<nasrudin_pg::sea_orm::DatabaseConnection>,
    pub axiom_store: Arc<AxiomStore>,
    pub discovery_tx: tokio::sync::broadcast::Sender<DiscoveryEvent>,
    pub ga_status: Arc<Mutex<GaStatusSnapshot>>,
}
