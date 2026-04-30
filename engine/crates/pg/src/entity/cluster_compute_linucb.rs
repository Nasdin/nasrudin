//! Per-island LinUCB sufficient statistics for the compute-scaling
//! bandit. See migration `m20260430_000025_cluster_compute_linucb`.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "cluster_compute_linucb")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub island_domain: String,
    pub a_matrix: Vec<f64>,
    pub b_vector: Vec<f64>,
    pub pulls: i64,
    pub updated_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
