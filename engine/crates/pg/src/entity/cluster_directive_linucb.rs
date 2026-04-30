//! Sufficient statistics for the per-(island, action) LinUCB
//! contextual bandit. See migration
//! `m20260430_000024_cluster_directive_linucb`.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "cluster_directive_linucb")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub island_domain: String,
    #[sea_orm(primary_key, auto_increment = false)]
    pub action: String,
    /// Row-major 6×6 = 36 doubles.
    pub a_matrix: Vec<f64>,
    /// Length-6 vector.
    pub b_vector: Vec<f64>,
    pub pulls: i64,
    pub updated_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
