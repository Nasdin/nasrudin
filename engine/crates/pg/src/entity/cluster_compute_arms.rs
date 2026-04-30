//! UCB1 arm state for the compute-scaling bandit. PK is
//! (island_domain, strength_bucket, multiplier_choice). See
//! migration `m20260430_000021_cluster_compute_arms`.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "cluster_compute_arms")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub island_domain: String,
    #[sea_orm(primary_key, auto_increment = false)]
    pub strength_bucket: i16,
    #[sea_orm(primary_key, auto_increment = false)]
    pub multiplier_choice: i16,
    pub pulls: i64,
    pub total_reward: f64,
    pub last_reward: f64,
    pub updated_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
