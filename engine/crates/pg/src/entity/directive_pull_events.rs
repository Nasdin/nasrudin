//! Raw event log for the directive bandit. Each row is one
//! observed reward; the running aggregate lives in
//! `cluster_directive_arms`. See migration
//! `m20260430_000020_directive_pull_events`.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "directive_pull_events")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i64,
    pub island_domain: String,
    pub action: String,
    pub strength_bucket: i16,
    pub multiplier_choice: i16,
    pub reward: f64,
    pub received_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
