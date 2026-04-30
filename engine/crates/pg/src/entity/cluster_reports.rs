//! Per-chunk per-cluster summary uploaded by workers. See migration
//! `m20260430_000017_cluster_reports` for the schema.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "cluster_reports")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i64,
    pub worker_id: Uuid,
    pub chunk_index: i64,
    pub k_used: i16,
    pub island_domain: String,
    pub cluster_id: i16,
    #[sea_orm(column_type = "JsonBinary")]
    pub summary: Json,
    pub received_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
