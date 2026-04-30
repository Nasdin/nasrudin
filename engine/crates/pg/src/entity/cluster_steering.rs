//! Per-cycle history rows for the LLM cluster steerer.
//!
//! See migration `m20260501_000001_cluster_steering` for the schema.
//! `started_at` is used everywhere for ordering (prompt history is
//! newest-first, admin listings the same). `outcome_json` is filled
//! when the next cycle closes this one — see `query::cluster_steering`.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "cluster_steering")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub started_at: DateTimeWithTimeZone,
    pub ended_at: Option<DateTimeWithTimeZone>,
    pub scope: String,
    #[sea_orm(column_type = "JsonBinary")]
    pub config_json: Json,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub outcome_json: Option<Json>,
    pub validation_failed: bool,
    pub model_id: String,
    pub prompt_tokens: Option<i32>,
    pub completion_tokens: Option<i32>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
