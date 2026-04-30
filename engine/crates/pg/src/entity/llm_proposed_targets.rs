//! LLM-proposed self-curriculum targets. See migration
//! `m20260430_000023_llm_proposed_targets`.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "llm_proposed_targets")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub target_id: String,
    pub latex: String,
    pub domain: String,
    pub weight: f64,
    pub status: String,
    pub proposed_at: DateTimeWithTimeZone,
    pub updated_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
