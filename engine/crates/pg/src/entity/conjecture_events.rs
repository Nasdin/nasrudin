use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "conjecture_events")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i64,
    pub job_id: Uuid,
    pub kind: String,
    #[sea_orm(column_type = "JsonBinary")]
    pub payload: Json,
    pub at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(
        belongs_to = "super::conjecture_jobs::Entity",
        from = "Column::JobId",
        to = "super::conjecture_jobs::Column::Id",
        on_delete = "Cascade"
    )]
    Job,
}

impl Related<super::conjecture_jobs::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::Job.def()
    }
}

impl ActiveModelBehavior for ActiveModel {}
