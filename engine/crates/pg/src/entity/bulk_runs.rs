use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "bulk_runs")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub started_by_admin_id: Uuid,
    pub action: String,
    #[sea_orm(column_type = "JsonBinary")]
    pub params: Json,
    pub total_count: i32,
    pub completed_count: i32,
    pub failed_count: i32,
    pub status: String,
    pub started_at: DateTimeWithTimeZone,
    pub completed_at: Option<DateTimeWithTimeZone>,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub failures: Option<Json>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
