use sea_orm::entity::prelude::*;

/// Worker status stored as TEXT in PostgreSQL.
#[derive(Debug, Clone, PartialEq, Eq, EnumIter, DeriveActiveEnum)]
#[sea_orm(rs_type = "String", db_type = "Text")]
pub enum WorkerStatus {
    #[sea_orm(string_value = "active")]
    Active,
    #[sea_orm(string_value = "inactive")]
    Inactive,
    #[sea_orm(string_value = "disconnected")]
    Disconnected,
}

/// Distributed worker registry.
///
/// Workers register via POST /api/workers/register and receive a text ID.
/// They heartbeat periodically to update `last_seen` and `theorems_contributed`.
#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "workers")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false, column_type = "Text")]
    pub id: String,
    pub name: Option<String>,
    pub host: Option<String>,
    pub last_seen: DateTimeWithTimeZone,
    pub theorems_contributed: i64,
    pub status: WorkerStatus,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
