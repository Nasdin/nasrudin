use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "billing_events")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    #[sea_orm(unique)]
    pub stripe_event_id: String,
    pub event_type: String,
    #[sea_orm(column_type = "JsonBinary")]
    pub payload: Json,
    pub received_at: DateTimeWithTimeZone,
    pub processed_at: Option<DateTimeWithTimeZone>,
    pub process_error: Option<String>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
