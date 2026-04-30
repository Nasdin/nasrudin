use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "refund_records")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub user_id: Uuid,
    pub admin_user_id: Uuid,
    #[sea_orm(unique)]
    pub stripe_refund_id: Option<String>,
    pub stripe_charge_id: String,
    pub amount_cents: i32,
    pub currency: String,
    pub reason: String,
    pub status: String,
    pub stripe_failure_reason: Option<String>,
    pub requested_at: DateTimeWithTimeZone,
    pub completed_at: Option<DateTimeWithTimeZone>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
