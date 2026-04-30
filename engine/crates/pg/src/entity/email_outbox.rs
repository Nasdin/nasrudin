use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "email_outbox")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub to_user_id: Option<Uuid>,
    pub to_address: String,
    pub template: String,
    pub subject: String,
    #[sea_orm(column_type = "Text")]
    pub body_text: String,
    #[sea_orm(column_type = "Text", nullable)]
    pub body_html: Option<String>,
    pub status: String,
    pub attempts: i32,
    pub last_attempt_at: Option<DateTimeWithTimeZone>,
    pub last_error: Option<String>,
    pub provider_message_id: Option<String>,
    pub queued_by_admin_id: Option<Uuid>,
    pub queued_by_action: Option<String>,
    pub created_at: DateTimeWithTimeZone,
    pub sent_at: Option<DateTimeWithTimeZone>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
