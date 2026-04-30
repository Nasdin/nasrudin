//! `admin_audit_log` — immutable record of every admin mutation.
//!
//! `request_ip` is stored as Postgres `inet` but kept as `String` here
//! because SeaORM's `Inet` mapping is unstable across versions. The
//! `query::admin_audit_log::insert` helper does the `::inet` cast.

use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "admin_audit_log")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub actor_user_id: Uuid,
    pub target_user_id: Option<Uuid>,
    pub action: String,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub before_value: Option<Json>,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub after_value: Option<Json>,
    pub reason: String,
    pub impersonating_user_id: Option<Uuid>,
    #[sea_orm(column_type = "Text", nullable)]
    pub request_ip: Option<String>,
    pub user_agent: Option<String>,
    pub created_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
