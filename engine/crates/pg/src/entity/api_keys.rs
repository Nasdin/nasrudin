use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "api_keys")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    /// Owning user. NULL for worker-issued keys.
    pub user_id: Option<Uuid>,
    /// "live" (user-issued) or "worker" (machine-issued).
    pub kind: String,
    pub name: String,
    /// First 12 chars of the full key, used for lookup before Argon2 verify.
    #[sea_orm(unique)]
    pub prefix: String,
    /// Argon2 hash of the full secret.
    #[sea_orm(column_type = "Text")]
    pub key_hash: String,
    pub last_used_at: Option<DateTimeWithTimeZone>,
    pub expires_at: Option<DateTimeWithTimeZone>,
    pub created_at: DateTimeWithTimeZone,
    pub revoked_at: Option<DateTimeWithTimeZone>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(
        belongs_to = "super::users::Entity",
        from = "Column::UserId",
        to = "super::users::Column::Id",
        on_delete = "Cascade"
    )]
    User,
}

impl Related<super::users::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::User.def()
    }
}

impl ActiveModelBehavior for ActiveModel {}
