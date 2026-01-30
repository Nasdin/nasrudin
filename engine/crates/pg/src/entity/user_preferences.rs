use sea_orm::entity::prelude::*;

/// User preferences stored as JSONB.
///
/// This uses the user's UUID as both the primary key and the foreign key
/// to the users table (1:1 relationship).
#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "user_preferences")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub user_id: Uuid,
    pub preferences: serde_json::Value,
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
