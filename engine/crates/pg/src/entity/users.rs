use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    #[sea_orm(unique)]
    pub email: String,
    #[sea_orm(column_type = "Text")]
    pub password_hash: String,
    pub display_name: Option<String>,
    pub created_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(has_many = "super::sessions::Entity")]
    Sessions,
    #[sea_orm(has_many = "super::saved_searches::Entity")]
    SavedSearches,
    #[sea_orm(has_one = "super::user_preferences::Entity")]
    Preferences,
}

impl Related<super::sessions::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::Sessions.def()
    }
}

impl Related<super::saved_searches::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::SavedSearches.def()
    }
}

impl Related<super::user_preferences::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::Preferences.def()
    }
}

impl ActiveModelBehavior for ActiveModel {}
