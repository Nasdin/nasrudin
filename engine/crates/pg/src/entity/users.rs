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
    pub plan_tier: String,
    pub stripe_customer_id: Option<String>,
    pub stripe_subscription_id: Option<String>,
    pub current_period_end: Option<DateTimeWithTimeZone>,
    pub plan_cycle_start: Option<DateTimeWithTimeZone>,
    /// $19/mo Researcher tier credit ledger. One credit is debited
    /// when a paid `conjecture_jobs` row is created and refunded on
    /// cancel-before-progress or zero-result `budget_exhausted`.
    pub research_credits: i32,
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
