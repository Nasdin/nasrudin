use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    #[sea_orm(unique)]
    pub email: String,
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
    /// Firebase UID — the source-of-truth identity link. Stable across
    /// provider linking (e.g. user adds Google to an email/password
    /// account → same UID).
    #[sea_orm(unique)]
    pub firebase_uid: String,
    /// Admin panel access. Gates `/api/admin/*` (alongside `ADMIN_TOKEN`
    /// bearer for system-actor calls). Demotion of the only admin row
    /// is blocked by the `users_last_admin_guard` Postgres trigger.
    pub is_admin: bool,
    /// Trust-bypass flag. Trusted submissions skip the redundant
    /// server-side `lake build` confirmation, with sampled spot-check
    /// for safety (see `crates/api/src/trust.rs`).
    pub is_trusted: bool,
    /// 1-in-N sampling rate for spot-checking trusted submissions.
    /// NULL = use `TRUSTED_SPOT_CHECK_RATE` env default; 0 = never
    /// spot-check; 1 = always spot-check (effectively untrusted).
    pub spot_check_rate: Option<i32>,
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
