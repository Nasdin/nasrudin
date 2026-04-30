use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "conjecture_jobs")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub owner_id: Uuid,
    pub state: String,
    pub outcome: Option<String>,
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub provider: String,
    pub model: String,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub suggestions: Option<Json>,
    pub chosen_index: Option<i32>,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub seed: Option<Json>,
    #[sea_orm(column_type = "JsonBinary")]
    pub budget: Json,
    pub claimed_by: Option<String>,
    pub claimed_at: Option<DateTimeWithTimeZone>,
    pub lease_expires_at: Option<DateTimeWithTimeZone>,
    pub last_heartbeat_at: Option<DateTimeWithTimeZone>,
    pub candidates_attempted: i32,
    pub candidates_verified: i32,
    #[sea_orm(column_type = r#"custom("bytea[]")"#, nullable)]
    pub verified_theorem_ids: Option<Vec<Vec<u8>>>,
    pub created_at: DateTimeWithTimeZone,
    pub completed_at: Option<DateTimeWithTimeZone>,
    /// Phase F: streamed Markdown paper draft. NULL until the user
    /// requests one; populated incrementally as the LLM streams.
    #[sea_orm(column_type = "Text", nullable)]
    pub paper_draft: Option<String>,
    /// Hard ceiling on lake-build slot-hours the cluster will spend
    /// on this conjecture (default 96 = 4 slots × 24h).
    pub lake_slot_hours_quota: i32,
    /// Slot-hours debited via heartbeats. Server caps the per-tick
    /// delta at `2 × wallclock_h × slots_held` to defeat lying workers.
    pub lake_slot_hours_consumed: f32,
    /// Queue ordering: highest first. Free baseline is 5.
    pub slice_priority: i32,
    /// Plan ownership ("researcher" today; future tiers extend).
    pub tier: String,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(
        belongs_to = "super::users::Entity",
        from = "Column::OwnerId",
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
