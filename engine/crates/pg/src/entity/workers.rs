use sea_orm::entity::prelude::*;
use serde::Serialize;

/// Worker status stored as TEXT in PostgreSQL.
#[derive(Debug, Clone, PartialEq, Eq, EnumIter, DeriveActiveEnum, Serialize)]
#[sea_orm(rs_type = "String", db_type = "Text")]
pub enum WorkerStatus {
    #[sea_orm(string_value = "active")]
    Active,
    #[sea_orm(string_value = "inactive")]
    Inactive,
    #[sea_orm(string_value = "disconnected")]
    Disconnected,
}

/// Distributed worker registry.
///
/// Workers register via POST /api/workers/register and receive a text ID.
/// They heartbeat periodically to update `last_seen` and `theorems_contributed`.
// `Eq` is removed because the new `reputation_score: f32` field doesn't
// implement Eq. Equality on a worker row by Eq was never load-bearing
// (we always compare by `id`), so dropping it has no behavioural effect.
#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize)]
#[sea_orm(table_name = "workers")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false, column_type = "Text")]
    pub id: String,
    pub name: Option<String>,
    pub host: Option<String>,
    pub last_seen: DateTimeWithTimeZone,
    pub theorems_contributed: i64,
    pub status: WorkerStatus,
    pub last_heartbeat_at: Option<DateTimeWithTimeZone>,
    pub last_contribution_at: Option<DateTimeWithTimeZone>,
    pub current_generation: i64,
    pub theorems_produced_total: i64,
    pub uptime_seconds: i64,
    pub engine_git_sha: Option<String>,
    /// Reputation score in [0.0, 1.0]. EMA over recent lake-promotion
    /// outcomes for chains the worker submitted: 0.99 × prev + 0.01 ×
    /// (1 if pass else 0). Default 1.0 (presumption of innocence).
    /// Ingest gate (P-Task 5) tightens rate limits as score degrades:
    /// `< 0.5` → 1/min, `< 0.2` → 503 + auto_revoked.
    #[sea_orm(default_value = 1.0)]
    pub reputation_score: f32,
    /// Cumulative count of lake-promotions whose outcome was Verified
    /// for chains this worker submitted. Display-only metric.
    #[sea_orm(default_value = 0)]
    pub spot_check_pass_count: i32,
    /// Cumulative count of lake-promotions whose outcome was Rejected.
    /// Triggers auto-revoke when the consecutive-fail streak reaches 5.
    #[sea_orm(default_value = 0)]
    pub spot_check_fail_count: i32,
    /// Set when the platform auto-revokes the worker due to repeated
    /// lake-build failures. Manual recovery requires an admin to clear
    /// this field via SQL.
    pub auto_revoked_at: Option<DateTimeWithTimeZone>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
