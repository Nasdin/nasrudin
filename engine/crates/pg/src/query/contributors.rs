//! User leaderboard queries — aggregate worker stats by user.
//!
//! Groups workers by their owner (via api_keys) and computes per-user
//! totals: worker count, theorems contributed, active workers.

use anyhow::Result;
use sea_orm::{ConnectionTrait, FromQueryResult, Statement, DatabaseBackend, ColumnTrait, EntityTrait, QueryFilter, QueryOrder, Order};
use uuid::Uuid;

use crate::entity::{api_keys, users, workers};

/// User with aggregated worker statistics for the leaderboard.
#[derive(Debug, Clone, serde::Serialize, FromQueryResult)]
pub struct ContributorStats {
    pub user_id: Uuid,
    pub display_name: Option<String>,
    pub handle: String,
    pub worker_count: i64,
    pub theorems_contributed: i64,
    pub active_worker_count: i64,
}

/// List all users who own workers, ordered by total theorems contributed DESC.
///
/// Joins users → api_keys (kind='worker', not revoked) → workers,
/// then aggregates by user_id. Users with no workers are excluded.
pub async fn list_contributors(db: &impl ConnectionTrait) -> Result<Vec<ContributorStats>> {
    use sea_orm::FromQueryResult;
    
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        SELECT 
            u.id as user_id,
            u.display_name,
            SPLIT_PART(u.email, '@', 1) as handle,
            COUNT(DISTINCT w.id)::BIGINT as worker_count,
            COALESCE(SUM(w.theorems_contributed), 0)::BIGINT as theorems_contributed,
            COUNT(DISTINCT CASE WHEN w.status = 'active' THEN w.id END)::BIGINT as active_worker_count
        FROM users u
        INNER JOIN api_keys ak ON ak.user_id = u.id AND ak.kind = 'worker' AND ak.revoked_at IS NULL
        INNER JOIN workers w ON w.id = ak.name
        GROUP BY u.id, u.display_name, u.email
        ORDER BY theorems_contributed DESC
        "#,
        [],
    );
    
    let rows = ContributorStats::find_by_statement(stmt).all(db).await?;
    Ok(rows)
}

/// Get a specific user's workers with full details.
///
/// Returns all workers owned by the user, ordered by theorems_contributed DESC.
pub async fn get_user_workers(
    db: &impl ConnectionTrait,
    user_id: Uuid,
) -> Result<Vec<workers::Model>> {
    let keys = api_keys::Entity::find()
        .filter(api_keys::Column::UserId.eq(user_id))
        .filter(api_keys::Column::Kind.eq("worker"))
        .filter(api_keys::Column::RevokedAt.is_null())
        .all(db)
        .await?;
    
    let worker_names: Vec<String> = keys.into_iter().map(|k| k.name).collect();
    if worker_names.is_empty() {
        return Ok(vec![]);
    }
    
    workers::Entity::find()
        .filter(workers::Column::Id.is_in(worker_names))
        .order_by(workers::Column::TheoremsContributed, Order::Desc)
        .all(db)
        .await
        .map_err(|e| e.into())
}

/// Get user by email (for droplet worker attribution).
pub async fn get_user_by_email(
    db: &impl ConnectionTrait,
    email: &str,
) -> Result<Option<users::Model>> {
    users::Entity::find()
        .filter(users::Column::Email.eq(email))
        .one(db)
        .await
        .map_err(|e| e.into())
}
