//! 60-second tick that marks expired impersonation sessions ended.
//!
//! Sessions whose `expires_at` lies in the past but whose `ended_at`
//! is still NULL get `ended_at = now()`, `end_reason = 'expired'`, and
//! a system-actor audit row recording IMPERSONATE_END.

use std::time::Duration;

use nasrudin_pg::sea_orm::DatabaseConnection;

use crate::admin::audit::{actions, SYSTEM_ACTOR_ID};

pub fn spawn(pg: DatabaseConnection) {
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(60));
        interval.tick().await; // burn the immediate tick
        loop {
            interval.tick().await;
            tick_once(&pg).await;
        }
    });
}

pub async fn tick_once(pg: &DatabaseConnection) {
    let expired = match nasrudin_pg::query::impersonation::list_expired(pg).await {
        Ok(v) => v,
        Err(e) => {
            tracing::warn!(error = %e, "impersonation expiry: list_expired failed");
            return;
        }
    };
    for row in expired {
        if nasrudin_pg::query::impersonation::end(pg, row.id, "expired")
            .await
            .is_ok()
        {
            let _ = nasrudin_pg::query::admin_audit_log::insert(
                pg,
                SYSTEM_ACTOR_ID,
                Some(row.target_user_id),
                Some(row.admin_user_id),
                actions::IMPERSONATE_END,
                None,
                Some(serde_json::json!({"session_id": row.id, "end_reason": "expired"})),
                "system: session expired automatically".into(),
                None,
                Some("expiry-tick".into()),
            )
            .await;
        }
    }
}
