//! Bulk admin operations runner.
//!
//! `POST /api/admin/users/bulk` returns a `run_id` immediately and
//! spawns a tokio task. The task iterates the supplied user_ids
//! serially, calling the same per-user mutation as the singleton
//! handlers — every step writes its own audit row via
//! `perform_audited`. Progress is broadcast on
//! `state.bulk_run_progress_tx` for the SSE handler to forward.
//!
//! Failures don't abort. The `bulk_runs.failures` JSONB array
//! accumulates `{user_id, error}` records the UI can surface for
//! re-targeting.

use std::sync::Arc;

use serde::{Deserialize, Serialize};
use serde_json::json;
use uuid::Uuid;

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::auth::AuthUser;
use crate::state::AppState;

/// Per-user action variants supported by the bulk runner.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "action", content = "params")]
pub enum BulkAction {
    #[serde(rename = "set_trust")]
    SetTrust { is_trusted: bool },
    #[serde(rename = "set_plan")]
    SetPlan { plan_tier: String },
    #[serde(rename = "adjust_credits")]
    AdjustCredits { delta: i32 },
    #[serde(rename = "set_spot_check_rate")]
    SetSpotCheckRate { rate: Option<i32> },
}

#[derive(Clone, Debug, Serialize)]
pub struct BulkProgress {
    pub completed: u32,
    pub failed: u32,
    pub last_user_id: Option<Uuid>,
    pub status: String,
}

pub fn spawn_run(
    state: Arc<AppState>,
    run_id: Uuid,
    actor: AuthUser,
    action: BulkAction,
    user_ids: Vec<Uuid>,
    reason: String,
) {
    tokio::spawn(async move {
        let pg = match &state.pg {
            Some(p) => p.clone(),
            None => return,
        };
        let mut completed = 0u32;
        let mut failed = 0u32;
        for uid in user_ids {
            match run_one(&pg, &actor, &action, uid, &reason).await {
                Ok(()) => {
                    completed += 1;
                    let _ =
                        nasrudin_pg::query::bulk_runs::increment_completed(&pg, run_id).await;
                }
                Err(e) => {
                    failed += 1;
                    let _ = nasrudin_pg::query::bulk_runs::increment_failed(
                        &pg,
                        run_id,
                        json!([{"user_id": uid, "error": e.to_string()}]),
                    )
                    .await;
                }
            }
            let _ = state.bulk_run_progress_tx.send((
                run_id,
                BulkProgress {
                    completed,
                    failed,
                    last_user_id: Some(uid),
                    status: "running".into(),
                },
            ));
        }
        let final_status = if failed == 0 {
            "completed"
        } else {
            "completed_with_failures"
        };
        let _ = nasrudin_pg::query::bulk_runs::complete(&pg, run_id, final_status).await;
        let _ = nasrudin_pg::query::admin_audit_log::insert(
            &pg,
            actor.id,
            None,
            None,
            actions::BULK_RUN_COMPLETE,
            None,
            Some(json!({
                "run_id": run_id,
                "completed": completed,
                "failed": failed,
            })),
            "bulk run completed".into(),
            None,
            None,
        )
        .await;
        let _ = state.bulk_run_progress_tx.send((
            run_id,
            BulkProgress {
                completed,
                failed,
                last_user_id: None,
                status: final_status.into(),
            },
        ));
    });
}

async fn run_one(
    pg: &nasrudin_pg::sea_orm::DatabaseConnection,
    actor: &AuthUser,
    action: &BulkAction,
    target: Uuid,
    reason: &str,
) -> Result<(), anyhow::Error> {
    let action_clone = action.clone();
    let action_label: &'static str = match action {
        BulkAction::SetTrust { .. } => actions::SET_IS_TRUSTED,
        BulkAction::SetPlan { .. } => actions::SET_PLAN_TIER,
        BulkAction::AdjustCredits { .. } => actions::ADJUST_CREDITS,
        BulkAction::SetSpotCheckRate { .. } => actions::SET_SPOT_CHECK_RATE,
    };
    let res = perform_audited(
        pg,
        actor,
        None,
        RequestMeta::default(),
        Some(target),
        action_label,
        reason.to_string(),
        json!({}),
        move |txn| {
            Box::pin(async move {
                match action_clone {
                    BulkAction::SetTrust { is_trusted } => {
                        nasrudin_pg::query::admin_users::set_is_trusted(txn, target, is_trusted)
                            .await?;
                        Ok::<_, sea_orm::DbErr>(((), json!({"is_trusted": is_trusted})))
                    }
                    BulkAction::SetPlan { plan_tier } => {
                        nasrudin_pg::query::admin_users::set_plan_tier(txn, target, &plan_tier)
                            .await?;
                        Ok::<_, sea_orm::DbErr>(((), json!({"plan_tier": plan_tier})))
                    }
                    BulkAction::AdjustCredits { delta } => {
                        let new = nasrudin_pg::query::admin_users::adjust_credits(
                            txn, target, delta,
                        )
                        .await?;
                        Ok::<_, sea_orm::DbErr>(((), json!({"research_credits": new})))
                    }
                    BulkAction::SetSpotCheckRate { rate } => {
                        nasrudin_pg::query::admin_users::set_spot_check_rate(txn, target, rate)
                            .await?;
                        Ok::<_, sea_orm::DbErr>(((), json!({"spot_check_rate": rate})))
                    }
                }
            })
        },
    )
    .await;
    res.map(|_| ()).map_err(|e| anyhow::anyhow!(e.to_string()))
}
