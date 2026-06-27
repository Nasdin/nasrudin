//! 30-second tick. Requeues `state='Running' AND lease_expires_at < NOW()`
//! conjecture rows; emits one `progress {worker_lost: true}` event per row
//! so SSE subscribers see the requeue.

use std::sync::Arc;
use std::time::Duration;

use crate::conjecture::ConjectureEvent;
use crate::state::AppState;

pub struct ConjectureLeaseReaper {
    pub state: Arc<AppState>,
}

impl ConjectureLeaseReaper {
    pub fn new(state: Arc<AppState>) -> Self {
        Self { state }
    }

    pub async fn run(self: Arc<Self>) {
        let mut interval = tokio::time::interval(Duration::from_secs(30));
        interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            interval.tick().await;
            if let Err(e) = self.reap_once().await {
                tracing::warn!("conjecture lease reaper tick failed: {e}");
            }
        }
    }

    async fn reap_once(&self) -> Result<(), sea_orm::DbErr> {
        let Some(pg) = self.state.pg.as_ref() else {
            return Ok(());
        };
        let requeued = nasrudin_pg::query::conjecture_jobs::requeue_expired_leases(pg).await?;
        if requeued.is_empty() {
            return Ok(());
        }
        tracing::info!("conjecture reaper requeued {} job(s)", requeued.len());
        for job_id in requeued {
            let payload = serde_json::json!({"worker_lost": true});
            if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
                pg,
                job_id,
                "progress",
                payload.clone(),
            )
            .await
            {
                let _ = self.state.conjecture_event_tx.send(ConjectureEvent {
                    id: event_id,
                    job_id,
                    kind: "progress".into(),
                    payload,
                    at: chrono::Utc::now(),
                });
            }
        }
        Ok(())
    }
}
