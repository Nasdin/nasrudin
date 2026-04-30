//! `POST /api/cluster-report`
//!
//! Workers POST per-chunk per-cluster `ClusterSummary` rows here. The
//! steerer reads from `cluster_reports` to compute UCB1 reward and to
//! populate the LLM prompt. Authentication reuses the worker bearer
//! token middleware (same as `/api/ingest`).

use axum::{extract::State, http::StatusCode, Json};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::sync::Arc;
use uuid::Uuid;

use crate::state::AppState;

#[derive(Debug, Deserialize)]
pub struct ClusterReportBody {
    pub worker_id: Uuid,
    pub chunk_index: i64,
    pub k_used: i16,
    pub island_reports: Vec<IslandReport>,
}

#[derive(Debug, Deserialize)]
pub struct IslandReport {
    pub island_domain: String,
    /// `ClusterSummary` JSON — kept opaque on this side so the schema
    /// can evolve in the GA crate without churning this handler.
    pub summaries: Vec<Value>,
}

#[derive(Debug, Serialize)]
pub struct Resp {
    pub received: bool,
    pub stored: u32,
}

pub async fn handler(
    State(state): State<Arc<AppState>>,
    Json(body): Json<ClusterReportBody>,
) -> (StatusCode, Json<Resp>) {
    let Some(pg) = state.pg.as_ref() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(Resp {
                received: false,
                stored: 0,
            }),
        );
    };
    let mut stored = 0u32;
    for island in body.island_reports {
        for s in island.summaries {
            let cluster_id = s
                .get("cluster_id")
                .and_then(|v| v.as_u64())
                .unwrap_or(0) as i16;
            match nasrudin_pg::query::cluster_reports::insert_summary(
                pg,
                body.worker_id,
                body.chunk_index,
                body.k_used,
                &island.island_domain,
                cluster_id,
                s,
            )
            .await
            {
                Ok(_) => stored += 1,
                Err(e) => tracing::warn!(error=%e, "cluster_report insert failed"),
            }
        }
    }
    (
        StatusCode::OK,
        Json(Resp {
            received: true,
            stored,
        }),
    )
}
