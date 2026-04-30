//! `POST /api/admin/reload_corpus` — hot-swap the AxiomStore from disk.
//!
//! Migrated to RequireAdmin + audit log. Heavy I/O (rebuilding the
//! AxiomStore) runs on a blocking thread. The audit row records the
//! before/after axiom totals.

use std::sync::Arc;

use axum::{
    Json,
    extract::{ConnectInfo, State},
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
};
use serde::Deserialize;
use serde_json::json;
use std::net::SocketAddr;

use nasrudin_derive::AxiomStore;

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize, Default)]
pub struct ReloadInput {
    #[serde(default)]
    pub reason: Option<String>,
}

pub async fn reload_corpus(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    body: Option<Json<ReloadInput>>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(json!({"error": "pg_unavailable"})),
            )
                .into_response();
        }
    };
    let reason = body
        .and_then(|b| b.0.reason)
        .unwrap_or_else(|| "operator-initiated corpus reload".into());
    let ua = headers
        .get(axum::http::header::USER_AGENT)
        .and_then(|v| v.to_str().ok())
        .map(str::to_string);

    // Heavy I/O off the runtime.
    let prover_root = std::env::var("PROVER_ROOT").unwrap_or_else(|_| "../prover".into());
    let rebuild = tokio::task::spawn_blocking(move || -> anyhow::Result<(AxiomStore, usize, usize)> {
        let mut store = AxiomStore::new();
        let catalog =
            std::path::Path::new(&prover_root).join("../physlean-extract/output/catalog.json");
        if catalog.exists() {
            store.load_from_catalog(&catalog)?;
        }
        store.load_special_relativity_upstream();
        store.load_electromagnetism_upstream();
        store.load_classical_mechanics_postulates();
        let math_corpus = std::path::Path::new(&prover_root)
            .join("../physlean-extract/output/math_corpus.json");
        let math_count = store.load_math_corpus(&math_corpus).unwrap_or(0);
        nasrudin_derive::no_cheat_audit::audit_or_panic(&store, "reload_corpus");
        let total = store.len();
        Ok((store, total, math_count))
    })
    .await;

    let (store, total, math_count) = match rebuild {
        Ok(Ok(t)) => t,
        Ok(Err(e)) => {
            tracing::error!("reload_corpus rebuild failed: {e}");
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({"error": format!("rebuild_failed: {e}")})),
            )
                .into_response();
        }
        Err(e) => {
            tracing::error!("reload_corpus join failed: {e}");
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({"error": format!("join_failed: {e}")})),
            )
                .into_response();
        }
    };

    let prev_total = state.axiom_store.load().len();
    let result = perform_audited(
        pg,
        &admin.0.user,
        None,
        RequestMeta {
            ip: Some(addr.ip()),
            user_agent: ua,
        },
        None,
        actions::RELOAD_CORPUS,
        reason,
        json!({"prev_total": prev_total}),
        move |_txn| {
            Box::pin(async move {
                Ok::<_, sea_orm::DbErr>((
                    (),
                    json!({"new_total": total, "math_count": math_count}),
                ))
            })
        },
    )
    .await;

    if let Err(e) = result {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": e.to_string()})),
        )
            .into_response();
    }

    state.axiom_store.replace(store);
    state.invalidate_seed_cache();
    tracing::info!("Hot-reloaded AxiomStore: {total} axioms ({math_count} math-corpus)");

    (
        StatusCode::OK,
        Json(json!({
            "count": total,
            "math_count": math_count,
            "hot_swapped": true,
        })),
    )
        .into_response()
}
