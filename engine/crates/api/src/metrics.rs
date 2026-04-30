//! Prometheus-format metrics exposition (P-Task 9).
//!
//! Exposed at `GET /metrics` for scraping by an external Prometheus
//! instance. The deploy stack runs Grafana alongside Caddy + Postgres
//! on the droplet (see `deploy/grafana/`); this is the data source.
//!
//! Metrics are computed on demand from RocksDB / Postgres / in-process
//! state, no separate metrics-collector layer. For a 64-core droplet
//! handling ~30k ingests/hour this is fine — `/metrics` is scraped
//! every 15s and the queries each take <5ms.

use std::sync::Arc;

use axum::{extract::State, http::StatusCode, response::IntoResponse};

use crate::state::AppState;

/// `GET /metrics` — Prometheus text exposition format.
///
/// Counters and gauges (no histograms; for those we'd want
/// `metrics-exporter-prometheus` runtime, deferred until we have a
/// real APM need).
pub async fn metrics(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let mut out = String::with_capacity(4096);

    // ── RocksDB queue depths ─────────────────────────────────────────
    let pg_queue = state.db.pg_insert_queue_depth().unwrap_or(0);
    let reverify_queue = state.db.reverify_queue_depth().unwrap_or(0);
    let lake_promo_queue = state.db.lake_promotion_queue_depth().unwrap_or(0);

    out.push_str(
        "# HELP nasrudin_pg_insert_queue_depth Theorems queued for asynchronous PG insertion (RocksDB-primary write-behind).\n",
    );
    out.push_str("# TYPE nasrudin_pg_insert_queue_depth gauge\n");
    out.push_str(&format!("nasrudin_pg_insert_queue_depth {pg_queue}\n"));

    out.push_str(
        "# HELP nasrudin_reverify_queue_depth Theorems awaiting chain-replay reverification.\n",
    );
    out.push_str("# TYPE nasrudin_reverify_queue_depth gauge\n");
    out.push_str(&format!("nasrudin_reverify_queue_depth {reverify_queue}\n"));

    out.push_str(
        "# HELP nasrudin_lake_promotion_queue_depth ChainVerified theorems awaiting lake-build promotion (P-Task 2).\n",
    );
    out.push_str("# TYPE nasrudin_lake_promotion_queue_depth gauge\n");
    out.push_str(&format!(
        "nasrudin_lake_promotion_queue_depth {lake_promo_queue}\n"
    ));

    // ── Theorem counts by domain ─────────────────────────────────────
    if let Ok(by_domain) = state.db.count_by_domain() {
        out.push_str(
            "# HELP nasrudin_theorems_by_domain Theorems in RocksDB grouped by physics domain.\n",
        );
        out.push_str("# TYPE nasrudin_theorems_by_domain gauge\n");
        for (dom, count) in &by_domain {
            out.push_str(&format!(
                "nasrudin_theorems_by_domain{{domain=\"{dom}\"}} {count}\n"
            ));
        }
    }

    // ── Aggregate stats ──────────────────────────────────────────────
    if let Ok(stats) = state.db.get_stats() {
        out.push_str("# HELP nasrudin_theorems_total Total theorem rows in RocksDB.\n");
        out.push_str("# TYPE nasrudin_theorems_total counter\n");
        out.push_str(&format!("nasrudin_theorems_total {}\n", stats.total_theorems));

        out.push_str(
            "# HELP nasrudin_theorems_verified Total theorems with status=Verified (any tactic).\n",
        );
        out.push_str("# TYPE nasrudin_theorems_verified counter\n");
        out.push_str(&format!(
            "nasrudin_theorems_verified {}\n",
            stats.total_verified
        ));

        out.push_str(
            "# HELP nasrudin_theorems_rejected Total theorems with status=Rejected (incl. cascade victims).\n",
        );
        out.push_str("# TYPE nasrudin_theorems_rejected counter\n");
        out.push_str(&format!(
            "nasrudin_theorems_rejected {}\n",
            stats.total_rejected
        ));

        out.push_str("# HELP nasrudin_theorems_pending Theorems with status=Pending (haven't replayed).\n");
        out.push_str("# TYPE nasrudin_theorems_pending gauge\n");
        out.push_str(&format!(
            "nasrudin_theorems_pending {}\n",
            stats.total_pending
        ));

        out.push_str("# HELP nasrudin_max_depth Highest derivation depth seen.\n");
        out.push_str("# TYPE nasrudin_max_depth gauge\n");
        out.push_str(&format!("nasrudin_max_depth {}\n", stats.max_depth));

        out.push_str("# HELP nasrudin_max_generation Highest GA generation seen.\n");
        out.push_str("# TYPE nasrudin_max_generation gauge\n");
        out.push_str(&format!("nasrudin_max_generation {}\n", stats.max_generation));
    }

    // ── 3-state verification split (P-Task 1 + P-Task 12) ──────────
    // Walk a bounded sample and count by tactic_used. With 100k+
    // theorems we don't want to scan all of them every 15s; cap at 10k.
    let mut chain_verified = 0u64;
    let mut worker_claim = 0u64;
    let mut lake_verified = 0u64;
    if let Ok(theorems) = state.db.list_theorems() {
        for t in theorems.into_iter().take(10_000) {
            if let nasrudin_core::VerificationStatus::Verified { tactic_used, .. } = &t.verified {
                if tactic_used == "chain_replay" {
                    chain_verified += 1;
                } else if tactic_used == "worker_claim" {
                    worker_claim += 1;
                } else if tactic_used == "lake_build" {
                    lake_verified += 1;
                }
            }
        }
    }
    out.push_str(
        "# HELP nasrudin_theorems_chain_verified Theorems with status=Verified{tactic=chain_replay} (provisional, server-only).\n",
    );
    out.push_str("# TYPE nasrudin_theorems_chain_verified gauge\n");
    out.push_str(&format!(
        "nasrudin_theorems_chain_verified {chain_verified}\n"
    ));

    out.push_str(
        "# HELP nasrudin_theorems_worker_claim Theorems with status=Verified{tactic=worker_claim} (worker locally lake-built; server lake pending).\n",
    );
    out.push_str("# TYPE nasrudin_theorems_worker_claim gauge\n");
    out.push_str(&format!(
        "nasrudin_theorems_worker_claim {worker_claim}\n"
    ));

    out.push_str(
        "# HELP nasrudin_theorems_lake_verified Theorems with status=Verified{tactic=lake_build} (kernel-confirmed by server).\n",
    );
    out.push_str("# TYPE nasrudin_theorems_lake_verified gauge\n");
    out.push_str(&format!(
        "nasrudin_theorems_lake_verified {lake_verified}\n"
    ));

    // ── Liveness ─────────────────────────────────────────────────────
    out.push_str("# HELP nasrudin_up 1 if the API is live (always 1 by definition).\n");
    out.push_str("# TYPE nasrudin_up gauge\n");
    out.push_str("nasrudin_up 1\n");

    (
        StatusCode::OK,
        [(
            axum::http::header::CONTENT_TYPE,
            "text/plain; version=0.0.4",
        )],
        out,
    )
        .into_response()
}
