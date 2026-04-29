//! Background drain task that flushes the RocksDB pg_insert_queue
//! into PostgreSQL.
//!
//! The hot ingest path (handlers/ingest.rs) persists every accepted
//! theorem to RocksDB synchronously, then enqueues a serialised
//! `nasrudin_pg::query::theorems::NewTheorem` payload in the
//! `pg_insert_queue` column family. This task wakes every
//! `DRAIN_INTERVAL`, drains up to `BATCH_SIZE` queued payloads, runs
//! them through `theorems::insert_pending` in a single transaction,
//! then `ack_pg_insert`s the successful ids.
//!
//! On API restart, the queue persists in RocksDB — so anything that
//! was enqueued but never reached PG before the previous shutdown
//! gets re-attempted on next boot. No verified theorem is ever lost
//! due to PG unavailability or API crash.

use std::sync::Arc;
use std::time::Duration;

use anyhow::Result;
use sea_orm::{DatabaseConnection, TransactionTrait};

use nasrudin_pg::query::theorems::{self, NewTheorem};
use nasrudin_rocks::TheoremDb;

const DRAIN_INTERVAL: Duration = Duration::from_millis(500);
const BATCH_SIZE: usize = 100;

/// Spawn the drain loop. Runs forever; cancel by dropping the API.
pub async fn drain_loop(rocks: Arc<TheoremDb>, pg: DatabaseConnection) {
    // Boot recovery: log queue depth so the operator can see how much
    // was carried over from a previous shutdown.
    if let Ok(depth) = rocks.pg_insert_queue_depth() {
        if depth > 0 {
            tracing::info!(
                "pg_drain: recovered {depth} queued theorems from previous shutdown"
            );
        }
    }

    loop {
        tokio::time::sleep(DRAIN_INTERVAL).await;
        if let Err(e) = drain_once(&rocks, &pg).await {
            tracing::warn!("pg_drain tick failed: {e}");
        }
    }
}

async fn drain_once(rocks: &Arc<TheoremDb>, pg: &DatabaseConnection) -> Result<()> {
    let batch = rocks.drain_pg_insert_queue(BATCH_SIZE)?;
    if batch.is_empty() {
        return Ok(());
    }

    // Decode payloads; skip malformed entries so a single bad row can't
    // wedge the drain forever. Bad entries get acked + logged.
    let mut decoded: Vec<(nasrudin_core::TheoremId, NewTheorem)> = Vec::with_capacity(batch.len());
    for (id, payload) in batch {
        match serde_json::from_slice::<NewTheorem>(&payload) {
            Ok(nt) => decoded.push((id, nt)),
            Err(e) => {
                tracing::warn!(
                    theorem_id = %hex::encode(id),
                    "pg_drain: dropping malformed queue entry: {e}"
                );
                rocks.ack_pg_insert(&id).ok();
            }
        }
    }
    if decoded.is_empty() {
        return Ok(());
    }

    // Insert all rows in a single transaction. If any one row fails on
    // a unique-constraint violation (duplicate canonical_hash from a
    // re-enqueue after a prior partial-flush crash), we ack it anyway
    // since the row is already in PG. Other failures retry next tick.
    let txn = pg.begin().await?;
    let mut acked = Vec::new();
    let mut requeue = Vec::new();
    for (id, nt) in decoded {
        match theorems::insert_pending(&txn, nt).await {
            Ok(_) => acked.push(id),
            Err(e) => {
                let msg = format!("{e}");
                // Duplicate key = already in PG, ack it.
                if msg.contains("duplicate key") || msg.contains("unique constraint") {
                    acked.push(id);
                } else {
                    tracing::warn!(
                        theorem_id = %hex::encode(id),
                        "pg_drain: insert_pending failed, will retry: {msg}"
                    );
                    requeue.push(id);
                }
            }
        }
    }
    txn.commit().await?;

    for id in &acked {
        rocks.ack_pg_insert(id).ok();
    }
    if !acked.is_empty() {
        tracing::debug!(
            "pg_drain: flushed {} theorems to PG ({} requeued)",
            acked.len(),
            requeue.len()
        );
    }
    Ok(())
}
