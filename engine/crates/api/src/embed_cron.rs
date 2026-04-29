//! Background rebuild scheduler for the embedding index.
//!
//! Two trigger conditions:
//! - Wall-clock cron: rebuild every 24h.
//! - Theorem-count threshold: rebuild after every 1000 newly-verified
//!   theorems since the last build.
//!
//! Implementation: spawn a tokio task that polls every 60 seconds. On
//! either trigger, fork to `embed_build` (subprocess) so a long
//! build doesn't block other server work.

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use chrono::Utc;
use nasrudin_rocks::TheoremDb;
use tokio::process::Command;

const POLL_INTERVAL: Duration = Duration::from_secs(60);
const REBUILD_AFTER: Duration = Duration::from_secs(24 * 3600);
const COUNT_DELTA_TRIGGER: u64 = 1000;

pub struct EmbedCron {
    pub db: Arc<TheoremDb>,
    pub out_path: PathBuf,
    last_rebuild_ms: AtomicU64,
    last_seen_count: AtomicU64,
}

impl EmbedCron {
    pub fn new(db: Arc<TheoremDb>, out_path: PathBuf) -> Self {
        Self {
            db,
            out_path,
            last_rebuild_ms: AtomicU64::new(0),
            last_seen_count: AtomicU64::new(0),
        }
    }

    /// Drive loop. Runs until the process exits.
    pub async fn run(self: Arc<Self>) {
        // Seed the count baseline once at startup so we don't trigger
        // a rebuild just because `last_seen_count` started at 0.
        if let Ok(stats) = self.db.get_stats() {
            self.last_seen_count
                .store(stats.total_verified, Ordering::Relaxed);
        }

        loop {
            tokio::time::sleep(POLL_INTERVAL).await;
            if let Err(e) = self.tick().await {
                tracing::warn!("embed_cron tick failed: {e}");
            }
        }
    }

    async fn tick(&self) -> anyhow::Result<()> {
        let now_ms = u64::try_from(Utc::now().timestamp_millis()).unwrap_or(0);
        let last = self.last_rebuild_ms.load(Ordering::Relaxed);
        let stats = self.db.get_stats()?;
        let prev_count = self.last_seen_count.load(Ordering::Relaxed);
        let delta = stats.total_verified.saturating_sub(prev_count);

        let time_trigger = now_ms.saturating_sub(last) >= REBUILD_AFTER.as_millis() as u64;
        let count_trigger = delta >= COUNT_DELTA_TRIGGER;

        if !time_trigger && !count_trigger {
            return Ok(());
        }

        tracing::info!(
            "embed_cron rebuilding (time_trigger={time_trigger}, count_trigger={count_trigger}, delta={delta})"
        );
        self.rebuild_subprocess().await?;
        self.last_rebuild_ms.store(now_ms, Ordering::Relaxed);
        self.last_seen_count
            .store(stats.total_verified, Ordering::Relaxed);
        Ok(())
    }

    async fn rebuild_subprocess(&self) -> anyhow::Result<()> {
        let exe = std::env::current_exe()?;
        let dir = exe
            .parent()
            .ok_or_else(|| anyhow::anyhow!("no parent dir"))?;
        let bin = dir.join("embed_build");
        if !bin.exists() {
            anyhow::bail!("embed_build binary not found next to current_exe at {bin:?}");
        }
        let status = Command::new(&bin)
            .env("NASRUDIN_EMBED_OUT", &self.out_path)
            .env(
                "ROCKS_DB_PATH",
                std::env::var("ROCKS_DB_PATH").unwrap_or_else(|_| "./data/theorems.db".into()),
            )
            .status()
            .await?;
        if !status.success() {
            anyhow::bail!("embed_build exited {:?}", status.code());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rebuild_after_one_day() {
        assert_eq!(REBUILD_AFTER.as_secs(), 24 * 3600);
    }

    #[test]
    fn count_threshold_is_1000() {
        assert_eq!(COUNT_DELTA_TRIGGER, 1000);
    }
}
