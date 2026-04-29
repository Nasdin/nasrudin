//! `cache-stats` — read RocksDB and report Phase-A cache hit / size metrics.
//!
//! Opens a read-only handle to the engine's RocksDB instance, iterates the
//! `attempts` and `tactic_priors` column families, and emits a JSON
//! summary on stdout. Useful for measuring cache hit rate over a workload.
//!
//! Usage:
//!   cache-stats --rocks-path ~/.nasrudin/db
//!
//! Output (JSON):
//!   {
//!     "attempts": { "rows": N, "verified": A, "rejected_type_error": B, ... },
//!     "tactic_priors": { "rows": M, "total_recorded_successes": S }
//!   }

use anyhow::Result;
use clap::Parser;
use rocksdb::{DB, IteratorMode, Options};
use serde::Serialize;

#[derive(Parser, Debug)]
#[command(name = "cache-stats")]
#[command(about = "Report Phase-A cache row counts and outcome breakdowns")]
struct Args {
    /// Path to the RocksDB instance (the same one workers/server use).
    #[arg(long, default_value = "./data/rocks")]
    rocks_path: String,
}

#[derive(Serialize, Default)]
struct Report {
    attempts: AttemptsStats,
    tactic_priors: PriorsStats,
}

#[derive(Serialize, Default)]
struct AttemptsStats {
    rows: u64,
    verified: u64,
    rejected_type_error: u64,
    rejected_timeout: u64,
    rejected_trivial: u64,
    pending: u64,
}

#[derive(Serialize, Default)]
struct PriorsStats {
    rows: u64,
    total_recorded_successes: u64,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let opts = Options::default();
    let cfs = DB::list_cf(&opts, &args.rocks_path).unwrap_or_default();
    let db = DB::open_cf_for_read_only(&opts, &args.rocks_path, cfs.clone(), false)?;

    let mut report = Report::default();

    if cfs.iter().any(|c| c == "attempts") {
        if let Some(cf) = db.cf_handle("attempts") {
            for item in db.iterator_cf(&cf, IteratorMode::Start) {
                let (_, v) = item?;
                report.attempts.rows += 1;
                if let Ok(rec) = serde_json::from_slice::<serde_json::Value>(&v) {
                    let kind = rec
                        .get("outcome")
                        .and_then(|o| o.get("kind"))
                        .and_then(|k| k.as_str())
                        .unwrap_or("");
                    match kind {
                        "verified" => report.attempts.verified += 1,
                        "rejected_type_error" => report.attempts.rejected_type_error += 1,
                        "rejected_timeout" => report.attempts.rejected_timeout += 1,
                        "rejected_trivial" => report.attempts.rejected_trivial += 1,
                        "pending" => report.attempts.pending += 1,
                        _ => {}
                    }
                }
            }
        }
    }

    if cfs.iter().any(|c| c == "tactic_priors") {
        if let Some(cf) = db.cf_handle("tactic_priors") {
            for item in db.iterator_cf(&cf, IteratorMode::Start) {
                let (_, v) = item?;
                report.tactic_priors.rows += 1;
                if let Ok(rec) = serde_json::from_slice::<serde_json::Value>(&v) {
                    if let Some(succs) = rec.get("successes").and_then(|s| s.as_array()) {
                        for s in succs {
                            if let Some(hits) = s.get("hits").and_then(|h| h.as_u64()) {
                                report.tactic_priors.total_recorded_successes += hits;
                            }
                        }
                    }
                }
            }
        }
    }

    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}
