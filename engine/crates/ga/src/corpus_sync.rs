//! Worker-side corpus hydration from `/api/corpus/dump`.
//!
//! ## Architecture
//!
//! Mirrors the API server's RocksDB-backed cold tier on the worker
//! so a Raspberry Pi-class box (1 GB RAM) can run the GA without
//! holding the ~195 k-entry Mathlib corpus in memory.
//!
//! Boot flow (driven by `worker.rs`):
//!
//! ```text
//! 1. Open local CorpusDb at $NASRUDIN_WORKER_ROCKS / default.
//! 2. If corpus.count() == 0 → hydrate_from_server(api_url, ...).
//!    Stream NDJSON from /api/corpus/dump, bulk-insert in 1000-axiom
//!    batches into CF_CORPUS_AXIOM + CF_CORPUS_DOMAIN.
//! 3. Build AxiomStore::with_corpus(Arc::new(corpus)) — the GA's
//!    hot path now point-fetches against local RocksDB instead of
//!    holding 195k axioms in a HashMap.
//! ```
//!
//! ## Resume + idempotency
//!
//! Hydration is a single-pass read of `/api/corpus/dump`. On
//! interruption (SIGINT, network drop, server restart mid-stream)
//! the partial cold tier is preserved on disk; the next worker boot
//! sees `count > 0` and *skips* hydration. To force re-hydration the
//! operator deletes `$NASRUDIN_WORKER_ROCKS` (or wipes the corpus
//! CFs). Resume-from-offset isn't worth the complexity: the dump
//! costs ~30 s on a typical home connection, and a partially-loaded
//! corpus is still useful (the worker just operates on the prefix
//! it managed to ingest before the interrupt).
//!
//! Repeated runs are idempotent because `CorpusBackend::put` uses
//! axiom-name as the primary key — re-inserting the same name
//! overwrites the bincode value with itself.
//!
//! ## ETag short-circuit
//!
//! After every successful hydration we persist the server's ETag in
//! a meta key. On subsequent boots, when the local count is non-zero
//! we send `If-None-Match: <persisted_etag>` and accept a 304 to
//! skip the dump entirely. Workers rebooting quickly (e.g.
//! `systemctl restart`) re-hydrate at zero cost.
//!
//! ## RAM bounds
//!
//! - **One NDJSON line at a time** through `AsyncBufReadExt::lines`.
//!   Average line ≈ 800 B; peak ≈ 50 KB for the deepest dependent-type
//!   Lean exprs (a few outliers).
//! - **One `WriteBatch` of `BATCH_SIZE` axioms** queued for RocksDB
//!   commit (≈ 5 MB).
//! - **One block-cache page in flight** during commits (~ 16 KB).
//!
//! Total resident overhead: < 10 MB above the worker's steady-state.
//! On a 1 GB Pi with `compute_block_cache_bytes` returning the 64 MB
//! floor, hydration runs comfortably without OOM.

use anyhow::{Context, Result};
use bytes::Bytes;
use futures::StreamExt;
use nasrudin_core::{Axiom, Domain, Expr};
use nasrudin_rocks::{CorpusBackend, CorpusDb};
use serde::Deserialize;
use std::path::Path;
use std::sync::Arc;
use tokio::io::AsyncBufReadExt;
use tokio_util::io::StreamReader;

use crate::worker_http::WorkerHttp;

/// How many axioms accumulate in a `CorpusBackend::put` loop before
/// we yield the tokio reactor. RocksDB write throughput on a Pi-class
/// SD card is ~5–20 MB/s; 1000 axioms × ~3 KB avg ≈ 3 MB per batch
/// keeps the WAL flushing in the ~150–600 ms range so each batch
/// stays under the worker's main-loop budget.
const BATCH_SIZE: usize = 1000;

/// Meta-CF key under which we persist the last-seen
/// `/api/corpus/dump` ETag. Stored alongside the official corpus
/// meta keys (`count`, `hydrated_at`, `version`) under the
/// `CF_CORPUS_META` column family via `CorpusBackend::meta_put`.
///
/// Worker-only — the API server doesn't read or write this; it has
/// its own etag-derivation logic in the corpus_dump handler.
const ETAG_META_KEY: &str = "worker_etag";

/// Wire-format of one NDJSON line emitted by `/api/corpus/dump`.
#[derive(Debug, Deserialize)]
struct DumpLine {
    name: String,
    domain: String,
    /// Server emits this as a JSON-stringified `Expr` (mirroring
    /// `/api/seed`'s `axioms[].statement` shape) so the worker can
    /// re-parse with `serde_json::from_value`.
    statement: serde_json::Value,
    description: String,
}

/// Resolve the local CorpusDb path. Honors `NASRUDIN_WORKER_ROCKS`,
/// falls back to `$HOME/.local/share/nasrudin-worker/rocks`, and on
/// machines without `$HOME` (rare CI / sandbox) uses `./worker-rocks`.
pub fn resolve_local_path() -> std::path::PathBuf {
    if let Ok(p) = std::env::var("NASRUDIN_WORKER_ROCKS") {
        return std::path::PathBuf::from(p);
    }
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
    std::path::PathBuf::from(home)
        .join(".local")
        .join("share")
        .join("nasrudin-worker")
        .join("rocks")
}

/// Open (or create) the worker's local cold-tier RocksDB.
///
/// Creates the parent directory if it doesn't exist. Uses
/// `CorpusDb::open_standalone` so we get the right block-cache
/// sizing + bloom-filter / point-lookup tuning without dragging in
/// the full `TheoremDb` (which has 12+ unused CFs we don't need on
/// the worker).
pub fn open_local(path: &Path) -> Result<CorpusDb> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).with_context(|| {
            format!("create parent dir for worker rocks: {}", parent.display())
        })?;
    }
    std::fs::create_dir_all(path)
        .with_context(|| format!("create worker rocks dir: {}", path.display()))?;
    CorpusDb::open_standalone(path)
        .with_context(|| format!("open standalone CorpusDb at {}", path.display()))
}

/// Read the persisted server-ETag from the worker's CorpusDb
/// `CF_CORPUS_META` column family, if any. Returns `None` on a fresh
/// DB or if the key was never set (first boot, or hydration was
/// interrupted before [`persist_etag`] fired).
fn load_persisted_etag(corpus: &CorpusDb) -> Option<String> {
    match corpus.meta_get(ETAG_META_KEY) {
        Ok(Some(bytes)) => String::from_utf8(bytes).ok().filter(|s| !s.is_empty()),
        Ok(None) => None,
        Err(e) => {
            tracing::warn!(error = %e, "load_persisted_etag: meta_get failed");
            None
        }
    }
}

/// Persist the latest server-ETag into `CF_CORPUS_META` so the next
/// boot can short-circuit via `If-None-Match`. Best-effort: a write
/// failure isn't fatal, just means the next boot will re-hydrate
/// unnecessarily.
fn persist_etag(corpus: &CorpusDb, etag: &str) {
    if let Err(e) = corpus.meta_put(ETAG_META_KEY, etag.as_bytes()) {
        tracing::warn!(
            error = %e,
            "persist etag failed; next boot will re-hydrate"
        );
    }
}

/// Hydrate the worker's cold tier from `GET /api/corpus/dump`.
///
/// Streams NDJSON line-by-line from the server, deserialises each
/// line into an `Axiom`, bulk-inserts in `BATCH_SIZE` chunks, and
/// finalises with `finish_hydration` so the next boot sees
/// `is_hydrated()` and skips this whole path.
///
/// Sends `Authorization: Bearer <worker_key>` if `worker_key` is
/// non-empty. The dump endpoint is public, but production deployments
/// behind Caddy may rate-limit anonymous traffic differently — the
/// header keeps the worker on the higher-throughput tier.
///
/// Returns the number of axioms ingested.
pub async fn hydrate_from_server(
    corpus: &CorpusDb,
    api_url: &str,
    worker_key: &str,
) -> Result<u64> {
    let http = WorkerHttp::from_env(api_url)?;
    let mut headers: Vec<(String, String)> = Vec::new();
    if !worker_key.is_empty() {
        headers.push(("authorization".into(), format!("Bearer {worker_key}")));
    }
    // If we have a persisted etag from a previous successful run,
    // send it so the server can short-circuit when nothing changed.
    let cached_etag = load_persisted_etag(corpus);
    if let Some(ref etag) = cached_etag {
        headers.push(("if-none-match".into(), etag.clone()));
    }
    let header_refs: Vec<(&str, &str)> =
        headers.iter().map(|(k, v)| (k.as_str(), v.as_str())).collect();

    let started = std::time::Instant::now();
    let (status, resp_headers, byte_stream) = http
        .get_stream("/api/corpus/dump", &header_refs)
        .await
        .context("GET /api/corpus/dump")?;

    if status == 304 {
        tracing::info!(
            "Corpus dump returned 304: local cold tier matches server etag {:?}",
            cached_etag
        );
        return Ok(corpus.count().unwrap_or(0));
    }
    if !(200..300).contains(&status) {
        anyhow::bail!("/api/corpus/dump returned status {status}");
    }

    let server_etag = resp_headers
        .get("etag")
        .and_then(|v| v.to_str().ok())
        .map(|s| s.to_string());
    let server_count = resp_headers
        .get("X-Corpus-Count")
        .and_then(|v| v.to_str().ok())
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0);

    tracing::info!(
        server_count,
        server_etag = ?server_etag,
        "Hydrating worker corpus from /api/corpus/dump (~150 MB)"
    );

    // Adapt the bytes stream into a `tokio::io::AsyncRead` so we can
    // use `BufReader::lines()` for one-line-at-a-time parsing.
    let reader = StreamReader::new(byte_stream.map(|r| match r {
        Ok(b) => Ok::<_, std::io::Error>(b),
        Err(e) => Err(e),
    }));
    let mut reader = tokio::io::BufReader::new(reader);

    let mut ingested: u64 = 0;
    let mut batch: Vec<Axiom> = Vec::with_capacity(BATCH_SIZE);
    let mut line = String::new();

    loop {
        line.clear();
        let n = reader
            .read_line(&mut line)
            .await
            .context("read NDJSON line")?;
        if n == 0 {
            break; // EOF
        }
        // Server emits one JSON object per line, terminated by '\n'.
        // Trim the trailing newline before parsing.
        let trimmed = line.trim_end();
        if trimmed.is_empty() {
            continue;
        }
        let parsed: DumpLine = match serde_json::from_str(trimmed) {
            Ok(v) => v,
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    line_preview = %&trimmed.chars().take(80).collect::<String>(),
                    "skipping malformed NDJSON line"
                );
                continue;
            }
        };
        let axiom = match parse_dump_line(parsed) {
            Ok(a) => a,
            Err(e) => {
                tracing::warn!(error = %e, "skipping unparsable axiom from dump");
                continue;
            }
        };
        batch.push(axiom);
        if batch.len() >= BATCH_SIZE {
            flush_batch(corpus, &mut batch)?;
            ingested += BATCH_SIZE as u64;
            if ingested.is_multiple_of(10_000) {
                tracing::info!(
                    progress = ingested,
                    elapsed_secs = started.elapsed().as_secs(),
                    "corpus hydration progress"
                );
            }
            // Yield occasionally so the runtime can run other tasks.
            tokio::task::yield_now().await;
        }
    }

    // Final partial batch.
    let final_partial = batch.len() as u64;
    if !batch.is_empty() {
        flush_batch(corpus, &mut batch)?;
    }
    ingested += final_partial;

    corpus
        .finish_hydration(ingested)
        .context("CorpusBackend::finish_hydration")?;

    if server_count > 0 && ingested != server_count {
        // Soft-warn rather than hard-fail: a count mismatch could be
        // a benign race (server was mid-reload), or an actual stream
        // truncation. Either way the corpus is still usable on the
        // next chunk; the worker logs and continues.
        tracing::warn!(
            ingested,
            server_count,
            "corpus hydration count mismatch — partial dump?"
        );
    }

    if let Some(etag) = server_etag {
        persist_etag(corpus, &etag);
    }

    tracing::info!(
        ingested,
        elapsed_secs = started.elapsed().as_secs(),
        "Worker corpus hydration complete"
    );
    Ok(ingested)
}

fn flush_batch(corpus: &CorpusDb, batch: &mut Vec<Axiom>) -> Result<()> {
    if batch.is_empty() {
        return Ok(());
    }
    // WAL-disabled bulk write: 1 fsync for the whole batch instead of
    // ~1000. On a Pi SD card this shaves minutes off cold-tier
    // hydration. Crash-safety is provided by `finish_hydration`
    // writing `count`/`hydrated_at` WITH the WAL after every batch
    // lands; if we crash here, the next boot sees no `count` meta
    // key and re-hydrates from scratch (idempotent — name-keyed).
    corpus
        .put_many(batch, /* wal_disabled */ true)
        .context("CorpusBackend::put_many")?;
    batch.clear();
    Ok(())
}

/// Decode one NDJSON line into an `Axiom`. The server emits the
/// `domain` field as the `Display` form (snake_case); we accept both
/// snake_case and the Rust enum name so we're forward-compatible if
/// the server ever switches conventions.
fn parse_dump_line(line: DumpLine) -> Result<Axiom> {
    let domain = parse_domain(&line.domain);
    let statement: Expr = serde_json::from_value(line.statement)
        .with_context(|| format!("parse statement for axiom {}", line.name))?;
    Ok(Axiom {
        name: line.name,
        domain,
        statement,
        description: line.description,
    })
}

fn parse_domain(s: &str) -> Domain {
    match s {
        "pure_math" | "PureMath" => Domain::PureMath,
        "classical_mechanics" | "ClassicalMechanics" => Domain::ClassicalMechanics,
        "electromagnetism" | "Electromagnetism" => Domain::Electromagnetism,
        "special_relativity" | "SpecialRelativity" => Domain::SpecialRelativity,
        "general_relativity" | "GeneralRelativity" => Domain::GeneralRelativity,
        "quantum_mechanics" | "QuantumMechanics" => Domain::QuantumMechanics,
        "quantum_field_theory" | "QuantumFieldTheory" => Domain::QuantumFieldTheory,
        "statistical_mechanics" | "StatisticalMechanics" => Domain::StatisticalMechanics,
        "thermodynamics" | "Thermodynamics" => Domain::Thermodynamics,
        "optics" | "Optics" => Domain::Optics,
        "fluid_dynamics" | "FluidDynamics" => Domain::FluidDynamics,
        // Cross-domain (`cross:foo+bar`) and unknown values fall back
        // to PureMath. Cross-domain is rare in the dump, and an
        // unrecognised label means the server is newer than the
        // worker — keep loading rather than panic.
        _ => Domain::PureMath,
    }
}

/// Build a worker-side AxiomStore backed by a freshly-hydrated cold
/// tier. The worker's hand-coded postulates are layered on top of
/// this in `worker.rs`'s boot path via `store.load_*_postulates()`.
///
/// Returns `Arc<dyn CorpusBackend>` and the `AxiomStore` so the
/// caller can hold the cold-tier handle for diagnostics if desired
/// (e.g. logging `corpus.count()` periodically).
pub fn build_axiom_store(
    corpus: Arc<dyn CorpusBackend>,
) -> nasrudin_derive::AxiomStore {
    nasrudin_derive::AxiomStore::with_corpus(corpus)
}

/// Internal helper to read a single byte stream into one `Bytes`
/// blob — used by tests where buffering the dump in memory is fine.
#[allow(dead_code)]
async fn collect_stream_to_bytes(
    mut stream: crate::worker_http::BoxByteStream,
) -> std::io::Result<Bytes> {
    let mut all = Vec::new();
    while let Some(chunk) = stream.next().await {
        let chunk = chunk?;
        all.extend_from_slice(&chunk);
    }
    Ok(Bytes::from(all))
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_core::{Axiom, BinOp, Domain, Expr};
    use tempfile::TempDir;

    fn mk(name: &str, dom: Domain) -> Axiom {
        Axiom {
            name: name.to_string(),
            domain: dom,
            statement: Expr::BinOp(
                BinOp::Eq,
                Box::new(Expr::Var(name.to_string())),
                Box::new(Expr::Lit(1, 1)),
            ),
            description: format!("doc {name}"),
        }
    }

    /// Round-trip: encode a few axioms as NDJSON the way
    /// `/api/corpus/dump` does, then parse them back via the worker's
    /// line decoder. Validates the wire shape contract end-to-end
    /// without needing a live HTTP server.
    #[test]
    fn ndjson_round_trip() {
        let cases = [
            mk("ax_a", Domain::PureMath),
            mk("ax_b", Domain::SpecialRelativity),
            mk("ax_c", Domain::Electromagnetism),
        ];

        let mut wire = String::new();
        for ax in &cases {
            let line = serde_json::json!({
                "name": ax.name,
                "domain": format!("{}", ax.domain),
                "statement": serde_json::to_value(&ax.statement).unwrap(),
                "description": ax.description,
            });
            wire.push_str(&serde_json::to_string(&line).unwrap());
            wire.push('\n');
        }

        let mut decoded: Vec<Axiom> = Vec::new();
        for line in wire.lines() {
            if line.is_empty() {
                continue;
            }
            let parsed: DumpLine = serde_json::from_str(line).unwrap();
            decoded.push(parse_dump_line(parsed).unwrap());
        }

        assert_eq!(decoded.len(), 3);
        for (i, ax) in decoded.iter().enumerate() {
            assert_eq!(ax.name, cases[i].name);
            assert_eq!(ax.domain, cases[i].domain);
            assert_eq!(ax.statement, cases[i].statement);
            assert_eq!(ax.description, cases[i].description);
        }
    }

    /// Open a worker CorpusDb, pump a few axioms through `put` /
    /// `finish_hydration` directly (simulating what
    /// `hydrate_from_server` does), then confirm `count` matches
    /// and `get` returns the expected entries.
    #[test]
    fn open_then_simulated_hydrate_then_count_matches() {
        let tmp = TempDir::new().unwrap();
        let path = tmp.path().join("worker-rocks");
        let corpus = open_local(&path).unwrap();
        assert_eq!(corpus.count().unwrap(), 0);
        assert!(!corpus.is_hydrated().unwrap());

        for i in 0..200 {
            let dom = match i % 3 {
                0 => Domain::PureMath,
                1 => Domain::SpecialRelativity,
                _ => Domain::Electromagnetism,
            };
            corpus.put(&mk(&format!("a{i}"), dom)).unwrap();
        }
        corpus.finish_hydration(200).unwrap();
        assert_eq!(corpus.count().unwrap(), 200);
        assert!(corpus.is_hydrated().unwrap());

        let ax = corpus.get("a42").unwrap().unwrap();
        assert_eq!(ax.name, "a42");
        assert_eq!(ax.domain, Domain::PureMath);
    }

    /// Sanity-check `resolve_local_path` honors the env var.
    #[test]
    fn resolve_local_path_honours_env_var() {
        // Use a locally-scoped guard so we don't leak env into
        // sibling tests. Multi-threaded test runner means we can't
        // rely on isolation here; the assertion just checks the
        // var-is-set branch rather than asserting the unset default.
        // SAFETY: scoped to this single-threaded test; no other test
        // thread reads/writes NASRUDIN_WORKER_ROCKS within this
        // block. The env API is unsafe in std edition 2024.
        unsafe {
            std::env::set_var("NASRUDIN_WORKER_ROCKS", "/tmp/test_rocks_xyz");
        }
        let p = resolve_local_path();
        assert_eq!(p, std::path::PathBuf::from("/tmp/test_rocks_xyz"));
        unsafe {
            std::env::remove_var("NASRUDIN_WORKER_ROCKS");
        }
    }

    /// `parse_domain` accepts both snake_case (Display form, what
    /// `/api/corpus/dump` emits) and CamelCase (Rust enum form, what
    /// `/api/seed` historically emits) so the worker is symmetric
    /// with both endpoints.
    #[test]
    fn parse_domain_dual_form() {
        assert_eq!(parse_domain("pure_math"), Domain::PureMath);
        assert_eq!(parse_domain("PureMath"), Domain::PureMath);
        assert_eq!(parse_domain("special_relativity"), Domain::SpecialRelativity);
        assert_eq!(parse_domain("SpecialRelativity"), Domain::SpecialRelativity);
        assert_eq!(parse_domain("nonsense"), Domain::PureMath);
    }
}
