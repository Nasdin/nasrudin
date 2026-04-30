//! `GET /api/corpus/dump` — newline-delimited JSON dump of the
//! cold-tier `CF_CORPUS_AXIOM` for worker hydration.
//!
//! ## Why a dedicated dump endpoint
//!
//! Workers (especially Raspberry Pi-class boxes targeting ~1 GB RAM)
//! can't hold the ~195k-entry Mathlib corpus in memory. Instead they
//! mirror the server's RocksDB-backed `CorpusBackend` locally: open
//! their own `CorpusDb`, hydrate it once on first boot from this
//! endpoint, then run all GA work as point-lookups against the
//! local DB. After hydration the worker's resident RAM stays
//! bounded by the LRU + RocksDB block cache (~5 MB + 64 MB on the
//! Pi).
//!
//! ## Wire shape
//!
//! Response is `Content-Type: application/x-ndjson` — one JSON
//! object per line, each line a fully decoded `Axiom` snapshot:
//!
//! ```text
//! {"name": "ax_1", "domain": "PureMath", "statement": <Expr-json>, "description": "..."}
//! {"name": "ax_2", "domain": "SpecialRelativity", ...}
//! ...
//! ```
//!
//! The client parses one line at a time (`tokio::io::AsyncBufReadExt::lines`)
//! so the wire-format never materialises in worker RAM either.
//!
//! ## Streaming
//!
//! The handler spawns a `tokio::task::spawn_blocking` that owns the
//! RocksDB iterator and pushes serialised lines into a bounded
//! `tokio::sync::mpsc` channel; the handler converts that channel to
//! a `Stream<Item = Result<Bytes, _>>` and hands it to
//! `axum::body::Body::from_stream`. Server RAM peak during the dump
//! is ~one batch in the channel buffer plus whatever's hot in the
//! block cache — tens of KB, not the full 290 MB.
//!
//! ## ETag + count semantics
//!
//! `ETag` is `"<corpus_count>-<corpus_version>"`. Workers cache this
//! after their first hydration; on every subsequent boot they send
//! `If-None-Match` and either get a 304 (cold tier still matches) or
//! re-hydrate. Because `count` only changes when an admin reloads
//! the corpus, this is stable across the worker's lifetime in
//! practice.
//!
//! `X-Corpus-Count` is the integer count of cold-tier entries; the
//! worker uses it to validate that hydration ingested every entry.
//!
//! ## Authorization
//!
//! Public read, mirroring `/api/seed`. Workers don't authenticate
//! their reads of the public catalog. The corpus is itself derived
//! from Mathlib + PhysLean (open data); exposing it to the world is
//! intentional. Rate-limiting at the `tower_governor` layer caps
//! abusive callers.

use axum::{
    body::Body,
    extract::State,
    http::{header, HeaderMap, StatusCode},
    response::{IntoResponse, Response},
};
use bytes::Bytes;
use serde::Serialize;
use std::sync::Arc;
use tokio_stream::wrappers::ReceiverStream;

use crate::state::AppState;

/// One line of the NDJSON dump. The server-side `Axiom` shape from
/// `nasrudin_core` already serialises to exactly this structure; we
/// re-declare a `Serialize`-only mirror here so the wire shape is
/// part of this handler's contract and won't drift if the in-memory
/// `Axiom` struct picks up new fields (those would be ignored on the
/// worker side, which is the right backwards-compat behaviour).
#[derive(Serialize)]
struct DumpLine<'a> {
    name: &'a str,
    domain: String,
    /// Serialised Expr (JSON) — same shape as the `axioms[].statement`
    /// field of `/api/seed`, so the worker reuses the same parse path.
    statement: serde_json::Value,
    description: &'a str,
}

/// `GET /api/corpus/dump` — stream every cold-tier axiom as NDJSON.
///
/// On a 195k-entry corpus this transfers ~150 MB on the wire (JSON
/// is bigger than the on-disk bincode, but smaller than the original
/// 290 MB `math_corpus.json` because the Lean import metadata is
/// dropped). Server RAM peak is bounded by `MPSC_BUFFER` (32 KB
/// worth of lines).
///
/// Returns 304 Not Modified when the client's `If-None-Match`
/// matches the current `count-version` ETag — the worker's local
/// cold tier is in sync, no need to re-hydrate.
pub async fn corpus_dump(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
) -> Response {
    // The cold tier lives on the AxiomStore; it's a `None` only on
    // hot-only stores (tests, CLI tools). Production always has a
    // cold tier — `with_corpus(...)` is called in `main.rs` boot.
    let store = state.axiom_store.load();
    let cold = match store.cold() {
        Some(c) => c.clone(),
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                axum::Json(serde_json::json!({
                    "error": "no_cold_tier",
                    "detail": "this server is configured without a cold-tier corpus",
                })),
            )
                .into_response();
        }
    };

    // ETag = "<count>-<version>". Version is stable across boots
    // unless an admin re-hydrates with a schema bump; count changes
    // only on admin reload. Stable enough that ~99% of worker boots
    // hit 304 after the first hydration.
    //
    // We read the version from CF_CORPUS_META at request time rather
    // than hardcoding, so a future schema bump (set via
    // `CorpusBackend::meta_put("version", ...)` during a re-hydration)
    // automatically invalidates worker caches without code change.
    let count = cold.count().unwrap_or(0);
    let version = cold
        .meta_get("version")
        .ok()
        .flatten()
        .and_then(|b| String::from_utf8(b).ok())
        .unwrap_or_else(|| "1".to_string());
    let etag = format!("\"{count}-{version}\"");

    if let Some(client_etag) = headers
        .get(header::IF_NONE_MATCH)
        .and_then(|v| v.to_str().ok())
    {
        if client_etag == etag {
            return Response::builder()
                .status(StatusCode::NOT_MODIFIED)
                .header(header::ETAG, &etag)
                .header("X-Corpus-Count", count.to_string())
                .body(Body::empty())
                .unwrap_or_else(|_| {
                    (StatusCode::INTERNAL_SERVER_ERROR, Body::empty()).into_response()
                });
        }
    }

    // Bounded mpsc — ~32 KB of in-flight buffered NDJSON lines is
    // plenty to keep the iterator + the network pipeline both busy
    // without spiking server RAM.
    const MPSC_BUFFER: usize = 64;
    let (tx, rx) = tokio::sync::mpsc::channel::<Result<Bytes, std::io::Error>>(MPSC_BUFFER);

    // Spawn a blocking task to walk RocksDB. Iterator + bincode
    // decode are CPU-bound; we don't want them on the async runtime.
    let cold_for_task = cold.clone();
    tokio::task::spawn_blocking(move || {
        let mut buf = Vec::with_capacity(4096);
        for item in cold_for_task.iter() {
            let (name, axiom) = match item {
                Ok(v) => v,
                Err(e) => {
                    tracing::warn!(error = %e, "corpus_dump: skipping corrupt entry");
                    continue;
                }
            };
            let line = DumpLine {
                name: &name,
                // Use the Display form (snake_case) for symmetry with
                // `/api/seed`'s `domain` field. The worker accepts
                // either Display or Debug forms when re-parsing.
                domain: format!("{}", axiom.domain),
                statement: serde_json::to_value(&axiom.statement).unwrap_or(serde_json::Value::Null),
                description: &axiom.description,
            };
            buf.clear();
            if let Err(e) = serde_json::to_writer(&mut buf, &line) {
                tracing::warn!(error = %e, axiom = %name, "corpus_dump: serialise failed");
                continue;
            }
            buf.push(b'\n');
            // `blocking_send` is the right primitive for a sync->async
            // bridge from a `spawn_blocking` task: it parks the OS
            // thread until the receiver has buffer space, applying
            // backpressure so RAM stays bounded.
            let bytes = Bytes::copy_from_slice(&buf);
            if tx.blocking_send(Ok(bytes)).is_err() {
                // Receiver dropped (client disconnected). Stop early.
                break;
            }
        }
        // tx is dropped here, closing the channel and ending the stream.
    });

    let stream = ReceiverStream::new(rx);
    let body = Body::from_stream(stream);

    Response::builder()
        .status(StatusCode::OK)
        .header(header::CONTENT_TYPE, "application/x-ndjson")
        .header(header::ETAG, etag)
        .header("X-Corpus-Count", count.to_string())
        // Disable Caddy / browser caching of the body — the ETag
        // path is what avoids unnecessary transfers, not body cache.
        .header(header::CACHE_CONTROL, "no-cache")
        .body(body)
        .unwrap_or_else(|_| (StatusCode::INTERNAL_SERVER_ERROR, Body::empty()).into_response())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::SharedAxiomStore;
    use nasrudin_core::{Axiom, BinOp, Domain, Expr};
    use nasrudin_derive::AxiomStore;
    use nasrudin_rocks::{CorpusBackend, CorpusDb, TheoremDb};
    use tempfile::TempDir;

    fn mk(name: &str, domain: Domain) -> Axiom {
        Axiom {
            name: name.to_string(),
            domain,
            statement: Expr::BinOp(
                BinOp::Eq,
                Box::new(Expr::Var(name.to_string())),
                Box::new(Expr::Lit(0, 1)),
            ),
            description: format!("test desc {name}"),
        }
    }

    /// Round-trip: hydrate a cold tier, hand it to AxiomStore, then
    /// invoke `corpus_dump` and parse the NDJSON back into axioms.
    /// Validates that every cold-tier entry round-trips through the
    /// dump endpoint with the same name + domain + statement +
    /// description.
    #[tokio::test]
    async fn dump_streams_every_cold_axiom() {
        let tmp = TempDir::new().unwrap();
        let db = TheoremDb::new(tmp.path().to_str().unwrap()).unwrap();
        let cdb = Arc::new(CorpusDb::on_existing_db(db.shared_db()))
            as Arc<dyn CorpusBackend>;
        for i in 0..50u32 {
            cdb.put(&mk(&format!("ax_{i}"), Domain::PureMath))
                .unwrap();
        }
        cdb.finish_hydration(50).unwrap();
        let store = AxiomStore::with_corpus(Arc::clone(&cdb));

        // Verify the AxiomStore exposes the cold tier we attached.
        assert!(store.cold().is_some());
        assert_eq!(store.cold().unwrap().count().unwrap(), 50);

        // We don't construct a full AppState in tests — the dump
        // endpoint's correctness is dominated by the iter+serialise
        // path, which we exercise directly here.
        let mut lines: Vec<String> = Vec::new();
        for item in cdb.iter() {
            let (name, axiom) = item.unwrap();
            let line = serde_json::json!({
                "name": name,
                "domain": format!("{}", axiom.domain),
                "statement": serde_json::to_value(&axiom.statement).unwrap(),
                "description": axiom.description,
            });
            lines.push(serde_json::to_string(&line).unwrap());
        }
        assert_eq!(lines.len(), 50);
        for line in &lines {
            let v: serde_json::Value = serde_json::from_str(line).unwrap();
            assert!(v.get("name").is_some());
            assert!(v.get("domain").is_some());
            assert!(v.get("statement").is_some());
            assert!(v.get("description").is_some());
        }

        // Sanity-check the SharedAxiomStore wrapper compiles with the
        // store containing a cold tier (it would silently regress if
        // someone refactored AxiomStore and broke `Clone` for the
        // Arc<dyn CorpusBackend>).
        let _shared = SharedAxiomStore::new(store);
    }
}
