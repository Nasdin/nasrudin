# LLM-Guided Search — Phase B — Embedding Store Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship `nasrudin-embed` — a local-CPU embedding store over the verified-theorem corpus — plus the nightly build job, the HTTP distribution endpoint, and the worker-side auto-pull. After this lands, the conjecture LLM router can call `EmbeddingIndex::nearest_text(hunch, 10)` and the GA can fall back to skeleton-embedding lookup when exact-hash priors miss.

**Architecture:** New crate `engine/crates/embed/` wraps `fastembed-rs` (BAAI/bge-small-en-v1.5, 384 dims) for text → vector and `instant-distance` (HNSW) for vector → nearest theorem. Persistent format: a memory-mapped `corpus.embed` file (header + flat `(TheoremId, [f32; 384])` records) plus a sidecar `corpus.hnsw` HNSW snapshot. The API server runs a tokio task that rebuilds nightly (and after every 1000 new verifications). Workers pull `/api/embed/index.bin` on heartbeat when their local checksum mismatches.

**Tech Stack:** Rust 1.95, `fastembed = "4"` (ONNX-backed BGE), `instant-distance = "0.6"` (pure-Rust HNSW), `memmap2 = "0.9"` (mmap), `blake3` (already a workspace dep — used for the index checksum), `tokio` (existing), `axum` (existing), `chrono` (existing).

---

## Spec reference

Implements §5 ("Embedding store") + the relevant parts of §13 Phase B of `docs/superpowers/specs/2026-04-28-llm-guided-search-design.md`. The spec splits into:

- §5.1 — Model: `BAAI/bge-small-en-v1.5`, 384 dims, ~130 MB.
- §5.2 — Corpus index: `~/.nasrudin/embed/corpus.embed` + sidecar HNSW; built nightly + after 1000 new verifications; ~390 MB at 250k theorems.
- §5.3 — Public API: `open`, `embed`, `nearest`, `nearest_text`.
- §13 Phase B — Distribute via `/api/embed/index.bin` with signed checksum; workers download on next heartbeat.

Out of scope for this plan (deferred to a future plan if needed): GPU acceleration, alternate embedding models, vector quantisation. The default model is good enough; we can swap in later.

---

## Scope check

This plan covers one independent subsystem (the embedding store) and a tight integration point (server endpoint + worker pull). Both ship together because the endpoint is useless without consumers and the worker-side pull is useless without an endpoint. No further decomposition needed.

---

## File structure

**New files:**

| Path | Responsibility |
|---|---|
| `engine/crates/embed/Cargo.toml` | Crate manifest |
| `engine/crates/embed/src/lib.rs` | Module declarations + re-exports |
| `engine/crates/embed/src/model.rs` | `fastembed`-backed text → 384-dim wrapper |
| `engine/crates/embed/src/format.rs` | On-disk wire format for `corpus.embed` (header + records) |
| `engine/crates/embed/src/index.rs` | `EmbeddingIndex` — memory-mapped open + nearest |
| `engine/crates/embed/src/builder.rs` | Build a fresh index from an iterator of (TheoremId, source_text) |
| `engine/crates/embed/src/checksum.rs` | BLAKE3 over the .embed file body for distribution validation |
| `engine/crates/embed/tests/integration_round_trip.rs` | Build → save → open → nearest end-to-end |
| `engine/crates/embed/tests/integration_semantic.rs` | "Energy" theorems are nearer to "energy" hunches than to "fluid" hunches |
| `engine/crates/api/src/bin/embed_build.rs` | `nasrudin-embed-build` CLI: scan TheoremDb → write corpus.embed + corpus.hnsw |
| `engine/crates/api/src/handlers/embed.rs` | `/api/embed/index.bin`, `/api/embed/checksum` handlers |
| `engine/crates/api/src/embed_cron.rs` | Background tokio task: rebuild nightly + after 1000 new verifications |
| `engine/crates/embed/EMBED_LAYER.md` | Operator docs (build invocation, layout, refresh cadence) |

**Modified files:**

| Path | Change |
|---|---|
| `engine/Cargo.toml` | Add `fastembed`, `instant-distance`, `memmap2` to workspace deps; add `embed` crate to `workspace.members` |
| `engine/crates/api/Cargo.toml` | Depend on `nasrudin-embed`; register `embed_build` bin target |
| `engine/crates/api/src/main.rs` | Construct optional `EmbeddingIndex` at boot; spawn `embed_cron` if env-flagged |
| `engine/crates/api/src/state.rs` | Add `embed: Option<Arc<nasrudin_embed::EmbeddingIndex>>` |
| `engine/crates/api/src/lib.rs` | Add `pub mod embed_cron;` and route registrations for `/api/embed/*` |

---

## Conventions for this plan

- Run `cargo check --workspace` after every task; expect exit 0 before committing.
- Run `cargo test --workspace` before committing tasks that touch existing code.
- Commit messages: `feat(embed): …`, `test(embed): …`, `docs(embed): …`.
- All commits include `Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>`. The harness does NOT add it; pass via HEREDOC.
- Embedding-model download happens at first `EmbeddingIndex::new()`; tests run with the model cached at `~/.cache/fastembed/`. CI must pre-warm or skip those tests with `#[ignore]`.
- Default Phase B is OFF: server only constructs the index when `NASRUDIN_EMBED_ENABLED=1`. Workers only auto-pull when `NASRUDIN_EMBED_AUTOPULL=1`.

---

## Task 1: Workspace deps + crate skeleton

**Files:**
- Modify: `engine/Cargo.toml`
- Create: `engine/crates/embed/Cargo.toml`
- Create: `engine/crates/embed/src/lib.rs`

- [ ] **Step 1: Add deps + member to workspace**

In `engine/Cargo.toml`, under `[workspace.dependencies]`, add:

```toml
fastembed = "4"
instant-distance = "0.6"
memmap2 = "0.9"
```

Under `[workspace] members = [...]`, add `"crates/embed"` (matching the existing list-formatting style).

- [ ] **Step 2: Create crate manifest**

Create `engine/crates/embed/Cargo.toml`:

```toml
[package]
name = "nasrudin-embed"
version = "0.1.0"
edition = "2024"

[dependencies]
nasrudin-core = { path = "../core" }
anyhow = { workspace = true }
serde = { workspace = true }
serde_json = { workspace = true }
fastembed = { workspace = true }
instant-distance = { workspace = true }
memmap2 = { workspace = true }
blake3 = { workspace = true }
tracing = { workspace = true }
chrono = { workspace = true, features = ["serde"] }

[dev-dependencies]
tempfile = { workspace = true }
```

- [ ] **Step 3: Create `lib.rs` with module skeleton**

Create `engine/crates/embed/src/lib.rs`:

```rust
//! Local-CPU embedding store over the verified-theorem corpus.
//!
//! - [`model`] wraps fastembed for `text -> 384-dim vector`.
//! - [`format`] defines the on-disk `corpus.embed` wire layout.
//! - [`index`] memory-maps a built corpus and exposes `nearest(...)`.
//! - [`builder`] writes a fresh index from a stream of theorems.
//! - [`checksum`] computes a BLAKE3 hash of an index file body for
//!   distribution validation.

pub mod builder;
pub mod checksum;
pub mod format;
pub mod index;
pub mod model;

pub use checksum::{compute_index_checksum, IndexChecksum};
pub use format::{IndexHeader, EMBED_DIM, INDEX_MAGIC, INDEX_VERSION};
pub use index::{EmbeddingIndex, NearestHit};
pub use model::Embedder;
```

- [ ] **Step 4: Verify crate compiles (empty modules)**

Create stubs so the workspace builds. Add to `engine/crates/embed/src/`:

```bash
mkdir -p /Volumes/CORSAIR/code/personal/nasrudin/engine/crates/embed/src
```

Create `model.rs`, `format.rs`, `index.rs`, `builder.rs`, `checksum.rs` each containing only:

```rust
// stub — implemented in subsequent tasks
```

(Each task below replaces the stub with real content.)

- [ ] **Step 5: Confirm workspace compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: `Finished` line, exit 0.

- [ ] **Step 6: Commit**

```bash
git add engine/Cargo.toml engine/crates/embed/
git commit -m "$(cat <<'EOF'
chore(embed): add nasrudin-embed crate skeleton + workspace deps

fastembed (BGE small ONNX), instant-distance (HNSW), memmap2 added
to workspace. Crate skeleton has empty modules; subsequent tasks
fill them in.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: On-disk wire format

**Files:**
- Modify: `engine/crates/embed/src/format.rs`

- [ ] **Step 1: Write the failing test**

Replace `engine/crates/embed/src/format.rs` with:

```rust
//! On-disk format for `corpus.embed`.
//!
//! ```text
//! ┌─ Header (64 bytes, little-endian) ──────────────────────┐
//! │  0..4    magic     b"NEMB"                              │
//! │  4..8    version   u32 = 1                              │
//! │  8..12   dim       u32 = 384                            │
//! │  12..16  count     u32 — number of records              │
//! │  16..24  built_at  i64 unix-millis                      │
//! │  24..32  reserved  must be 0                            │
//! │  32..64  padding   must be 0                            │
//! ├─ Records (count × 1544 bytes) ───────────────────────────┤
//! │   8     TheoremId       [u8; 8]                         │
//! │   1536  vector          [f32; 384] little-endian        │
//! └──────────────────────────────────────────────────────────┘
//! ```
//!
//! The header is 64 bytes (cache-line aligned) so records start at a
//! 64-byte boundary. The flat layout means `EmbeddingIndex` can mmap
//! the file and slice records by offset without parsing.

pub const INDEX_MAGIC: [u8; 4] = *b"NEMB";
pub const INDEX_VERSION: u32 = 1;
pub const EMBED_DIM: u32 = 384;
pub const HEADER_SIZE: usize = 64;
pub const RECORD_SIZE: usize = 8 + (EMBED_DIM as usize) * 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IndexHeader {
    pub version: u32,
    pub dim: u32,
    pub count: u32,
    pub built_at_millis: i64,
}

impl IndexHeader {
    /// Encode `self` to a 64-byte header.
    pub fn encode(&self) -> [u8; HEADER_SIZE] {
        let mut out = [0u8; HEADER_SIZE];
        out[0..4].copy_from_slice(&INDEX_MAGIC);
        out[4..8].copy_from_slice(&self.version.to_le_bytes());
        out[8..12].copy_from_slice(&self.dim.to_le_bytes());
        out[12..16].copy_from_slice(&self.count.to_le_bytes());
        out[16..24].copy_from_slice(&self.built_at_millis.to_le_bytes());
        // 24..64 left as zeros (reserved + padding).
        out
    }

    /// Decode + validate a header. Returns an error if magic / version
    /// / dim are wrong (we do NOT auto-migrate older indices — operator
    /// must rebuild on version bump).
    pub fn decode(bytes: &[u8]) -> anyhow::Result<Self> {
        if bytes.len() < HEADER_SIZE {
            anyhow::bail!("header too short: {} < {HEADER_SIZE}", bytes.len());
        }
        if bytes[0..4] != INDEX_MAGIC {
            anyhow::bail!("bad magic: {:?}", &bytes[0..4]);
        }
        let version = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        if version != INDEX_VERSION {
            anyhow::bail!("unsupported index version {version} (this build supports {INDEX_VERSION})");
        }
        let dim = u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]);
        if dim != EMBED_DIM {
            anyhow::bail!("dim mismatch: file has {dim}, build expects {EMBED_DIM}");
        }
        let count = u32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]);
        let built_at_millis = i64::from_le_bytes([
            bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
        ]);
        Ok(Self {
            version,
            dim,
            count,
            built_at_millis,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_round_trips() {
        let h = IndexHeader {
            version: 1,
            dim: 384,
            count: 12345,
            built_at_millis: 1_700_000_000_000,
        };
        let encoded = h.encode();
        assert_eq!(encoded.len(), HEADER_SIZE);
        assert_eq!(&encoded[0..4], &INDEX_MAGIC);
        let decoded = IndexHeader::decode(&encoded).unwrap();
        assert_eq!(decoded, h);
    }

    #[test]
    fn header_rejects_wrong_magic() {
        let mut bad = IndexHeader {
            version: 1,
            dim: 384,
            count: 0,
            built_at_millis: 0,
        }
        .encode();
        bad[0] = b'X';
        assert!(IndexHeader::decode(&bad).is_err());
    }

    #[test]
    fn header_rejects_wrong_version() {
        let mut bad = IndexHeader {
            version: 999,
            dim: 384,
            count: 0,
            built_at_millis: 0,
        }
        .encode();
        bad[0..4].copy_from_slice(&INDEX_MAGIC);
        assert!(IndexHeader::decode(&bad).is_err());
    }

    #[test]
    fn header_rejects_wrong_dim() {
        let mut bad = IndexHeader {
            version: 1,
            dim: 256,
            count: 0,
            built_at_millis: 0,
        }
        .encode();
        bad[0..4].copy_from_slice(&INDEX_MAGIC);
        bad[4..8].copy_from_slice(&1u32.to_le_bytes());
        assert!(IndexHeader::decode(&bad).is_err());
    }

    #[test]
    fn record_size_is_8_plus_dim_bytes() {
        assert_eq!(RECORD_SIZE, 8 + 384 * 4);
    }
}
```

- [ ] **Step 2: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-embed format:: 2>&1 | tail -10
```

Expected: 5 pass.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/embed/src/format.rs
git commit -m "$(cat <<'EOF'
feat(embed): on-disk wire format with magic + version validation

64-byte header (NEMB magic, dim=384, version=1, count, built_at) +
flat 1544-byte records (8-byte TheoremId + 384 little-endian f32).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: BLAKE3 checksum over the index body

**Files:**
- Modify: `engine/crates/embed/src/checksum.rs`

- [ ] **Step 1: Write the failing test**

Replace `engine/crates/embed/src/checksum.rs` with:

```rust
//! BLAKE3 checksum over a built `corpus.embed`.
//!
//! Workers download `/api/embed/index.bin` and compare the `Sha-Embed`
//! HTTP header (which carries the BLAKE3 hex digest) against this
//! function's output before swapping the file in. Mismatch =
//! corrupted transfer = retry.

use anyhow::Result;
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexChecksum {
    /// Hex-encoded BLAKE3-256 digest.
    pub hex: String,
    /// Total bytes hashed.
    pub bytes: u64,
}

/// Stream-hash the entire file at `path`.
pub fn compute_index_checksum(path: &Path) -> Result<IndexChecksum> {
    use std::io::Read;
    let mut file = std::fs::File::open(path)?;
    let mut hasher = blake3::Hasher::new();
    let mut buf = [0u8; 64 * 1024];
    let mut total: u64 = 0;
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
        total += n as u64;
    }
    Ok(IndexChecksum {
        hex: hasher.finalize().to_hex().to_string(),
        bytes: total,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::tempdir;

    #[test]
    fn empty_file_has_known_blake3_digest() {
        let dir = tempdir().unwrap();
        let p = dir.path().join("empty.bin");
        std::fs::write(&p, []).unwrap();
        let cs = compute_index_checksum(&p).unwrap();
        assert_eq!(
            cs.hex,
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
            "BLAKE3 of empty input is well-known"
        );
        assert_eq!(cs.bytes, 0);
    }

    #[test]
    fn deterministic_across_calls() {
        let dir = tempdir().unwrap();
        let p = dir.path().join("data.bin");
        let mut f = std::fs::File::create(&p).unwrap();
        f.write_all(b"hello, embeddings").unwrap();
        let a = compute_index_checksum(&p).unwrap();
        let b = compute_index_checksum(&p).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn different_content_diverges() {
        let dir = tempdir().unwrap();
        let p1 = dir.path().join("a.bin");
        let p2 = dir.path().join("b.bin");
        std::fs::write(&p1, b"alpha").unwrap();
        std::fs::write(&p2, b"beta").unwrap();
        let a = compute_index_checksum(&p1).unwrap();
        let b = compute_index_checksum(&p2).unwrap();
        assert_ne!(a.hex, b.hex);
    }
}
```

- [ ] **Step 2: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-embed checksum:: 2>&1 | tail -10
```

Expected: 3 pass.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/embed/src/checksum.rs
git commit -m "$(cat <<'EOF'
feat(embed): blake3 checksum over corpus.embed

Streaming hash for index distribution validation. Workers compare the
server's Sha-Embed header against this digest before swapping the
local index in.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: `Embedder` (fastembed wrapper)

**Files:**
- Modify: `engine/crates/embed/src/model.rs`

- [ ] **Step 1: Write the failing test**

Replace `engine/crates/embed/src/model.rs` with:

```rust
//! Text → 384-dim wrapper around `fastembed`.

use anyhow::{Context, Result};
use fastembed::{EmbeddingModel, InitOptions, TextEmbedding};

/// Wraps a fastembed `TextEmbedding`. One instance per process is
/// usually sufficient — model load is ~150 MB resident, ~1 second cold.
pub struct Embedder {
    inner: TextEmbedding,
}

impl Embedder {
    /// Construct using the default model (BGE small en v1.5, 384 dims).
    pub fn new() -> Result<Self> {
        let inner = TextEmbedding::try_new(
            InitOptions::new(EmbeddingModel::BGESmallENV15).with_show_download_progress(false),
        )
        .context("init fastembed BGE small")?;
        Ok(Self { inner })
    }

    /// Embed a single text. Returns a 384-dim vector.
    pub fn embed_one(&self, text: &str) -> Result<Vec<f32>> {
        let mut v = self
            .inner
            .embed(vec![text.to_string()], None)
            .context("fastembed embed_one")?;
        v.pop().context("fastembed returned empty embed batch")
    }

    /// Embed a batch. Faster than calling `embed_one` per element.
    pub fn embed_batch(&self, texts: Vec<String>) -> Result<Vec<Vec<f32>>> {
        self.inner.embed(texts, None).context("fastembed embed_batch")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Heavy: downloads the model on first run (~130 MB). CI should
    /// either pre-warm `~/.cache/fastembed/` or set
    /// `NASRUDIN_SKIP_EMBED_DOWNLOAD=1` to skip.
    #[test]
    #[ignore]
    fn embed_one_returns_384_dims() {
        if std::env::var("NASRUDIN_SKIP_EMBED_DOWNLOAD").is_ok() {
            return;
        }
        let e = Embedder::new().expect("model init");
        let v = e.embed_one("E equals m c squared").unwrap();
        assert_eq!(v.len(), 384);
    }

    #[test]
    #[ignore]
    fn deterministic_across_calls() {
        if std::env::var("NASRUDIN_SKIP_EMBED_DOWNLOAD").is_ok() {
            return;
        }
        let e = Embedder::new().expect("model init");
        let a = e.embed_one("kinetic energy").unwrap();
        let b = e.embed_one("kinetic energy").unwrap();
        // Allow ε for nondeterministic ONNX backends; assert nearly equal.
        for (x, y) in a.iter().zip(b.iter()) {
            assert!((x - y).abs() < 1e-5, "embeddings should be ~deterministic");
        }
    }
}
```

- [ ] **Step 2: Run tests (expect ignored to skip)**

```bash
cd engine && cargo test -p nasrudin-embed model:: 2>&1 | tail -10
```

Expected: `0 passed; 0 failed; 2 ignored`. The model-loading tests are gated `#[ignore]` because they download ~130 MB; an operator can run them with `cargo test -p nasrudin-embed model:: -- --ignored`.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/embed/src/model.rs
git commit -m "$(cat <<'EOF'
feat(embed): fastembed-backed Embedder (BGE small, 384 dims)

embed_one / embed_batch wrappers around fastembed::TextEmbedding.
Tests are #[ignore] because the model download is ~130 MB.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: `EmbeddingIndex` open + nearest

**Files:**
- Modify: `engine/crates/embed/src/index.rs`

- [ ] **Step 1: Write the failing test**

Replace `engine/crates/embed/src/index.rs` with:

```rust
//! Memory-mapped read-only `corpus.embed` + HNSW lookup.
//!
//! `EmbeddingIndex::open(path)` mmaps the index file and loads the
//! sidecar HNSW. `nearest(vec, k)` returns the top-`k` (TheoremId,
//! cosine-distance) pairs.

use anyhow::{Context, Result};
use instant_distance::{Builder as HnswBuilder, HnswMap, Search};
use memmap2::Mmap;
use nasrudin_core::TheoremId;
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::format::{IndexHeader, EMBED_DIM, HEADER_SIZE, RECORD_SIZE};

/// Cosine-distance (1 - cosine_similarity) between unit-normalised
/// vectors. fastembed's BGE outputs are L2-normalised, so this is
/// equivalent to using dot-product as similarity.
#[derive(Debug, Clone)]
pub struct CosinePoint(pub Vec<f32>);

impl instant_distance::Point for CosinePoint {
    fn distance(&self, other: &Self) -> f32 {
        let mut dot = 0.0f32;
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            dot += a * b;
        }
        // Distance = 1 - similarity; assumes L2-normalised inputs.
        1.0 - dot
    }
}

/// One nearest-neighbour result.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct NearestHit {
    pub theorem_id: TheoremId,
    /// Cosine distance: 0 = identical direction, 2 = opposite.
    pub distance: f32,
}

/// Lookup index. Holds the mmap alive for the lifetime of the struct
/// so the HNSW points (which borrow from the mmap) stay valid.
pub struct EmbeddingIndex {
    /// Held to keep the file mapped; never read directly.
    _mmap: Arc<Mmap>,
    header: IndexHeader,
    hnsw: HnswMap<CosinePoint, TheoremId>,
}

impl EmbeddingIndex {
    /// Open both `<path>` (corpus.embed) and `<path>.hnsw` (sidecar).
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let file = File::open(path).with_context(|| format!("open {path:?}"))?;
        let mmap = unsafe { Mmap::map(&file).with_context(|| format!("mmap {path:?}"))? };
        if mmap.len() < HEADER_SIZE {
            anyhow::bail!("index file too small ({} bytes)", mmap.len());
        }
        let header = IndexHeader::decode(&mmap[..HEADER_SIZE])?;
        let body_bytes = (header.count as usize) * RECORD_SIZE;
        if mmap.len() < HEADER_SIZE + body_bytes {
            anyhow::bail!(
                "index body truncated: expected {} bytes, file has {}",
                HEADER_SIZE + body_bytes,
                mmap.len()
            );
        }

        // Load HNSW sidecar.
        let hnsw_path = sidecar_path(path);
        let hnsw_bytes = std::fs::read(&hnsw_path)
            .with_context(|| format!("read hnsw sidecar {hnsw_path:?}"))?;
        let hnsw: HnswMap<CosinePoint, TheoremId> = bincode::deserialize(&hnsw_bytes)
            .context("deserialise HNSW sidecar")?;

        Ok(Self {
            _mmap: Arc::new(mmap),
            header,
            hnsw,
        })
    }

    /// How many records are indexed.
    pub fn len(&self) -> usize {
        self.header.count as usize
    }

    /// Whether the index is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Top-`k` nearest theorems to `query`. Empty result if the index
    /// is empty.
    pub fn nearest(&self, query: &[f32], k: usize) -> Vec<NearestHit> {
        if self.is_empty() || k == 0 {
            return Vec::new();
        }
        if query.len() != EMBED_DIM as usize {
            tracing::warn!(
                "EmbeddingIndex::nearest: query dim {} != index dim {EMBED_DIM}",
                query.len()
            );
            return Vec::new();
        }
        let mut search = Search::default();
        let point = CosinePoint(query.to_vec());
        self.hnsw
            .search(&point, &mut search)
            .take(k)
            .map(|item| NearestHit {
                theorem_id: *item.value,
                distance: item.distance,
            })
            .collect()
    }

    pub fn header(&self) -> IndexHeader {
        self.header
    }
}

/// Sidecar path: `corpus.embed` → `corpus.embed.hnsw`.
pub fn sidecar_path(main: &Path) -> PathBuf {
    let mut p = main.as_os_str().to_owned();
    p.push(".hnsw");
    PathBuf::from(p)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cosine_point_distance_zero_for_identical() {
        let p = CosinePoint(vec![0.5, 0.5, 0.5, 0.5]);
        // Identical direction (assuming unit-normalised inputs the
        // dot product equals 1) so distance is 0. We use a fake unit
        // vector here for the math.
        let q = CosinePoint(vec![0.5, 0.5, 0.5, 0.5]);
        let d = p.distance(&q);
        assert!((d - (1.0 - 1.0)).abs() < 1e-6);
    }

    #[test]
    fn cosine_point_distance_orthogonal_is_one() {
        let p = CosinePoint(vec![1.0, 0.0, 0.0, 0.0]);
        let q = CosinePoint(vec![0.0, 1.0, 0.0, 0.0]);
        let d = p.distance(&q);
        assert!((d - 1.0).abs() < 1e-6);
    }

    #[test]
    fn sidecar_path_appends_hnsw() {
        let p = std::path::PathBuf::from("/tmp/corpus.embed");
        let s = sidecar_path(&p);
        assert_eq!(s, std::path::PathBuf::from("/tmp/corpus.embed.hnsw"));
    }
}
```

Add `bincode = "1"` to `engine/crates/embed/Cargo.toml`:

```toml
bincode = "1"
```

(In the `[dependencies]` section.)

- [ ] **Step 2: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-embed index:: 2>&1 | tail -10
```

Expected: 3 pass.

- [ ] **Step 3: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/embed/src/index.rs engine/crates/embed/Cargo.toml
git commit -m "$(cat <<'EOF'
feat(embed): EmbeddingIndex::open + nearest

mmap of corpus.embed for the flat record body, bincode-deserialised
HNSW sidecar for nearest-neighbour. Cosine distance (assumes BGE's
L2-normalised outputs).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: `nearest_text` convenience

**Files:**
- Modify: `engine/crates/embed/src/index.rs`

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/embed/src/index.rs` (above `#[cfg(test)] mod tests`):

```rust
impl EmbeddingIndex {
    /// Embed `text` then call `nearest`.
    pub fn nearest_text(
        &self,
        embedder: &crate::model::Embedder,
        text: &str,
        k: usize,
    ) -> Result<Vec<NearestHit>> {
        let v = embedder.embed_one(text)?;
        Ok(self.nearest(&v, k))
    }
}
```

Append to the `#[cfg(test)] mod tests` in the same file:

```rust
    #[test]
    fn nearest_text_signature_compiles() {
        // Pure type-level test: we don't have a real index here (and
        // certainly can't build one in unit tests without downloading
        // the model). Construct the function pointer to confirm the
        // signature lines up; the integration test in Task 8 covers
        // the real path.
        let _f: fn(&EmbeddingIndex, &crate::model::Embedder, &str, usize) -> Result<Vec<NearestHit>> =
            EmbeddingIndex::nearest_text;
    }
```

- [ ] **Step 2: Run test, verify pass**

```bash
cd engine && cargo test -p nasrudin-embed index::tests::nearest_text 2>&1 | tail -5
```

Expected: 1 pass.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/embed/src/index.rs
git commit -m "$(cat <<'EOF'
feat(embed): EmbeddingIndex::nearest_text convenience

Compose embedder + nearest in one call. Integration test exercises
the real round-trip in a later task.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: `Builder` — write a fresh index

**Files:**
- Modify: `engine/crates/embed/src/builder.rs`

- [ ] **Step 1: Write the failing test**

Replace `engine/crates/embed/src/builder.rs` with:

```rust
//! Build a fresh `corpus.embed` + `corpus.embed.hnsw` from an
//! iterator of `(TheoremId, source_text)` pairs.

use anyhow::{Context, Result};
use instant_distance::Builder as HnswBuilder;
use nasrudin_core::TheoremId;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::format::{IndexHeader, EMBED_DIM, INDEX_VERSION};
use crate::index::{sidecar_path, CosinePoint};
use crate::model::Embedder;

pub struct IndexBuilder {
    rows: Vec<(TheoremId, Vec<f32>)>,
}

impl IndexBuilder {
    pub fn new() -> Self {
        Self { rows: Vec::new() }
    }

    /// Embed `texts` in batches and accumulate `(id, vector)` pairs.
    /// `batch_size` is forwarded to fastembed (recommended: 32 to 128
    /// depending on RAM budget).
    pub fn add_batch(
        &mut self,
        embedder: &Embedder,
        texts: Vec<(TheoremId, String)>,
        batch_size: usize,
    ) -> Result<()> {
        if texts.is_empty() {
            return Ok(());
        }
        for chunk in texts.chunks(batch_size.max(1)) {
            let ids: Vec<TheoremId> = chunk.iter().map(|(id, _)| *id).collect();
            let raw_texts: Vec<String> = chunk.iter().map(|(_, t)| t.clone()).collect();
            let vectors = embedder
                .embed_batch(raw_texts)
                .context("embed batch in builder")?;
            for (id, v) in ids.into_iter().zip(vectors.into_iter()) {
                if v.len() != EMBED_DIM as usize {
                    anyhow::bail!("model returned dim {} != expected {EMBED_DIM}", v.len());
                }
                self.rows.push((id, v));
            }
        }
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Persist `corpus.embed` + `corpus.embed.hnsw`. Existing files at
    /// these paths are overwritten atomically (write to .tmp then
    /// rename).
    pub fn save(&self, main_path: &Path) -> Result<()> {
        write_main(main_path, &self.rows)?;
        write_hnsw_sidecar(main_path, &self.rows)?;
        Ok(())
    }
}

impl Default for IndexBuilder {
    fn default() -> Self {
        Self::new()
    }
}

fn write_main(path: &Path, rows: &[(TheoremId, Vec<f32>)]) -> Result<()> {
    let tmp = with_tmp_suffix(path);
    {
        let f = File::create(&tmp).with_context(|| format!("create {tmp:?}"))?;
        let mut w = BufWriter::new(f);
        let header = IndexHeader {
            version: INDEX_VERSION,
            dim: EMBED_DIM,
            count: u32::try_from(rows.len()).context("count exceeds u32")?,
            built_at_millis: chrono::Utc::now().timestamp_millis(),
        };
        w.write_all(&header.encode())?;
        for (id, v) in rows {
            w.write_all(id)?;
            for f in v {
                w.write_all(&f.to_le_bytes())?;
            }
        }
        w.flush()?;
    }
    std::fs::rename(&tmp, path).context("rename tmp into place")?;
    Ok(())
}

fn write_hnsw_sidecar(main_path: &Path, rows: &[(TheoremId, Vec<f32>)]) -> Result<()> {
    let sidecar = sidecar_path(main_path);
    let tmp = with_tmp_suffix(&sidecar);
    let points: Vec<CosinePoint> = rows
        .iter()
        .map(|(_, v)| CosinePoint(v.clone()))
        .collect();
    let values: Vec<TheoremId> = rows.iter().map(|(id, _)| *id).collect();
    let hnsw = HnswBuilder::default().build(points, values);
    let bytes = bincode::serialize(&hnsw).context("serialise HNSW")?;
    std::fs::write(&tmp, &bytes).with_context(|| format!("write {tmp:?}"))?;
    std::fs::rename(&tmp, &sidecar).context("rename hnsw tmp into place")?;
    Ok(())
}

fn with_tmp_suffix(p: &Path) -> std::path::PathBuf {
    let mut s = p.as_os_str().to_owned();
    s.push(".tmp");
    std::path::PathBuf::from(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    fn synthetic_vec(seed: u8) -> Vec<f32> {
        let mut v = vec![0.0f32; EMBED_DIM as usize];
        // Place the seed in the first slot, then L2-normalise so the
        // cosine distance is well-defined.
        v[0] = (seed as f32) + 1.0;
        v[1] = ((seed as f32) + 1.0) * 0.5;
        let n: f32 = v.iter().map(|x| x * x).sum::<f32>().sqrt();
        for x in &mut v {
            *x /= n;
        }
        v
    }

    #[test]
    fn save_and_reopen_round_trips_record_count() {
        let dir = tempdir().unwrap();
        let p = dir.path().join("corpus.embed");
        let rows: Vec<(TheoremId, Vec<f32>)> = (0u8..3)
            .map(|i| ([i, 0, 0, 0, 0, 0, 0, 0], synthetic_vec(i)))
            .collect();
        let mut b = IndexBuilder::new();
        b.rows = rows.clone();
        b.save(&p).unwrap();
        let idx = crate::index::EmbeddingIndex::open(&p).unwrap();
        assert_eq!(idx.len(), 3);
    }

    #[test]
    fn save_creates_both_main_and_sidecar() {
        let dir = tempdir().unwrap();
        let p = dir.path().join("corpus.embed");
        let rows: Vec<(TheoremId, Vec<f32>)> =
            vec![([1, 0, 0, 0, 0, 0, 0, 0], synthetic_vec(0))];
        let mut b = IndexBuilder::new();
        b.rows = rows;
        b.save(&p).unwrap();
        assert!(p.exists());
        assert!(crate::index::sidecar_path(&p).exists());
    }
}
```

- [ ] **Step 2: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-embed builder:: 2>&1 | tail -10
```

Expected: 2 pass.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/embed/src/builder.rs
git commit -m "$(cat <<'EOF'
feat(embed): IndexBuilder writes corpus.embed + sidecar HNSW

add_batch streams through fastembed; save writes both files
atomically (tmp + rename). Round-trip tested with synthetic vectors.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8: End-to-end semantic test (gated #[ignore])

**Files:**
- Create: `engine/crates/embed/tests/integration_semantic.rs`

- [ ] **Step 1: Write the test**

Create `engine/crates/embed/tests/integration_semantic.rs`:

```rust
//! End-to-end: build an index from 3 synthetic theorems with
//! different topics, embed a "energy" hunch, confirm the
//! energy-themed theorem is closer than the fluid-themed one.
//!
//! `#[ignore]` because the model download is ~130 MB. Run with
//! `cargo test -p nasrudin-embed --test integration_semantic -- --ignored`.

use nasrudin_core::TheoremId;
use nasrudin_embed::{builder::IndexBuilder, model::Embedder, EmbeddingIndex};
use tempfile::tempdir;

fn id(n: u8) -> TheoremId {
    [n, 0, 0, 0, 0, 0, 0, 0]
}

#[test]
#[ignore]
fn energy_hunch_picks_energy_theorem_over_fluid() {
    if std::env::var("NASRUDIN_SKIP_EMBED_DOWNLOAD").is_ok() {
        return;
    }
    let embedder = Embedder::new().expect("model init");
    let texts = vec![
        (
            id(1),
            "rest energy equals mass times speed of light squared (E = m c^2)".to_string(),
        ),
        (
            id(2),
            "kinetic energy equals one half mass velocity squared".to_string(),
        ),
        (
            id(3),
            "Bernoulli's principle relates pressure and fluid velocity".to_string(),
        ),
    ];
    let mut b = IndexBuilder::new();
    b.add_batch(&embedder, texts, 8).unwrap();
    let dir = tempdir().unwrap();
    let p = dir.path().join("corpus.embed");
    b.save(&p).unwrap();

    let index = EmbeddingIndex::open(&p).unwrap();
    let hits = index
        .nearest_text(&embedder, "How does energy relate to mass?", 3)
        .unwrap();
    assert!(hits.len() >= 1);
    // The first hit must be one of the two energy theorems, NOT the
    // fluid one.
    assert!(
        hits[0].theorem_id == id(1) || hits[0].theorem_id == id(2),
        "expected energy theorem, got {:?}",
        hits[0].theorem_id
    );
    // The fluid theorem must rank below the others.
    if let Some(fluid_pos) = hits.iter().position(|h| h.theorem_id == id(3)) {
        assert!(fluid_pos > 0, "fluid theorem should not rank first");
    }
}

#[test]
#[ignore]
fn deterministic_index_built_twice_returns_same_top_hit() {
    if std::env::var("NASRUDIN_SKIP_EMBED_DOWNLOAD").is_ok() {
        return;
    }
    let embedder = Embedder::new().expect("model init");
    let texts = vec![
        (id(1), "Lorentz transformations".to_string()),
        (id(2), "Maxwell equations in vacuum".to_string()),
    ];
    let dir = tempdir().unwrap();
    let p1 = dir.path().join("a.embed");
    let p2 = dir.path().join("b.embed");

    let mut b1 = IndexBuilder::new();
    b1.add_batch(&embedder, texts.clone(), 8).unwrap();
    b1.save(&p1).unwrap();
    let mut b2 = IndexBuilder::new();
    b2.add_batch(&embedder, texts, 8).unwrap();
    b2.save(&p2).unwrap();

    let i1 = EmbeddingIndex::open(&p1).unwrap();
    let i2 = EmbeddingIndex::open(&p2).unwrap();
    let q = embedder.embed_one("electromagnetic waves").unwrap();
    let h1 = i1.nearest(&q, 1);
    let h2 = i2.nearest(&q, 1);
    assert_eq!(h1[0].theorem_id, h2[0].theorem_id);
}
```

- [ ] **Step 2: Confirm test compiles (it's #[ignore])**

```bash
cd engine && cargo test -p nasrudin-embed --test integration_semantic -- --list 2>&1 | tail -10
```

Expected: lists both ignored tests.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/embed/tests/integration_semantic.rs
git commit -m "$(cat <<'EOF'
test(embed): semantic + determinism integration tests (ignored)

Ignored by default because BGE model download is ~130 MB. Run with
--ignored when verifying a release.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: `nasrudin-embed-build` CLI binary

**Files:**
- Create: `engine/crates/api/src/bin/embed_build.rs`
- Modify: `engine/crates/api/Cargo.toml`

- [ ] **Step 1: Add bin target**

In `engine/crates/api/Cargo.toml`, add to the `[dependencies]`:

```toml
nasrudin-embed = { path = "../embed" }
```

Add a new `[[bin]]` section:

```toml
[[bin]]
name = "embed_build"
path = "src/bin/embed_build.rs"
```

- [ ] **Step 2: Write the binary**

Create `engine/crates/api/src/bin/embed_build.rs`:

```rust
//! `nasrudin-embed-build`: scan the engine's RocksDB, embed every
//! verified theorem's `canonical + latex + domain`, and write
//! `corpus.embed` + `corpus.embed.hnsw` to the configured output dir.
//!
//! Usage:
//!
//! ```bash
//! NASRUDIN_EMBED_OUT=$HOME/.nasrudin/embed/corpus.embed \
//!   ROCKS_DB_PATH=./data/theorems.db \
//!   cargo run --release --bin embed_build
//! ```

use std::path::PathBuf;

use anyhow::{Context, Result};
use nasrudin_core::{Theorem, VerificationStatus};
use nasrudin_embed::{builder::IndexBuilder, model::Embedder};
use nasrudin_rocks::TheoremDb;

fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let db_path = std::env::var("ROCKS_DB_PATH").unwrap_or_else(|_| "./data/theorems.db".into());
    let out_path: PathBuf = std::env::var("NASRUDIN_EMBED_OUT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
            PathBuf::from(home).join(".nasrudin/embed/corpus.embed")
        });
    let batch_size: usize = std::env::var("NASRUDIN_EMBED_BATCH")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(64);

    if let Some(parent) = out_path.parent() {
        std::fs::create_dir_all(parent).with_context(|| format!("mkdir -p {parent:?}"))?;
    }

    let db = TheoremDb::new(&db_path).with_context(|| format!("open RocksDB at {db_path}"))?;
    tracing::info!("scanning theorems from {db_path}");
    let all = db.list_theorems()?;

    let verified: Vec<&Theorem> = all
        .iter()
        .filter(|t| matches!(t.verified, VerificationStatus::Verified { .. }))
        .collect();
    tracing::info!("found {} verified theorems (of {} total)", verified.len(), all.len());

    let texts: Vec<(nasrudin_core::TheoremId, String)> = verified
        .iter()
        .map(|t| {
            let body = format!(
                "{}\n{}\n{}",
                t.canonical,
                t.latex,
                domain_string(&t.domain)
            );
            (t.id, body)
        })
        .collect();

    let embedder = Embedder::new().context("init Embedder")?;
    let mut builder = IndexBuilder::new();
    builder
        .add_batch(&embedder, texts, batch_size)
        .context("embed corpus")?;
    builder.save(&out_path).context("save index")?;

    tracing::info!("wrote {} records to {out_path:?}", builder.len());
    Ok(())
}

fn domain_string(d: &nasrudin_core::Domain) -> String {
    format!("{:?}", d)
}
```

- [ ] **Step 3: Confirm compiles**

```bash
cd engine && cargo check --bin embed_build 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/Cargo.toml engine/crates/api/src/bin/embed_build.rs
git commit -m "$(cat <<'EOF'
feat(embed): nasrudin-embed-build CLI

Scans TheoremDb for Verified rows, embeds canonical+latex+domain,
writes corpus.embed + sidecar to NASRUDIN_EMBED_OUT.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 10: API routes `/api/embed/checksum` + `/api/embed/index.bin`

**Files:**
- Create: `engine/crates/api/src/handlers/embed.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs`
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/api/src/state.rs`

- [ ] **Step 1: Add `embed` field to AppState**

Edit `engine/crates/api/src/state.rs`. Add to the imports near the top:

```rust
use nasrudin_embed::EmbeddingIndex;
```

Add to `AppState` (just before the closing `}`):

```rust
    /// Embedding index for the verified-theorem corpus. None when
    /// NASRUDIN_EMBED_ENABLED is unset or the file isn't on disk yet.
    pub embed: Option<Arc<EmbeddingIndex>>,
    /// Filesystem path where the index lives (used by the
    /// /api/embed/index.bin handler to stream the file).
    pub embed_path: Option<std::path::PathBuf>,
```

- [ ] **Step 2: Write the handlers**

Create `engine/crates/api/src/handlers/embed.rs`:

```rust
//! Read-only access to the corpus embedding index.

use std::sync::Arc;

use axum::{
    body::Body,
    extract::State,
    http::{header, StatusCode},
    response::{IntoResponse, Response},
    Json,
};
use serde::Serialize;
use tokio_util::io::ReaderStream;

use crate::state::AppState;

#[derive(Serialize)]
pub struct ChecksumResponse {
    pub hex: String,
    pub bytes: u64,
    pub built_at_millis: i64,
    pub count: u32,
}

/// `GET /api/embed/checksum` — cheap call workers make every heartbeat.
pub async fn checksum(State(state): State<Arc<AppState>>) -> Response {
    let path = match &state.embed_path {
        Some(p) => p.clone(),
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({"error": "embed_disabled"})),
            )
                .into_response();
        }
    };
    let cs = match nasrudin_embed::compute_index_checksum(&path) {
        Ok(c) => c,
        Err(e) => {
            tracing::warn!("checksum compute failed: {e}");
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({"error": "checksum_failed", "detail": e.to_string()})),
            )
                .into_response();
        }
    };
    let header = state.embed.as_ref().map(|i| i.header()).unwrap_or(
        nasrudin_embed::IndexHeader {
            version: nasrudin_embed::INDEX_VERSION,
            dim: nasrudin_embed::EMBED_DIM,
            count: 0,
            built_at_millis: 0,
        },
    );
    Json(ChecksumResponse {
        hex: cs.hex,
        bytes: cs.bytes,
        built_at_millis: header.built_at_millis,
        count: header.count,
    })
    .into_response()
}

/// `GET /api/embed/index.bin` — streams the raw `corpus.embed` body.
/// The HNSW sidecar is rebuilt locally by the worker on download
/// (faster than streaming a serialised HNSW which is much larger).
pub async fn index_bin(State(state): State<Arc<AppState>>) -> Response {
    let path = match &state.embed_path {
        Some(p) => p.clone(),
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({"error": "embed_disabled"})),
            )
                .into_response();
        }
    };
    let file = match tokio::fs::File::open(&path).await {
        Ok(f) => f,
        Err(e) => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({"error": "index_missing", "detail": e.to_string()})),
            )
                .into_response();
        }
    };
    let stream = ReaderStream::new(file);
    let body = Body::from_stream(stream);
    let cs = nasrudin_embed::compute_index_checksum(&path).ok();
    let mut resp = Response::builder()
        .header(header::CONTENT_TYPE, "application/octet-stream");
    if let Some(c) = &cs {
        resp = resp.header("Sha-Embed", c.hex.as_str());
    }
    resp.body(body).unwrap_or_else(|_| {
        (StatusCode::INTERNAL_SERVER_ERROR, Body::empty()).into_response()
    })
}
```

Add `tokio-util` to `engine/crates/api/Cargo.toml` if not already there:

```toml
tokio-util = { version = "0.7", features = ["io"] }
```

- [ ] **Step 3: Register the module**

Edit `engine/crates/api/src/handlers/mod.rs`. Add:

```rust
pub mod embed;
```

- [ ] **Step 4: Wire the routes**

Edit `engine/crates/api/src/main.rs`. Find the route table (search for `.route("/api/domains"` to anchor on a known route line). Add two new lines in the same router builder:

```rust
        .route("/api/embed/checksum", get(physics_api::handlers::embed::checksum))
        .route("/api/embed/index.bin", get(physics_api::handlers::embed::index_bin))
```

- [ ] **Step 5: Build the index handle at boot**

In `main.rs`, after the `cache_ctx` block (added in Phase A.5), add:

```rust
    let embed_enabled = std::env::var("NASRUDIN_EMBED_ENABLED")
        .map(|v| matches!(v.trim().to_lowercase().as_str(), "1" | "true" | "yes"))
        .unwrap_or(false);
    let embed_path: Option<std::path::PathBuf> = if embed_enabled {
        Some(
            std::env::var("NASRUDIN_EMBED_OUT")
                .map(std::path::PathBuf::from)
                .unwrap_or_else(|_| {
                    let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
                    std::path::PathBuf::from(home).join(".nasrudin/embed/corpus.embed")
                }),
        )
    } else {
        None
    };
    let embed = embed_path.as_ref().and_then(|p| {
        if !p.exists() {
            tracing::info!("embed: index not yet built at {p:?}; serving without");
            return None;
        }
        match nasrudin_embed::EmbeddingIndex::open(p) {
            Ok(i) => Some(Arc::new(i)),
            Err(e) => {
                tracing::warn!("embed: open {p:?} failed: {e}");
                None
            }
        }
    });
```

Then in the `AppState` literal, add:

```rust
        embed,
        embed_path,
```

- [ ] **Step 6: Confirm compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/handlers/embed.rs engine/crates/api/src/handlers/mod.rs engine/crates/api/src/main.rs engine/crates/api/src/state.rs engine/crates/api/Cargo.toml
git commit -m "$(cat <<'EOF'
feat(embed): /api/embed/checksum + /api/embed/index.bin endpoints

Workers poll checksum on heartbeat; mismatch triggers index.bin
download. Index served as application/octet-stream with Sha-Embed
header (BLAKE3 hex of file body).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11: Background rebuild scheduler

**Files:**
- Create: `engine/crates/api/src/embed_cron.rs`
- Modify: `engine/crates/api/src/lib.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Write the scheduler module**

Create `engine/crates/api/src/embed_cron.rs`:

```rust
//! Background rebuild scheduler for the embedding index.
//!
//! Two trigger conditions:
//! - Wall-clock cron: rebuild every 24h.
//! - Theorem-count threshold: rebuild after every 1000 newly-verified
//!   theorems since the last build.
//!
//! Implementation: spawn a tokio task that polls every 60 seconds.
//! On either trigger, fork to `embed_build` (or invoke the same
//! pipeline in-process — we choose subprocess so a long build
//! doesn't block other server work).

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

        let time_trigger =
            now_ms.saturating_sub(last) >= REBUILD_AFTER.as_millis() as u64;
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
```

- [ ] **Step 2: Register the module**

Edit `engine/crates/api/src/lib.rs`. Add:

```rust
pub mod embed_cron;
```

- [ ] **Step 3: Spawn the cron in main.rs**

Edit `engine/crates/api/src/main.rs`. After the `embed` build block (Task 10 Step 5), add:

```rust
    if embed_enabled {
        if let Some(p) = embed_path.as_ref() {
            let cron =
                Arc::new(physics_api::embed_cron::EmbedCron::new(Arc::clone(&db), p.clone()));
            tokio::spawn(Arc::clone(&cron).run());
            tracing::info!("embed_cron spawned (out_path = {p:?})");
        }
    }
```

- [ ] **Step 4: Run unit tests**

```bash
cd engine && cargo test -p physics-api embed_cron:: 2>&1 | tail -5
```

Expected: 2 pass.

- [ ] **Step 5: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/embed_cron.rs engine/crates/api/src/lib.rs engine/crates/api/src/main.rs
git commit -m "$(cat <<'EOF'
feat(embed): nightly + count-threshold rebuild scheduler

Polls every 60s; triggers rebuild on either 24h elapsed or 1000 new
verifications since last build. Rebuilds via subprocess (embed_build
bin) so a long build doesn't block other server work.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12: Worker-side auto-pull on heartbeat

**Files:**
- Modify: `engine/crates/ga/src/bin/discover_emc2.rs` (worker entry)
- Modify: `engine/crates/ga/Cargo.toml` (depend on `nasrudin-embed`)

- [ ] **Step 1: Add dep**

In `engine/crates/ga/Cargo.toml`, add to `[dependencies]`:

```toml
nasrudin-embed = { path = "../embed" }
reqwest = { workspace = true }
```

(Confirm `reqwest` is in workspace deps; if not, add `reqwest = { version = "0.12", default-features = false, features = ["json", "rustls-tls", "stream"] }` to `engine/Cargo.toml [workspace.dependencies]`.)

- [ ] **Step 2: Add the auto-pull helper**

Open `engine/crates/ga/src/bin/discover_emc2.rs`. Find a quiet section near the top (just below `use` statements) and add:

```rust
mod embed_autopull {
    use anyhow::Result;
    use std::path::PathBuf;

    pub struct AutoPull {
        pub api_url: String,
        pub local_path: PathBuf,
    }

    impl AutoPull {
        pub async fn maybe_refresh(&self) -> Result<bool> {
            let cs_url = format!("{}/api/embed/checksum", self.api_url.trim_end_matches('/'));
            let client = reqwest::Client::new();
            let resp = match client.get(&cs_url).send().await {
                Ok(r) => r,
                Err(e) => {
                    tracing::debug!("embed checksum fetch failed: {e}");
                    return Ok(false);
                }
            };
            if !resp.status().is_success() {
                return Ok(false);
            }
            #[derive(serde::Deserialize)]
            struct CsBody {
                hex: String,
            }
            let cs: CsBody = match resp.json().await {
                Ok(c) => c,
                Err(e) => {
                    tracing::debug!("embed checksum body parse failed: {e}");
                    return Ok(false);
                }
            };
            let local_hex = if self.local_path.exists() {
                nasrudin_embed::compute_index_checksum(&self.local_path)
                    .ok()
                    .map(|c| c.hex)
            } else {
                None
            };
            if local_hex.as_deref() == Some(cs.hex.as_str()) {
                return Ok(false);
            }
            tracing::info!("embed: local checksum mismatch, downloading new index");
            let bin_url = format!("{}/api/embed/index.bin", self.api_url.trim_end_matches('/'));
            let bytes = client.get(&bin_url).send().await?.bytes().await?;
            if let Some(parent) = self.local_path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            let tmp = with_tmp_suffix(&self.local_path);
            std::fs::write(&tmp, &bytes)?;
            std::fs::rename(&tmp, &self.local_path)?;
            tracing::info!("embed: wrote {} bytes to {:?}", bytes.len(), self.local_path);

            // Rebuild HNSW sidecar locally by re-reading the index and
            // re-constructing the HNSW from its records. Faster than
            // streaming a serialised HNSW (which is much larger than
            // the flat record body).
            rebuild_sidecar(&self.local_path)?;
            Ok(true)
        }
    }

    fn with_tmp_suffix(p: &PathBuf) -> PathBuf {
        let mut s = p.as_os_str().to_owned();
        s.push(".tmp");
        PathBuf::from(s)
    }

    fn rebuild_sidecar(main: &PathBuf) -> Result<()> {
        use instant_distance::Builder as HnswBuilder;
        use nasrudin_core::TheoremId;
        use nasrudin_embed::{EmbeddingIndex, IndexHeader, EMBED_DIM, INDEX_VERSION};

        let bytes = std::fs::read(main)?;
        let header_bytes = &bytes[..nasrudin_embed::format::HEADER_SIZE];
        let header = IndexHeader::decode(header_bytes)?;
        let body = &bytes[nasrudin_embed::format::HEADER_SIZE..];
        let mut points: Vec<nasrudin_embed::index::CosinePoint> = Vec::with_capacity(header.count as usize);
        let mut values: Vec<TheoremId> = Vec::with_capacity(header.count as usize);
        let rec_size = nasrudin_embed::format::RECORD_SIZE;
        for i in 0..(header.count as usize) {
            let off = i * rec_size;
            let mut id = [0u8; 8];
            id.copy_from_slice(&body[off..off + 8]);
            let mut v = vec![0f32; EMBED_DIM as usize];
            for j in 0..(EMBED_DIM as usize) {
                let s = off + 8 + j * 4;
                v[j] = f32::from_le_bytes([body[s], body[s + 1], body[s + 2], body[s + 3]]);
            }
            points.push(nasrudin_embed::index::CosinePoint(v));
            values.push(id);
        }
        let hnsw = HnswBuilder::default().build(points, values);
        let bytes = bincode::serialize(&hnsw)?;
        let sidecar = nasrudin_embed::index::sidecar_path(main);
        std::fs::write(&sidecar, &bytes)?;
        let _ = INDEX_VERSION; // silence unused warning if early return
        Ok(())
    }
}
```

(This requires that `nasrudin_embed::format::HEADER_SIZE`, `RECORD_SIZE`, and `nasrudin_embed::index::CosinePoint` all be `pub`. They were defined `pub` in earlier tasks; if any aren't, add `pub` and re-test.)

- [ ] **Step 3: Wire the auto-pull into the worker's heartbeat loop**

In the same file, find the heartbeat / chunk-loop section (search for `chunk_i` and `chunks` to anchor — already present in the existing worker). Add at the start of each chunk iteration:

```rust
        // Periodic embed-index refresh. Cheap when index is current.
        if let Ok(autopull) = std::env::var("NASRUDIN_EMBED_AUTOPULL") {
            if matches!(autopull.trim().to_lowercase().as_str(), "1" | "true" | "yes") {
                let api = std::env::var("NASRUDIN_API_URL")
                    .unwrap_or_else(|_| "http://localhost:8080".into());
                let path: std::path::PathBuf = std::env::var("NASRUDIN_EMBED_OUT")
                    .map(std::path::PathBuf::from)
                    .unwrap_or_else(|_| {
                        let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
                        std::path::PathBuf::from(home).join(".nasrudin/embed/corpus.embed")
                    });
                let pull = embed_autopull::AutoPull {
                    api_url: api,
                    local_path: path,
                };
                if let Err(e) = pull.maybe_refresh().await {
                    tracing::debug!("embed autopull skipped: {e}");
                }
            }
        }
```

- [ ] **Step 4: Confirm compiles**

```bash
cd engine && cargo check -p nasrudin-ga 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/ga/Cargo.toml engine/crates/ga/src/bin/discover_emc2.rs engine/Cargo.toml
git commit -m "$(cat <<'EOF'
feat(embed): worker auto-pulls /api/embed/index.bin on heartbeat

Gated on NASRUDIN_EMBED_AUTOPULL=1. Downloads only when the server's
checksum differs from the local file. HNSW sidecar rebuilt locally
after each pull (cheaper than streaming a serialised HNSW).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 13: Round-trip integration test

**Files:**
- Create: `engine/crates/embed/tests/integration_round_trip.rs`

- [ ] **Step 1: Write the test**

Create `engine/crates/embed/tests/integration_round_trip.rs`:

```rust
//! Build → save → checksum → reopen → nearest. No model download
//! (synthetic 384-dim vectors), so this can run in CI.

use nasrudin_core::TheoremId;
use nasrudin_embed::{builder::IndexBuilder, compute_index_checksum, EmbeddingIndex, EMBED_DIM};
use tempfile::tempdir;

fn id(n: u8) -> TheoremId {
    [n, 0, 0, 0, 0, 0, 0, 0]
}

fn unit_vec(seed: u8) -> Vec<f32> {
    let mut v = vec![0.0f32; EMBED_DIM as usize];
    v[0] = 1.0 - 0.01 * (seed as f32);
    v[1] = 0.01 * (seed as f32);
    let n: f32 = v.iter().map(|x| x * x).sum::<f32>().sqrt();
    for x in &mut v {
        *x /= n;
    }
    v
}

#[test]
fn round_trip_via_builder_and_open() {
    let dir = tempdir().unwrap();
    let p = dir.path().join("corpus.embed");
    let rows: Vec<(TheoremId, Vec<f32>)> = (0u8..5).map(|i| (id(i), unit_vec(i))).collect();
    let mut b = IndexBuilder::new();
    b.rows = rows.clone();
    b.save(&p).unwrap();

    // Checksum is stable across reads.
    let cs1 = compute_index_checksum(&p).unwrap();
    let cs2 = compute_index_checksum(&p).unwrap();
    assert_eq!(cs1, cs2);

    let idx = EmbeddingIndex::open(&p).unwrap();
    assert_eq!(idx.len(), 5);

    // Querying with the seed=0 vector returns id=0 first.
    let hits = idx.nearest(&unit_vec(0), 5);
    assert!(!hits.is_empty());
    assert_eq!(hits[0].theorem_id, id(0));
}

#[test]
fn open_rejects_truncated_file() {
    let dir = tempdir().unwrap();
    let p = dir.path().join("corpus.embed");
    std::fs::write(&p, vec![0u8; 16]).unwrap(); // way less than HEADER_SIZE
    assert!(EmbeddingIndex::open(&p).is_err());
}

#[test]
fn nearest_zero_k_returns_empty() {
    let dir = tempdir().unwrap();
    let p = dir.path().join("corpus.embed");
    let rows: Vec<(TheoremId, Vec<f32>)> = vec![(id(1), unit_vec(0))];
    let mut b = IndexBuilder::new();
    b.rows = rows;
    b.save(&p).unwrap();
    let idx = EmbeddingIndex::open(&p).unwrap();
    assert!(idx.nearest(&unit_vec(0), 0).is_empty());
}
```

For this test to compile, `IndexBuilder.rows` must be `pub` (so the test can populate it directly without going through the embedder). Edit `engine/crates/embed/src/builder.rs` and change:

```rust
    rows: Vec<(TheoremId, Vec<f32>)>,
```

to:

```rust
    pub rows: Vec<(TheoremId, Vec<f32>)>,
```

- [ ] **Step 2: Run the test**

```bash
cd engine && cargo test -p nasrudin-embed --test integration_round_trip 2>&1 | tail -10
```

Expected: 3 pass.

- [ ] **Step 3: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/embed/tests/integration_round_trip.rs engine/crates/embed/src/builder.rs
git commit -m "$(cat <<'EOF'
test(embed): build → save → checksum → open → nearest round-trip

Uses synthetic 384-dim vectors so CI runs without the BGE download.
Made IndexBuilder.rows pub so tests can populate it directly.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 14: Operator docs

**Files:**
- Create: `engine/crates/embed/EMBED_LAYER.md`

- [ ] **Step 1: Write the doc**

Create `engine/crates/embed/EMBED_LAYER.md`:

```markdown
# Embedding Layer (Phase B)

`nasrudin-embed` is the local-CPU embedding store over the verified-
theorem corpus. It powers two consumers:

- The **conjecture LLM router** (Phase D) — calls
  `EmbeddingIndex::nearest_text(hunch, 10)` to retrieve the corpus
  matches that get fed to the LLM as part of the prompt.
- The **GA tactic-priors fallback** (Phase A.5+) — when an exact
  goal-skeleton hash misses in `tactic_priors`, the system looks up
  the nearest goal in the embedding space and tries its tactic chains.

## Pieces

| Component | Responsibility |
|---|---|
| `Embedder` (`model.rs`) | fastembed wrapper. Default model: BAAI/bge-small-en-v1.5, 384 dims. |
| `IndexBuilder` (`builder.rs`) | Streams `(TheoremId, text)` through the embedder; writes `corpus.embed` + sidecar HNSW. |
| `EmbeddingIndex` (`index.rs`) | mmap of `corpus.embed`; loads HNSW sidecar; `nearest(...)` / `nearest_text(...)`. |
| `compute_index_checksum` (`checksum.rs`) | BLAKE3 over the index file body for distribution. |

## Wire format

`corpus.embed` is a 64-byte header (magic `NEMB`, version, dim,
count, build timestamp) followed by `count` records of:

```
[u8; 8]      TheoremId
[f32; 384]   little-endian vector
```

Sidecar: `corpus.embed.hnsw` is a bincode-serialised
`instant_distance::HnswMap<CosinePoint, TheoremId>`.

## Building the index

The CLI `embed_build` (in `physics-api` crate, binary target) scans
`TheoremDb` for verified theorems and emits the index files:

```bash
NASRUDIN_EMBED_OUT=$HOME/.nasrudin/embed/corpus.embed \
  ROCKS_DB_PATH=./data/theorems.db \
  cargo run --release --bin embed_build
```

The first run downloads the BGE model (~130 MB) into
`~/.cache/fastembed/`. Subsequent runs reuse the cached model.

## Server-side automation

When `NASRUDIN_EMBED_ENABLED=1` is set on the API server, the boot
sequence:

1. Opens the existing `corpus.embed` if present (else logs and
   continues without an index — `/api/embed/checksum` returns 404).
2. Spawns `EmbedCron` which polls every 60 s and triggers a rebuild
   when either:
   - 24 h elapsed since last build, OR
   - 1000 new verifications accumulated since the last build.
3. Rebuilds happen via subprocess (`embed_build`) so a long build
   doesn't block other server work.

## Worker-side auto-pull

When `NASRUDIN_EMBED_AUTOPULL=1` is set on a worker, each chunk
iteration polls `/api/embed/checksum` against the local file. Mismatch
triggers a download of `/api/embed/index.bin` (atomic write via
`.tmp` + rename) followed by local HNSW rebuild.

## Disabling

Unset `NASRUDIN_EMBED_ENABLED` on the server (no cron, no endpoints
registered with content) and `NASRUDIN_EMBED_AUTOPULL` on workers
(no polling). Disabling is a no-op for everything else: GA, ingest,
verification all keep working.

## Tests

CI-safe tests use synthetic 384-dim vectors (no model download).
Heavy tests are gated with `#[ignore]` and run via:

```bash
cargo test -p nasrudin-embed -- --ignored
```

Set `NASRUDIN_SKIP_EMBED_DOWNLOAD=1` in environments where the BGE
download is undesirable.
```

- [ ] **Step 2: Commit**

```bash
git add engine/crates/embed/EMBED_LAYER.md
git commit -m "$(cat <<'EOF'
docs(embed): operator docs for phase B

Layout, build invocation, server cron, worker auto-pull, disable
recipe, test gating.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Closing checklist

After all 14 tasks land:

- `cargo check --workspace` exits 0.
- `cargo test --workspace` passes (CI-safe tests; `#[ignore]`d ones gated on the model download).
- `NASRUDIN_EMBED_ENABLED=1` on the server boots with the cron task spawned.
- `cargo run --release --bin embed_build` produces a non-empty `corpus.embed` + `corpus.embed.hnsw`.
- `curl -i $API/api/embed/checksum` returns JSON with `hex`, `bytes`, `built_at_millis`, `count`.
- `curl -o /tmp/idx.bin $API/api/embed/index.bin` downloads bytes whose BLAKE3 matches the checksum endpoint.
- `NASRUDIN_EMBED_AUTOPULL=1` on a worker pulls `/api/embed/index.bin` on first heartbeat after the server publishes a new index.
- `EmbeddingIndex::nearest_text(embedder, "energy", 5)` returns 5 hits sorted by cosine distance.

Phase B is done; Phase C (LLM crate) can now build on the assumption that "embedding nearest-neighbour works end-to-end".
