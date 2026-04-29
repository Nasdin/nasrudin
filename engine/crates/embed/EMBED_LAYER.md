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
`.tmp` + rename) followed by local HNSW rebuild from the records.

## Disabling

Unset `NASRUDIN_EMBED_ENABLED` on the server (no cron, no useful
data on the endpoints) and `NASRUDIN_EMBED_AUTOPULL` on workers
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
