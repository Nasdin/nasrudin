# LLM-Guided Search — Phase A.5 — Cache Wiring Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Wire the three Phase A caches (attempts, tactic priors, persistent Lean) into the production hot paths so flipping the env flags actually changes behaviour. Resolve the five Phase-A.5-prep items from the cross-cutting review.

**Architecture:** Add the missing `axiom_set_hash` helper in `nasrudin-core`, add `on_existing_db` constructors so both RocksDB caches can share the engine's main `TheoremDb`, refactor `verify_with_cache`'s 8-arg signature into a borrowed context struct, drain pending oneshots when the persistent elaborator emits `Fatal`, then thread `(AttemptsCache, TacticPriorsCache, CacheStats, lean_version, worker_id, axiom_set_hash)` through the two production verification paths (sync `verify_chain` for the GA, async `LakeBuilder::verify` for the reverify queue) and add `record_success` callsites on verifier success. After this lands, `NASRUDIN_CACHE_ATTEMPTS=1`, `NASRUDIN_CACHE_TACTIC_PRIORS=1`, and `NASRUDIN_CACHE_PERSISTENT_LEAN=1` will visibly accelerate workers.

**Tech Stack:** Rust 1.95, RocksDB (already a workspace dep), `blake3` (workspace dep added in Phase A), `tokio` (existing), `chrono` (existing).

---

## Spec reference

Implements §3.4 ("Cache layer integration plan") of `docs/superpowers/specs/2026-04-28-llm-guided-search-design.md` plus the integration items deferred from Phase A's cross-cutting review:

1. Missing `axiom_set_hash` helper in `nasrudin_core::axiom_set`.
2. `AttemptsCache::on_existing_db(db)` constructor (and same for `TacticPriorsCache`) so production reuses the engine's main RocksDB.
3. `verify_with_cache` 8-arg signature → `VerifyWithCacheCtx` struct.
4. PersistentElaborator `Fatal`-response path drains pending oneshots.
5. `record_success` has no production caller.

After A.5: Phase A flags can be flipped on a single worker and stats reported via `cargo run --bin cache_stats` will show real hit counts.

---

## File structure

**New files:**

| Path | Responsibility |
|---|---|
| `engine/crates/derive/tests/integration_cache_wiring.rs` | End-to-end: second `verify_chain` on identical input hits the attempts cache without invoking `lake build` |

**Modified files:**

| Path | Change |
|---|---|
| `engine/crates/core/src/axiom_set.rs` | Add `axiom_set_hash(ids: &BTreeSet<TheoremId>) -> [u8; 8]` (BLAKE3 prefix over sorted IDs) |
| `engine/crates/core/src/lib.rs` | Re-export `axiom_set::axiom_set_hash` |
| `engine/crates/rocks/src/attempts_cache.rs` | Refactor: `AttemptsCache` holds `Arc<DB>`; add `on_existing_db(db: Arc<DB>)`; existing `open(path)` keeps standalone-test path working |
| `engine/crates/rocks/src/tactic_priors.rs` | Same `on_existing_db(db: Arc<DB>)` constructor refactor |
| `engine/crates/rocks/src/lib.rs` | Add `TheoremDb::shared_db() -> Arc<DB>` accessor (or expose `db_arc()`); make `DB` field `Arc<DB>` internally |
| `engine/crates/derive/src/lean_verify.rs` | Replace 8-arg `verify_with_cache` with `verify_with_cache(ctx: &VerifyWithCacheCtx, lean_content: &str, module_path: &str)`; add `pub struct VerifyWithCacheCtx` carrying the borrowed cache + identity fields |
| `engine/crates/lean-bridge/src/persistent.rs` | On `Response::Fatal`, drain `inflight` and signal each pending oneshot with the fatal message before logging |
| `engine/crates/ga/src/chain_engine.rs` | Add optional `cache_ctx: Option<CacheBundle<'_>>` to `DiscoveryConfig`; pass through to `verify_chain` |
| `engine/crates/ga/src/chain_ga.rs` | `verify_chain` accepts `Option<CacheBundle<'_>>`; calls `verify_with_cache` when set, otherwise `verify_file`; on success, `record_success` against the goal skeleton |
| `engine/crates/ga/src/lib.rs` | New `pub struct CacheBundle<'a>` re-exported (carries `&AttemptsCache`, `&TacticPriorsCache`, `&CacheStats`, `lean_version: &str`, `worker_id: &str`) |
| `engine/crates/api/src/lake_builder.rs` | Add async `verify_with_cache(&self, ctx, lean_source, theorem_id_hex)` that wraps `verify` with the same lookup-or-compute-then-record_success flow |
| `engine/crates/api/src/state.rs` | Add `pub cache_ctx: Option<Arc<crate::cache::CacheCtx>>` field |
| `engine/crates/api/src/cache.rs` (new module) | Owns `pub struct CacheCtx { attempts, tactic_priors, stats, lean_version, worker_id }` constructed once at startup |
| `engine/crates/api/src/main.rs` | Build `CacheCtx` from `CacheConfig::from_env()` and the shared `TheoremDb` Arc; pass into `AppState`; pass into `ReverifyQueue` |
| `engine/crates/api/src/reverify.rs` | When `state.cache_ctx` is set, call `lake.verify_with_cache(...)` instead of `lake.verify(...)` |
| `engine/crates/derive/CACHE_LAYER.md` | New "Phase A.5 — wiring" section documenting how flags now thread through the GA + reverify paths, and the new `cache_stats` invocation pattern |

---

## Conventions for this plan

- Run `cargo check --workspace` from `engine/` after every task; expect exit 0 before committing.
- Run `cargo test --workspace` from `engine/` before committing any task that touches existing tests.
- All commits must end with a `Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>` trailer (the harness does NOT add it automatically); pass commit messages via HEREDOC.
- Commit message style: `feat(cache): …`, `fix(cache): …`, `refactor(cache): …`, `test(cache): …`.
- Every task ends with a working tree (`cargo check --workspace` clean). No "this will compile after Task N+1" tasks.
- Tests use `tempfile::tempdir()` for isolated RocksDB fixtures.
- For env-mutating tests, use `serial_test::serial` (already a dev-dep from Phase A).

---

## Task 1: `axiom_set_hash` helper in `nasrudin-core`

**Files:**
- Modify: `engine/crates/core/src/axiom_set.rs`
- Modify: `engine/crates/core/src/lib.rs`

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/core/src/axiom_set.rs` inside `#[cfg(test)] mod tests`:

```rust
    #[test]
    fn axiom_set_hash_is_deterministic() {
        let ids = BTreeSet::from([id(1), id(2), id(3)]);
        let h1 = axiom_set_hash(&ids);
        let h2 = axiom_set_hash(&ids);
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 8);
    }

    #[test]
    fn axiom_set_hash_order_independent() {
        // BTreeSet already orders; this confirms callers passing differently-
        // built sets with the same members still hash identically.
        let mut a = BTreeSet::new();
        a.insert(id(2));
        a.insert(id(1));
        a.insert(id(3));
        let mut b = BTreeSet::new();
        b.insert(id(3));
        b.insert(id(1));
        b.insert(id(2));
        assert_eq!(axiom_set_hash(&a), axiom_set_hash(&b));
    }

    #[test]
    fn axiom_set_hash_empty_set_distinct_from_single_element() {
        let empty = BTreeSet::new();
        let one = BTreeSet::from([id(1)]);
        assert_ne!(axiom_set_hash(&empty), axiom_set_hash(&one));
    }

    #[test]
    fn axiom_set_hash_different_members_diverge() {
        let a = BTreeSet::from([id(1), id(2)]);
        let b = BTreeSet::from([id(1), id(3)]);
        assert_ne!(axiom_set_hash(&a), axiom_set_hash(&b));
    }

    #[test]
    fn axiom_id_from_name_is_deterministic() {
        let a = axiom_id_from_name("rest_frame_psq_zero");
        let b = axiom_id_from_name("rest_frame_psq_zero");
        assert_eq!(a, b);
        assert_eq!(a.len(), 8);
    }

    #[test]
    fn axiom_id_from_name_diverges_for_different_names() {
        let a = axiom_id_from_name("rest_frame_psq_zero");
        let b = axiom_id_from_name("photon_dispersion");
        assert_ne!(a, b);
    }
```

- [ ] **Step 2: Run tests to verify failure**

```bash
cd engine && cargo test -p nasrudin-core axiom_set::tests::axiom_set_hash 2>&1 | tail -10
```

Expected: `cannot find function axiom_set_hash` compile error.

- [ ] **Step 3: Add `blake3` to nasrudin-core's deps**

In `engine/crates/core/Cargo.toml`, confirm under `[dependencies]`:

```toml
blake3 = { workspace = true }
```

(Already added in Phase A Task 2; if missing, add it.)

- [ ] **Step 4: Implement `axiom_set_hash` + `axiom_id_from_name`**

Append to `engine/crates/core/src/axiom_set.rs` above the `#[cfg(test)]` block:

```rust
/// 8-byte BLAKE3 prefix over the sorted axiom IDs in `set`.
///
/// Used as the second half of the 16-byte cache key for both the
/// `attempts` and `tactic_priors` column families. `BTreeSet` ordering
/// guarantees the hash is stable across calls regardless of insertion
/// order; calling with the same membership always yields the same prefix.
pub fn axiom_set_hash(set: &BTreeSet<TheoremId>) -> [u8; 8] {
    let mut hasher = blake3::Hasher::new();
    for id in set {
        hasher.update(id);
    }
    let full = hasher.finalize();
    let mut out = [0u8; 8];
    out.copy_from_slice(&full.as_bytes()[..8]);
    out
}

/// Synthetic 8-byte ID derived from a free-form axiom name.
///
/// `nasrudin_derive::AxiomStore` keys axioms by `String` name (no
/// `TheoremId` field on the `Axiom` struct). Cache code wants
/// `BTreeSet<TheoremId>` to feed into [`axiom_set_hash`], so this
/// helper provides a stable name-to-ID mapping. Same name always
/// yields the same 8 bytes; different names diverge with overwhelming
/// probability (BLAKE3, no truncation collisions in practice).
pub fn axiom_id_from_name(name: &str) -> TheoremId {
    let full = blake3::hash(name.as_bytes());
    let mut out = [0u8; 8];
    out.copy_from_slice(&full.as_bytes()[..8]);
    out
}
```

- [ ] **Step 5: Re-export from `nasrudin-core`**

Edit `engine/crates/core/src/lib.rs`. Find the line `pub use axiom_set::collect_axiom_ids;` and replace with:

```rust
pub use axiom_set::{axiom_id_from_name, axiom_set_hash, collect_axiom_ids};
```

- [ ] **Step 6: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-core axiom_set:: 2>&1 | tail -10
```

Expected: 4 new tests + existing 9 pass.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/core/src/axiom_set.rs engine/crates/core/src/lib.rs
git commit -m "$(cat <<'EOF'
feat(core): add axiom_set_hash for cache keys

8-byte BLAKE3 prefix over a sorted `BTreeSet<TheoremId>`. Forms the
right half of the 16-byte cache keys used by `attempts` and
`tactic_priors` column families.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: `AttemptsCache::on_existing_db` constructor

**Files:**
- Modify: `engine/crates/rocks/src/attempts_cache.rs`
- Modify: `engine/crates/rocks/src/lib.rs`

- [ ] **Step 1: Expose shared DB handle on `TheoremDb`**

In `engine/crates/rocks/src/lib.rs`, find:

```rust
pub struct TheoremDb {
    db: DB,
}
```

Replace with:

```rust
pub struct TheoremDb {
    db: std::sync::Arc<DB>,
}
```

Then find the `TheoremDb::new` constructor (around `pub fn new(path: &str) -> Result<Self> {` ending at `Ok(Self { db })`) and change the final line `Ok(Self { db })` to `Ok(Self { db: std::sync::Arc::new(db) })`.

Then add this method right after the closing `}` of the `new` function:

```rust
    /// Borrowed clone of the underlying RocksDB handle. Used by cache
    /// wrappers (`AttemptsCache::on_existing_db`, `TacticPriorsCache::on_existing_db`)
    /// to share the engine's main DB instance instead of opening a
    /// second standalone database.
    pub fn shared_db(&self) -> std::sync::Arc<DB> {
        std::sync::Arc::clone(&self.db)
    }
```

All existing internal uses of `self.db` continue to work unchanged because `Arc<DB>` derefs to `DB`.

- [ ] **Step 2: Verify existing callers still compile**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: `Finished` line, exit 0. (If a pre-existing borrow elsewhere in `lib.rs` complains about `&self.db` no longer being `&DB`, dereference explicitly with `&*self.db` at that line.)

- [ ] **Step 3: Write the failing test**

Append to `engine/crates/rocks/src/attempts_cache.rs` inside the `#[cfg(test)] mod tests` block:

```rust
    #[test]
    fn on_existing_db_shares_storage_with_main_db() {
        use crate::TheoremDb;
        let dir = tempdir().unwrap();
        let main = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
        let cache = AttemptsCache::on_existing_db(main.shared_db()).unwrap();
        let key = [7u8; 16];
        let record = AttemptRecord {
            outcome: AttemptOutcome::RejectedTimeout,
            lean_version: "4.27.0".into(),
            timestamp: Utc::now(),
            attempted_by: "shared".into(),
            elapsed_ms: 1,
        };
        cache.put(&key, &record).unwrap();
        // Reopen the cache against the same shared handle and confirm
        // it sees the previously-written row (i.e. the CF really is on
        // the main DB, not in a separate temp location).
        let cache2 = AttemptsCache::on_existing_db(main.shared_db()).unwrap();
        assert!(cache2.get(&key).unwrap().is_some());
    }
```

- [ ] **Step 4: Run tests, verify failure**

```bash
cd engine && cargo test -p nasrudin-rocks attempts_cache::tests::on_existing_db 2>&1 | tail -10
```

Expected: `no function or associated item named on_existing_db`.

- [ ] **Step 5: Refactor `AttemptsCache` to hold `Arc<DB>` and add `on_existing_db`**

In `engine/crates/rocks/src/attempts_cache.rs`, find:

```rust
pub struct AttemptsCache {
    db: DB,
}
```

Replace with:

```rust
pub struct AttemptsCache {
    db: std::sync::Arc<rocksdb::DB>,
}
```

In the existing `pub fn open(path: &str)` body, replace the final two lines:

```rust
        let db = DB::open_cf_descriptors(&opts, path, vec![cf])
            .context("open attempts cache db")?;
        Ok(Self { db })
```

with:

```rust
        let db = DB::open_cf_descriptors(&opts, path, vec![cf])
            .context("open attempts cache db")?;
        Ok(Self { db: std::sync::Arc::new(db) })
```

Then add immediately below the `open` function:

```rust
    /// Construct an `AttemptsCache` backed by an existing RocksDB
    /// instance — typically the engine's main `TheoremDb`. The caller
    /// must already have the `attempts` CF registered (Phase A Task 6
    /// added it to `ALL_CFS`); we just take a borrowed clone of the
    /// shared handle.
    pub fn on_existing_db(db: std::sync::Arc<rocksdb::DB>) -> Result<Self> {
        // Sanity-check that the CF is present on this DB. If not, the
        // caller wired a wrong DB instance and a quick error here is
        // friendlier than a NULL CF panic on first put.
        if db.cf_handle(CF_ATTEMPTS).is_none() {
            return Err(anyhow::anyhow!(
                "attempts CF missing on shared DB; did you open via TheoremDb::new?"
            ));
        }
        Ok(Self { db })
    }
```

- [ ] **Step 6: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-rocks attempts_cache:: 2>&1 | tail -10
```

Expected: All `attempts_cache::tests::*` pass (existing 7 + 1 new).

- [ ] **Step 7: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/rocks/src/lib.rs engine/crates/rocks/src/attempts_cache.rs
git commit -m "$(cat <<'EOF'
feat(cache): AttemptsCache::on_existing_db + TheoremDb::shared_db

Production callers wire AttemptsCache against the engine's main
TheoremDb instead of a standalone path. Standalone open(path) is
preserved for tests.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: `TacticPriorsCache::on_existing_db` constructor

**Files:**
- Modify: `engine/crates/rocks/src/tactic_priors.rs`

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/rocks/src/tactic_priors.rs` inside `#[cfg(test)] mod tests`:

```rust
    #[test]
    fn on_existing_db_shares_storage_with_main_db() {
        use crate::TheoremDb;
        let dir = tempdir().unwrap();
        let main = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
        let cache = TacticPriorsCache::on_existing_db(main.shared_db()).unwrap();
        let key = [0xb7; 16];
        cache.record_success(&key, "ring", 5).unwrap();
        let cache2 = TacticPriorsCache::on_existing_db(main.shared_db()).unwrap();
        let top = cache2.top(&key, 5).unwrap();
        assert_eq!(top.len(), 1);
        assert_eq!(top[0].tactic_chain, "ring");
        assert_eq!(top[0].hits, 1);
    }
```

- [ ] **Step 2: Run tests, verify failure**

```bash
cd engine && cargo test -p nasrudin-rocks tactic_priors::tests::on_existing_db 2>&1 | tail -10
```

Expected: `no function or associated item named on_existing_db`.

- [ ] **Step 3: Refactor `TacticPriorsCache` to hold `Arc<DB>` and add `on_existing_db`**

In `engine/crates/rocks/src/tactic_priors.rs`, find:

```rust
pub struct TacticPriorsCache {
    db: DB,
}
```

Replace with:

```rust
pub struct TacticPriorsCache {
    db: std::sync::Arc<rocksdb::DB>,
}
```

In the existing `pub fn open(path: &str)` body, replace the final two lines:

```rust
        let db = DB::open_cf_descriptors(&opts, path, vec![cf])
            .context("open tactic_priors db")?;
        Ok(Self { db })
```

with:

```rust
        let db = DB::open_cf_descriptors(&opts, path, vec![cf])
            .context("open tactic_priors db")?;
        Ok(Self { db: std::sync::Arc::new(db) })
```

Then add immediately below the `open` function:

```rust
    /// Construct a `TacticPriorsCache` backed by an existing RocksDB
    /// instance — typically the engine's main `TheoremDb`. The caller
    /// must already have the `tactic_priors` CF registered (Phase A
    /// Task 6 added it to `ALL_CFS`); we just take a borrowed clone of
    /// the shared handle.
    pub fn on_existing_db(db: std::sync::Arc<rocksdb::DB>) -> Result<Self> {
        if db.cf_handle(CF_TACTIC_PRIORS).is_none() {
            return Err(anyhow::anyhow!(
                "tactic_priors CF missing on shared DB; did you open via TheoremDb::new?"
            ));
        }
        Ok(Self { db })
    }
```

- [ ] **Step 4: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-rocks tactic_priors:: 2>&1 | tail -10
```

Expected: 7 tests pass (existing 6 + 1 new).

- [ ] **Step 5: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/rocks/src/tactic_priors.rs
git commit -m "$(cat <<'EOF'
feat(cache): TacticPriorsCache::on_existing_db

Mirrors AttemptsCache::on_existing_db so production reuses the
engine's main TheoremDb instance.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: `VerifyWithCacheCtx` struct refactor

**Files:**
- Modify: `engine/crates/derive/src/lean_verify.rs`

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/derive/src/lean_verify.rs`:

```rust
#[cfg(test)]
mod ctx_tests {
    use super::*;
    use nasrudin_rocks::AttemptsCache;
    use tempfile::tempdir;

    #[test]
    fn verify_with_cache_ctx_constructs_with_borrowed_fields() {
        let dir = tempdir().unwrap();
        let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
        let key = [0u8; 16];
        let ctx = VerifyWithCacheCtx {
            verifier: &LeanVerifier::new("/nonexistent"),
            cache: &cache,
            cache_key: &key,
            lean_version: "4.27.0",
            worker_id: "ctx-test",
            ttl_days: 30,
        };
        // Just exercising the type; we don't actually run verifier.
        assert_eq!(ctx.lean_version, "4.27.0");
        assert_eq!(ctx.ttl_days, 30);
    }
}
```

- [ ] **Step 2: Run test, verify failure**

```bash
cd engine && cargo test -p nasrudin-derive lean_verify::ctx_tests 2>&1 | tail -10
```

Expected: `cannot find type VerifyWithCacheCtx`.

- [ ] **Step 3: Add `VerifyWithCacheCtx` and refactor `verify_with_cache`**

Edit `engine/crates/derive/src/lean_verify.rs`. Find the existing `pub fn verify_with_cache(` signature (8 args, ending in `ttl_days: i64`) and the entire function body (through the closing `}`), and replace with:

```rust
/// Borrowed bundle of identity + caches passed to `verify_with_cache`.
///
/// Holding all of these on one struct keeps the call site tidy at every
/// production verification path. All fields are borrowed for the
/// duration of the call — caller owns the `AttemptsCache` and
/// `LeanVerifier`.
pub struct VerifyWithCacheCtx<'a> {
    pub verifier: &'a LeanVerifier,
    pub cache: &'a AttemptsCache,
    pub cache_key: &'a [u8; 16],
    pub lean_version: &'a str,
    pub worker_id: &'a str,
    /// How many days a cached outcome is considered fresh. Records older
    /// than this are treated as cache misses.
    pub ttl_days: i64,
}

/// Cache-backed wrapper around [`LeanVerifier::verify_file`].
///
/// On cache hit (within `ttl_days`), returns the cached outcome
/// translated back to a [`LeanVerifyResult`]. On miss, calls the
/// underlying verifier, caches the outcome (skipping `ProcessError` —
/// transient), and returns the verifier's original result.
pub fn verify_with_cache(
    ctx: &VerifyWithCacheCtx<'_>,
    lean_content: &str,
    module_path: &str,
) -> LeanVerifyResult {
    let max_age = Duration::days(ctx.ttl_days);

    match ctx.cache.get_with_ttl(ctx.cache_key, max_age) {
        Ok(Some(record)) => {
            return match record.outcome {
                AttemptOutcome::Verified { .. } => LeanVerifyResult::Success,
                AttemptOutcome::RejectedTypeError { msg } => {
                    LeanVerifyResult::Failed { stderr: msg }
                }
                AttemptOutcome::RejectedTimeout => LeanVerifyResult::Failed {
                    stderr: "timeout".into(),
                },
                AttemptOutcome::RejectedTrivial { reason } => {
                    LeanVerifyResult::Failed { stderr: reason }
                }
                AttemptOutcome::Pending => {
                    ctx.verifier.verify_file(lean_content, module_path)
                }
            };
        }
        Ok(None) => {}
        Err(e) => {
            tracing::warn!("attempts cache get failed: {e}");
            return ctx.verifier.verify_file(lean_content, module_path);
        }
    }

    let started = std::time::Instant::now();
    let raw = ctx.verifier.verify_file(lean_content, module_path);
    let elapsed_ms = u32::try_from(started.elapsed().as_millis()).unwrap_or(u32::MAX);

    let outcome = match &raw {
        LeanVerifyResult::Success => AttemptOutcome::Verified {
            theorem_id: [0u8; 8],
            tactic: String::new(),
        },
        LeanVerifyResult::Failed { stderr } => AttemptOutcome::RejectedTypeError {
            msg: truncate(stderr, 256),
        },
        LeanVerifyResult::ProcessError { .. } => {
            return raw;
        }
    };

    let record = AttemptRecord {
        outcome,
        lean_version: ctx.lean_version.to_string(),
        timestamp: chrono::Utc::now(),
        attempted_by: ctx.worker_id.to_string(),
        elapsed_ms,
    };
    if let Err(e) = ctx.cache.put(ctx.cache_key, &record) {
        tracing::warn!("attempts cache put failed: {e}");
    }
    raw
}
```

(The old 8-arg signature is fully removed — there are no other callers in tree yet, the integration test in Task 11 uses the new struct form.)

- [ ] **Step 4: Update Phase A's standalone integration test to use the new ctx**

Edit `engine/crates/derive/tests/integration_attempts_cache.rs`. Search for `verify_with_cache(` and update any call sites. (If the existing test only exercises `AttemptsCache::lookup_or_compute` directly and never calls `verify_with_cache`, no change is needed; verify by reading the file.)

- [ ] **Step 5: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-derive lean_verify:: 2>&1 | tail -10
```

Expected: all lean_verify tests pass, including `ctx_tests::verify_with_cache_ctx_constructs_with_borrowed_fields`.

- [ ] **Step 6: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/derive/src/lean_verify.rs engine/crates/derive/tests/integration_attempts_cache.rs
git commit -m "$(cat <<'EOF'
refactor(cache): verify_with_cache takes VerifyWithCacheCtx

Replaces 8 positional args with one borrowed context struct.
Behaviour unchanged; ProcessError still skips the cache.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Drain pending oneshots on PersistentElaborator `Fatal`

**Files:**
- Modify: `engine/crates/lean-bridge/src/persistent.rs`

**Why:** Today when the persistent Lean process emits `{"kind":"fatal", …}`, the reader task logs the error but does not signal the in-flight oneshot senders. Callers waiting on those `oneshot::Receiver`s eventually time out, but they hold the request-timeout budget hostage and the elaborator is non-recoverable mid-flight. Draining the inflight map and replying to each pending oneshot with a synthetic `Fatal` response (or letting the oneshot drop, which surfaces as the existing "response channel dropped" error) makes failures fast and lets callers recover.

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/lean-bridge/src/persistent.rs` inside `#[cfg(test)] mod tests`:

```rust
    /// Synthetic test: directly invoke the inflight-drain helper added in
    /// Step 3 with a populated map, confirm every oneshot fires with a
    /// Fatal payload (mirroring what the reader task does on Fatal).
    #[tokio::test]
    async fn fatal_drains_inflight_oneshots() {
        let inflight: Inflight = Arc::new(Mutex::new(HashMap::new()));
        let (tx_a, rx_a) = oneshot::channel::<Response>();
        let (tx_b, rx_b) = oneshot::channel::<Response>();
        {
            let mut g = inflight.lock().await;
            g.insert(1, tx_a);
            g.insert(2, tx_b);
        }
        drain_inflight_with_fatal(&inflight, "lean process exploded").await;
        let r_a = rx_a.await.expect("oneshot A should fire");
        let r_b = rx_b.await.expect("oneshot B should fire");
        assert!(matches!(r_a, Response::Fatal { .. }));
        assert!(matches!(r_b, Response::Fatal { .. }));
        // Map is drained.
        assert!(inflight.lock().await.is_empty());
    }
```

- [ ] **Step 2: Run test, verify failure**

```bash
cd engine && cargo test -p nasrudin-lean-bridge persistent::tests::fatal_drains_inflight 2>&1 | tail -10
```

Expected: `cannot find function drain_inflight_with_fatal`.

- [ ] **Step 3: Add `drain_inflight_with_fatal` helper and call it from the reader task**

Edit `engine/crates/lean-bridge/src/persistent.rs`. After the existing `fn response_id(…) -> Option<u64>` helper at the bottom of the file (before `#[cfg(test)] mod tests`), add:

```rust
async fn drain_inflight_with_fatal(inflight: &Inflight, message: &str) {
    let mut g = inflight.lock().await;
    let drained: Vec<oneshot::Sender<Response>> = g.drain().map(|(_, s)| s).collect();
    drop(g);
    for sender in drained {
        let _ = sender.send(Response::Fatal {
            message: message.to_string(),
        });
    }
}
```

Then find the reader task block (the `tokio::spawn(async move { while let Ok(Some(line)) = reader.next_line().await {`). Replace the `else if let Response::Fatal { message } = resp {` arm with:

```rust
                } else if let Response::Fatal { message } = resp {
                    tracing::error!("persistent lean fatal: {message}");
                    drain_inflight_with_fatal(&inflight_r, &message).await;
                }
```

- [ ] **Step 4: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-lean-bridge persistent:: 2>&1 | tail -10
```

Expected: All persistent::tests pass (existing 4 + 1 new).

- [ ] **Step 5: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/lean-bridge/src/persistent.rs
git commit -m "$(cat <<'EOF'
fix(lean-bridge): drain inflight oneshots on PersistentElaborator Fatal

Previously a Fatal response from the Lean process logged the error
but left every pending request waiting for the per-request timeout
to fire. Now Fatal drains the inflight map and signals every pending
oneshot with the Fatal message — callers fail fast and can rebuild
the elaborator.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: `CacheBundle<'a>` for the GA hot path

**Files:**
- Create: `engine/crates/ga/src/cache_bundle.rs`
- Modify: `engine/crates/ga/src/lib.rs`
- Modify: `engine/crates/ga/Cargo.toml`

- [ ] **Step 1: Confirm dependencies are present**

Open `engine/crates/ga/Cargo.toml`. The `[dependencies]` section must include:

```toml
nasrudin-core = { path = "../core" }
nasrudin-derive = { path = "../derive" }
nasrudin-rocks = { path = "../rocks" }
```

If `nasrudin-rocks` is missing, add it. Run:

```bash
cd engine && cargo check -p nasrudin-ga 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 2: Write the failing test**

Create `engine/crates/ga/src/cache_bundle.rs`:

```rust
//! Borrowed bundle of caches + identity passed into `verify_chain`.
//!
//! Holding all of these on one struct keeps the GA call site tidy and
//! avoids spreading 6 positional arguments across `chain_engine` →
//! `chain_ga` → `verify_chain`.

use nasrudin_derive::CacheStats;
use nasrudin_rocks::{AttemptsCache, TacticPriorsCache};

/// All borrowed; lifetime tied to the GA discovery loop.
pub struct CacheBundle<'a> {
    pub attempts: &'a AttemptsCache,
    pub tactic_priors: &'a TacticPriorsCache,
    pub stats: &'a CacheStats,
    /// E.g. `"4.27.0"`. Used as `AttemptRecord.lean_version`.
    pub lean_version: &'a str,
    /// E.g. `"worker-abcd"`. Used as `AttemptRecord.attempted_by`.
    pub worker_id: &'a str,
    /// 30 in production. Tests pass a low value (or i64::MAX for "never expire").
    pub ttl_days: i64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_derive::CacheStats;
    use tempfile::tempdir;

    #[test]
    fn bundle_can_be_constructed_with_borrowed_fields() {
        let stats = CacheStats::default();
        let dir_a = tempdir().unwrap();
        let attempts = AttemptsCache::open(dir_a.path().to_str().unwrap()).unwrap();
        let dir_t = tempdir().unwrap();
        let priors = TacticPriorsCache::open(dir_t.path().to_str().unwrap()).unwrap();
        let bundle = CacheBundle {
            attempts: &attempts,
            tactic_priors: &priors,
            stats: &stats,
            lean_version: "4.27.0",
            worker_id: "test",
            ttl_days: 30,
        };
        assert_eq!(bundle.lean_version, "4.27.0");
        assert_eq!(bundle.ttl_days, 30);
    }
}
```

- [ ] **Step 3: Re-export from `ga/src/lib.rs`**

Edit `engine/crates/ga/src/lib.rs`. Add (with the other module declarations):

```rust
pub mod cache_bundle;
pub use cache_bundle::CacheBundle;
```

- [ ] **Step 4: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-ga cache_bundle:: 2>&1 | tail -10
```

Expected: `bundle_can_be_constructed_with_borrowed_fields … ok`.

- [ ] **Step 5: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/ga/src/cache_bundle.rs engine/crates/ga/src/lib.rs engine/crates/ga/Cargo.toml
git commit -m "$(cat <<'EOF'
feat(ga): CacheBundle for verify_chain wiring

One borrowed struct carrying both caches, stats, and worker identity.
Wired into verify_chain in the next task.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Wire `CacheBundle` into `verify_chain`

**Files:**
- Modify: `engine/crates/ga/src/chain_ga.rs`

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/ga/src/chain_ga.rs` inside `#[cfg(test)] mod tests`:

```rust
    #[test]
    fn verify_chain_with_cache_no_prover_root_skips_lake_build() {
        // Smoke test: the cache wiring compiles and the verify_chain_cached
        // signature accepts an Option<CacheBundle>. We don't have a Lean
        // toolchain in unit tests, so we exercise the None branch (which
        // mirrors the existing verify_chain behaviour) and the Some branch
        // through the integration test in Task 11.
        use crate::cache_bundle::CacheBundle;
        use nasrudin_derive::CacheStats;
        use nasrudin_rocks::{AttemptsCache, TacticPriorsCache};
        use tempfile::tempdir;

        let stats = CacheStats::default();
        let dir_a = tempdir().unwrap();
        let attempts = AttemptsCache::open(dir_a.path().to_str().unwrap()).unwrap();
        let dir_t = tempdir().unwrap();
        let priors = TacticPriorsCache::open(dir_t.path().to_str().unwrap()).unwrap();
        let bundle = CacheBundle {
            attempts: &attempts,
            tactic_priors: &priors,
            stats: &stats,
            lean_version: "4.27.0",
            worker_id: "test",
            ttl_days: 30,
        };
        let store = upstream_store();
        let chain = Chain(vec![]);
        // No prover root path → pre-filter rejects (empty chain). The
        // assertion is that the cached path returns the same outcome
        // shape as the un-cached path.
        let outcome = verify_chain_cached(
            &chain,
            &store,
            std::path::Path::new("/nonexistent"),
            "test_basename",
            "test_thm",
            Some(&bundle),
        );
        assert!(matches!(outcome, ChainVerifyOutcome::PreFilterFailed { .. }));
    }
```

- [ ] **Step 2: Run test, verify failure**

```bash
cd engine && cargo test -p nasrudin-ga chain_ga::tests::verify_chain_with_cache 2>&1 | tail -10
```

Expected: `cannot find function verify_chain_cached`.

- [ ] **Step 3: Add `verify_chain_cached` keeping `verify_chain` as a thin shim**

Edit `engine/crates/ga/src/chain_ga.rs`. Find the existing `pub fn verify_chain(…)` function, and right above it add:

```rust
use crate::cache_bundle::CacheBundle;
use nasrudin_core::{axiom_id_from_name, axiom_set_hash, canonical_hash};
use nasrudin_derive::lean_verify::{verify_with_cache, VerifyWithCacheCtx};
use nasrudin_derive::RuleStep;
use nasrudin_rocks::{AttemptsCache, TacticPriorsCache};
use std::collections::BTreeSet;

/// Cache-aware variant of [`verify_chain`].
///
/// When `bundle` is `Some`, the lake-build path goes through the
/// `attempts` cache (skip on hit) and on success records the winning
/// tactic into `tactic_priors`. When `None`, behaves identically to
/// [`verify_chain`].
pub fn verify_chain_cached(
    chain: &Chain,
    store: &AxiomStore,
    prover_root: impl AsRef<Path>,
    module_basename: &str,
    theorem_name: &str,
    bundle: Option<&CacheBundle<'_>>,
) -> ChainVerifyOutcome {
    use std::sync::atomic::Ordering;

    // Pre-filter: run the chain.
    let mut ctx = DerivationContext::new();
    if let Err(e) = chain.execute(store, &mut ctx) {
        return ChainVerifyOutcome::PreFilterFailed {
            reason: format!("{e}"),
        };
    }
    let final_expr = match ctx.current() {
        Some(e) => e.clone(),
        None => {
            return ChainVerifyOutcome::PreFilterFailed {
                reason: "chain produced no current expression".into(),
            };
        }
    };

    // Emit Lean.
    let cfg = LeanEmitConfig {
        namespace: "PhysicsGenerator.Derived".into(),
        theorem_name: theorem_name.to_string(),
        use_mathlib: true,
    };
    let lean_source = emit_lean_file(&ctx, &cfg);
    let module_path = format!("PhysicsGenerator.Derived.{module_basename}");

    let verifier = LeanVerifier::new(prover_root.as_ref());

    // Build the cache key + invoke the cached path. If `bundle` is None
    // we simply call `verify_file` directly — same as the legacy path.
    let outcome = if let Some(b) = bundle {
        let canonical_str = final_expr.to_canonical();
        let mut canon8 = [0u8; 8];
        let canon_bytes = canonical_hash(&canonical_str);
        canon8.copy_from_slice(&canon_bytes[..8]);

        // Walk chain steps, collect any IntroduceAxiom / IntroduceTheorem
        // names, hash each into a synthetic 8-byte ID, then BLAKE3 the
        // sorted set. (Chain doesn't carry a ProofTree; this is the
        // canonical way to express "axioms in scope for this attempt".)
        let mut axiom_ids: BTreeSet<[u8; 8]> = BTreeSet::new();
        for step in &chain.0 {
            match step {
                RuleStep::IntroduceAxiom { axiom_name } => {
                    axiom_ids.insert(axiom_id_from_name(axiom_name));
                }
                RuleStep::IntroduceTheorem { theorem_name } => {
                    axiom_ids.insert(axiom_id_from_name(theorem_name));
                }
                _ => {}
            }
        }
        let axiom_hash = axiom_set_hash(&axiom_ids);
        let cache_key = AttemptsCache::make_key(&canon8, &axiom_hash);

        // Pre-pull the cache count for stats. `verify_with_cache` itself
        // doesn't increment them; we do it here so callers see hit/miss
        // accounting without touching the derive crate.
        let pre_hit = b
            .attempts
            .get_with_ttl(&cache_key, chrono::Duration::days(b.ttl_days))
            .ok()
            .flatten()
            .is_some();
        if pre_hit {
            b.stats.attempts_hits.fetch_add(1, Ordering::Relaxed);
        } else {
            b.stats.attempts_misses.fetch_add(1, Ordering::Relaxed);
        }

        let vctx = VerifyWithCacheCtx {
            verifier: &verifier,
            cache: b.attempts,
            cache_key: &cache_key,
            lean_version: b.lean_version,
            worker_id: b.worker_id,
            ttl_days: b.ttl_days,
        };
        let raw = verify_with_cache(&vctx, &lean_source, &module_path);

        // On success record the tactic chain prior. We don't have a
        // discrete tactic name from `lake build`'s top-level run today —
        // the GA emits a `decide` / `simp; ring` style block. Persisting
        // the module name as the prior keeps the schema honest until the
        // tactic-extraction layer lands.
        if matches!(raw, LeanVerifyResult::Success) {
            // Goal skeleton from the final expression of the chain.
            let skel_hash = nasrudin_core::skeleton_hash(&final_expr);
            let priors_key = TacticPriorsCache::make_key(&skel_hash, &axiom_hash);
            let elapsed_short: u16 = 0; // verifier already returned; we don't measure here
            if let Err(e) =
                b.tactic_priors.record_success(&priors_key, theorem_name, elapsed_short)
            {
                tracing::warn!("tactic_priors record_success failed: {e}");
            }
        }
        raw
    } else {
        verifier.verify_file(&lean_source, &module_path)
    };

    // Same cleanup as legacy verify_chain.
    if !matches!(outcome, LeanVerifyResult::Success) {
        let relative = format!("{}.lean", module_path.replace('.', "/"));
        let file_path = prover_root.as_ref().join(&relative);
        let _ = std::fs::remove_file(&file_path);
    }

    match outcome {
        LeanVerifyResult::Success => ChainVerifyOutcome::Verified {
            lean_source,
            module_path,
        },
        LeanVerifyResult::Failed { stderr } => ChainVerifyOutcome::LeanRejected {
            lean_source,
            stderr,
        },
        LeanVerifyResult::ProcessError { message } => {
            ChainVerifyOutcome::ToolchainError { message }
        }
    }
}
```

Then change `pub fn verify_chain` (the existing one) to delegate:

```rust
pub fn verify_chain(
    chain: &Chain,
    store: &AxiomStore,
    prover_root: impl AsRef<Path>,
    module_basename: &str,
    theorem_name: &str,
) -> ChainVerifyOutcome {
    verify_chain_cached(chain, store, prover_root, module_basename, theorem_name, None)
}
```

- [ ] **Step 4: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-ga chain_ga::tests::verify_chain_with_cache 2>&1 | tail -10
```

Expected: pass.

- [ ] **Step 5: Confirm full workspace still compiles + existing tests pass**

```bash
cd engine && cargo test --workspace --lib 2>&1 | tail -20
```

Expected: every existing test still passes.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/ga/src/chain_ga.rs
git commit -m "$(cat <<'EOF'
feat(ga): wire CacheBundle into verify_chain_cached

verify_chain stays as a no-cache shim; new verify_chain_cached threads
AttemptsCache (skip on hit, write on miss) and TacticPriorsCache
(record_success on Verified). Stats incremented per call. Axiom-set
hash derived by walking RuleStep::IntroduceAxiom / IntroduceTheorem
names through axiom_id_from_name.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8: Plumb cache through `chain_engine::run_discovery`

**Files:**
- Modify: `engine/crates/ga/src/chain_engine.rs`

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/ga/src/chain_engine.rs` inside `#[cfg(test)] mod tests`:

```rust
    #[test]
    fn discovery_config_accepts_cache_bundle_field() {
        // Type-level test: DiscoveryConfig must have a cache_ctx Option
        // field of the right type so callers (workers, in-process GA)
        // can pass it in without rebuilding the struct each iteration.
        let cfg = DiscoveryConfig {
            generations: 1,
            cache_ctx: None,
            ..DiscoveryConfig::default()
        };
        assert!(cfg.cache_ctx.is_none());
    }
```

- [ ] **Step 2: Run test, verify failure**

```bash
cd engine && cargo test -p nasrudin-ga chain_engine::tests::discovery_config_accepts_cache_bundle_field 2>&1 | tail -10
```

Expected: `no field cache_ctx`.

- [ ] **Step 3: Add `cache_ctx` to `DiscoveryConfig` and pass through `run_discovery`**

Edit `engine/crates/ga/src/chain_engine.rs`. Find the `pub struct DiscoveryConfig` definition. Add this field at the bottom (just before the closing `}`):

```rust
    /// When `Some`, the GA's lake-verify path goes through the cache
    /// layer (skip on hit, record on success). Held as a raw pointer-
    /// like wrapper rather than `&CacheBundle<'_>` because
    /// `DiscoveryConfig` is `Clone`. See [`CacheCtxHandle`] below.
    pub cache_ctx: Option<CacheCtxHandle>,
```

Then immediately above the struct, define:

```rust
/// Type-erased pointer to a `CacheBundle`. Holds the bundle for the
/// duration of a discovery run; the caller (worker, in-process GA) is
/// responsible for keeping the underlying caches alive.
///
/// Cloned along with `DiscoveryConfig` (cheap — it's a borrowed handle
/// behind an `Arc<Mutex<…>>`-shaped struct on the caller side).
#[derive(Clone)]
pub struct CacheCtxHandle {
    inner: std::sync::Arc<dyn CacheCtxAccess + Send + Sync>,
}

/// Internal trait erased by `CacheCtxHandle`. Implementors hand out a
/// `CacheBundle<'_>` for the duration of one verify call.
pub trait CacheCtxAccess {
    fn with_bundle<'a>(
        &'a self,
        cb: &mut dyn FnMut(&crate::cache_bundle::CacheBundle<'a>),
    );
}

impl CacheCtxHandle {
    pub fn new(inner: std::sync::Arc<dyn CacheCtxAccess + Send + Sync>) -> Self {
        Self { inner }
    }
    pub fn with_bundle<'a>(
        &'a self,
        cb: &mut dyn FnMut(&crate::cache_bundle::CacheBundle<'a>),
    ) {
        self.inner.with_bundle(cb);
    }
}
```

Then add to `Default for DiscoveryConfig`:

```rust
            cache_ctx: None,
```

(immediately before the closing `}` of the `Self { ... }` literal in `default()`).

Then update the call to `verify_chain` inside `run_discovery`. Find:

```rust
                    match verify_chain(
                        &top.chain,
                        store,
                        prover_root.as_path(),
                        &basename,
                        &theorem_name,
                    ) {
```

Replace with:

```rust
                    let outcome = match config.cache_ctx.as_ref() {
                        Some(handle) => {
                            let mut held: Option<crate::chain_ga::ChainVerifyOutcome> = None;
                            handle.with_bundle(&mut |bundle| {
                                held = Some(crate::chain_ga::verify_chain_cached(
                                    &top.chain,
                                    store,
                                    prover_root.as_path(),
                                    &basename,
                                    &theorem_name,
                                    Some(bundle),
                                ));
                            });
                            held.unwrap_or(crate::chain_ga::ChainVerifyOutcome::ToolchainError {
                                message: "cache handle did not produce outcome".into(),
                            })
                        }
                        None => crate::chain_ga::verify_chain(
                            &top.chain,
                            store,
                            prover_root.as_path(),
                            &basename,
                            &theorem_name,
                        ),
                    };
                    match outcome {
```

- [ ] **Step 4: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-ga chain_engine:: 2>&1 | tail -10
```

Expected: existing tests still pass + 1 new test passes.

- [ ] **Step 5: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/ga/src/chain_engine.rs
git commit -m "$(cat <<'EOF'
feat(ga): plumb CacheCtxHandle through DiscoveryConfig

run_discovery now picks up an optional cache_ctx and routes to
verify_chain_cached when set. Default None preserves single-node
behaviour.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: Build `CacheCtx` in the API server's `main.rs`

**Files:**
- Create: `engine/crates/api/src/cache.rs`
- Modify: `engine/crates/api/src/lib.rs` (or wherever the existing module declarations live)
- Modify: `engine/crates/api/src/state.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Create the cache module**

Create `engine/crates/api/src/cache.rs`:

```rust
//! Server-side cache wiring.
//!
//! Owns the long-lived `AttemptsCache` and `TacticPriorsCache` against
//! the engine's main `TheoremDb`, plus the `CacheStats` counter sink.
//! Constructed once in `main.rs` from `CacheConfig::from_env()` and
//! plumbed into `AppState` and `ReverifyQueue`.

use std::sync::Arc;

use nasrudin_derive::{CacheConfig, CacheStats};
use nasrudin_rocks::{AttemptsCache, TacticPriorsCache, TheoremDb};

/// Long-lived cache bundle held on `AppState`. `Option`-shaped at the
/// `AppState` level so feature-flag-off path is a `None` (no
/// branches, no allocations).
pub struct CacheCtx {
    pub config: CacheConfig,
    pub attempts: Arc<AttemptsCache>,
    pub tactic_priors: Arc<TacticPriorsCache>,
    pub stats: Arc<CacheStats>,
    pub lean_version: String,
    pub worker_id: String,
}

impl CacheCtx {
    /// Build from `CacheConfig::from_env()` against the engine's main
    /// `TheoremDb`. Caches are constructed unconditionally — the
    /// per-flag gating happens at the call site (we still pay the
    /// `Arc<DB>` clone, which is one atomic-increment).
    ///
    /// `lean_version` and `worker_id` are stamped onto every cached
    /// `AttemptRecord`. Read from env (`NASRUDIN_LEAN_VERSION`,
    /// `NASRUDIN_WORKER_ID`) with sensible defaults.
    pub fn build(db: &Arc<TheoremDb>) -> anyhow::Result<Self> {
        let config = CacheConfig::from_env();
        let attempts = Arc::new(AttemptsCache::on_existing_db(db.shared_db())?);
        let tactic_priors = Arc::new(TacticPriorsCache::on_existing_db(db.shared_db())?);
        let stats = Arc::new(CacheStats::default());
        let lean_version =
            std::env::var("NASRUDIN_LEAN_VERSION").unwrap_or_else(|_| "4.27.0".into());
        let worker_id =
            std::env::var("NASRUDIN_WORKER_ID").unwrap_or_else(|_| "api-server".into());
        Ok(Self {
            config,
            attempts,
            tactic_priors,
            stats,
            lean_version,
            worker_id,
        })
    }
}
```

- [ ] **Step 2: Register the module**

Search for where existing modules are declared in the API crate:

```bash
grep -n "^pub mod\|^mod " /Volumes/CORSAIR/code/personal/nasrudin/engine/crates/api/src/lib.rs 2>/dev/null
```

If `engine/crates/api/src/lib.rs` exists and declares modules there, add `pub mod cache;` to it. Otherwise, in `engine/crates/api/src/main.rs` add `mod cache;` near the top with the other `mod` declarations.

- [ ] **Step 3: Add `cache_ctx: Option<Arc<CacheCtx>>` to `AppState`**

Edit `engine/crates/api/src/state.rs`. Add to the imports:

```rust
use crate::cache::CacheCtx;
```

Add to the `pub struct AppState` (just before the closing `}`):

```rust
    /// Server-side cache bundle. `None` when no caches are constructed
    /// (the GA / reverify paths fall back to direct verification).
    /// Populated unconditionally today; the per-flag gating happens at
    /// the call site via `cache_ctx.config.attempts_enabled` etc.
    pub cache_ctx: Option<Arc<CacheCtx>>,
```

- [ ] **Step 4: Build `CacheCtx` in `main.rs`**

Edit `engine/crates/api/src/main.rs`. Find the line:

```rust
    let db = Arc::new(TheoremDb::new(&db_path)?);
    tracing::info!("RocksDB opened at {db_path}");
```

Immediately after that block, add:

```rust
    let cache_ctx = match physics_api::cache::CacheCtx::build(&db) {
        Ok(c) => {
            tracing::info!(
                "cache layer built (attempts={}, tactic_priors={}, persistent_lean={})",
                c.config.attempts_enabled,
                c.config.tactic_priors_enabled,
                c.config.persistent_lean_enabled,
            );
            Some(Arc::new(c))
        }
        Err(e) => {
            tracing::warn!("cache layer init failed ({e}); continuing without caches");
            None
        }
    };
```

Then find the `AppState` construction (search for `let state = Arc::new(AppState {`) and add `cache_ctx: cache_ctx.clone(),` to the struct literal.

- [ ] **Step 5: Pass `CacheCtx` into `ReverifyQueue`**

Edit `engine/crates/api/src/reverify.rs`. Add to the imports:

```rust
use crate::cache::CacheCtx;
```

Add a field to `ReverifyQueue`:

```rust
    pub cache_ctx: Option<std::sync::Arc<CacheCtx>>,
```

Update the construction in `main.rs` (find `Arc::new(physics_api::reverify::ReverifyQueue {`) and add `cache_ctx: cache_ctx.clone(),` to the struct literal.

- [ ] **Step 6: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -10
```

Expected: clean.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/cache.rs engine/crates/api/src/state.rs engine/crates/api/src/main.rs engine/crates/api/src/reverify.rs engine/crates/api/src/lib.rs
git commit -m "$(cat <<'EOF'
feat(cache): wire CacheCtx into AppState and ReverifyQueue

Builds AttemptsCache + TacticPriorsCache against the engine's main
TheoremDb at boot; AppState carries Option<Arc<CacheCtx>>. ReverifyQueue
gets the same handle. No behaviour change yet — the next task gates the
verify path on cache_ctx.config.attempts_enabled.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 10: Cache-aware `LakeBuilder::verify`

**Files:**
- Modify: `engine/crates/api/src/lake_builder.rs`

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/api/src/lake_builder.rs` at the end of the file (or in an existing `#[cfg(test)] mod tests` if there is one — verify with `grep -n "#\[cfg(test)\]" engine/crates/api/src/lake_builder.rs`):

```rust
#[cfg(test)]
mod cache_tests {
    use super::*;
    use nasrudin_rocks::{AttemptOutcome, AttemptRecord, AttemptsCache};
    use chrono::Utc;
    use tempfile::tempdir;

    #[tokio::test]
    async fn verify_cached_returns_hit_without_invoking_lake() {
        let dir = tempdir().unwrap();
        let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
        let key = [9u8; 16];
        cache
            .put(
                &key,
                &AttemptRecord {
                    outcome: AttemptOutcome::Verified {
                        theorem_id: [0; 8],
                        tactic: "ring".into(),
                    },
                    lean_version: "4.27.0".into(),
                    timestamp: Utc::now(),
                    attempted_by: "test".into(),
                    elapsed_ms: 1,
                },
            )
            .unwrap();

        // `lake_builder` is constructed pointing at /nonexistent —
        // a real lake invocation would error. Cache hit must short-
        // circuit before that.
        let lake = LakeBuilder::new(
            std::path::PathBuf::from("/nonexistent"),
            std::path::PathBuf::from("/tmp"),
            1,
        );
        let result = lake
            .verify_cached(&cache, &key, "4.27.0", "test", 30, "lean source", "abc123")
            .await
            .expect("cache hit must return Ok");
        assert!(matches!(result, VerifyOutcome::Verified { .. }));
    }
}
```

- [ ] **Step 2: Run test, verify failure**

```bash
cd engine && cargo test -p physics-api lake_builder::cache_tests 2>&1 | tail -10
```

Expected: `no method named verify_cached`.

- [ ] **Step 3: Implement `verify_cached`**

Edit `engine/crates/api/src/lake_builder.rs`. Add to the imports at the top:

```rust
use chrono::Duration as ChronoDuration;
use nasrudin_rocks::{AttemptOutcome, AttemptRecord, AttemptsCache};
```

Inside `impl LakeBuilder`, add (right after the existing `pub async fn verify`):

```rust
    /// Cache-backed wrapper around [`Self::verify`]. On hit (within
    /// `ttl_days`), returns the cached outcome without invoking
    /// `lake build`. On miss, runs `verify` and writes the outcome
    /// (skipping persistence on transient process errors — same as
    /// `nasrudin_derive::lean_verify::verify_with_cache`).
    pub async fn verify_cached(
        &self,
        cache: &AttemptsCache,
        cache_key: &[u8; 16],
        lean_version: &str,
        worker_id: &str,
        ttl_days: i64,
        lean_source: &str,
        theorem_id_hex: &str,
    ) -> Result<VerifyOutcome> {
        let max_age = ChronoDuration::days(ttl_days);
        if let Ok(Some(rec)) = cache.get_with_ttl(cache_key, max_age) {
            return Ok(match rec.outcome {
                AttemptOutcome::Verified { tactic, .. } => VerifyOutcome::Verified {
                    tactic: if tactic.is_empty() {
                        "cached".into()
                    } else {
                        tactic
                    },
                    duration_ms: 0,
                },
                AttemptOutcome::RejectedTypeError { msg } => VerifyOutcome::Rejected {
                    reason: "cached_rejected".into(),
                    stderr_tail: msg,
                },
                AttemptOutcome::RejectedTimeout => VerifyOutcome::Rejected {
                    reason: "cached_timeout".into(),
                    stderr_tail: String::new(),
                },
                AttemptOutcome::RejectedTrivial { reason } => VerifyOutcome::Rejected {
                    reason,
                    stderr_tail: String::new(),
                },
                AttemptOutcome::Pending => self.verify(lean_source, theorem_id_hex).await?,
            });
        }

        let raw = self.verify(lean_source, theorem_id_hex).await?;
        let (outcome, persist) = match &raw {
            VerifyOutcome::Verified { tactic, duration_ms: _ } => (
                AttemptOutcome::Verified {
                    theorem_id: [0u8; 8],
                    tactic: tactic.clone(),
                },
                true,
            ),
            VerifyOutcome::Rejected { reason, stderr_tail } => (
                AttemptOutcome::RejectedTypeError {
                    msg: format!("{reason}: {stderr_tail}"),
                },
                true,
            ),
        };
        if persist {
            let record = AttemptRecord {
                outcome,
                lean_version: lean_version.to_string(),
                timestamp: chrono::Utc::now(),
                attempted_by: worker_id.to_string(),
                elapsed_ms: 0,
            };
            if let Err(e) = cache.put(cache_key, &record) {
                tracing::warn!("attempts cache put failed: {e}");
            }
        }
        Ok(raw)
    }
```

- [ ] **Step 4: Run tests, verify pass**

```bash
cd engine && cargo test -p physics-api lake_builder::cache_tests 2>&1 | tail -10
```

Expected: pass.

- [ ] **Step 5: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/lake_builder.rs
git commit -m "$(cat <<'EOF'
feat(api): LakeBuilder::verify_cached for the reverify worker pool

Async wrapper around verify() that consults AttemptsCache (skip on
hit, write on miss) using the same outcome-mapping as
nasrudin_derive::lean_verify::verify_with_cache. ProcessError-equivalent
transient failures are caught upstream by verify() returning Err, so
they don't reach the cache layer.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11: Wire `verify_cached` into the reverify hot path

**Files:**
- Modify: `engine/crates/api/src/reverify.rs`

- [ ] **Step 1: Find both `lake.verify` callsites**

```bash
grep -n "lake.verify(" /Volumes/CORSAIR/code/personal/nasrudin/engine/crates/api/src/reverify.rs
```

Expected: two callsites — A-path (around line 141) and B-path (around line 256). Note line numbers, they will shift after the edit.

- [ ] **Step 2: Update both callsites to gate on `cache_ctx.config.attempts_enabled`**

For each `match self.lake.verify(<source>, &theorem_id_hex).await? {` block, replace with:

```rust
                let verify_outcome = match self
                    .cache_ctx
                    .as_ref()
                    .filter(|c| c.config.attempts_enabled)
                {
                    Some(c) => {
                        // Cache key: canonical_hash || axiom_set_hash.
                        // canonical_hash from the row; axiom_set_hash from
                        // the chain replay if available, else zero-padded.
                        let mut canon8 = [0u8; 8];
                        canon8.copy_from_slice(&row.canonical_hash[..8]);
                        let axiom_hash = self.axiom_hash_for_row(&row);
                        let cache_key = nasrudin_rocks::AttemptsCache::make_key(&canon8, &axiom_hash);
                        self.lake
                            .verify_cached(
                                &c.attempts,
                                &cache_key,
                                &c.lean_version,
                                &c.worker_id,
                                30,
                                <SOURCE_VAR>,
                                &theorem_id_hex,
                            )
                            .await?
                    }
                    None => self.lake.verify(<SOURCE_VAR>, &theorem_id_hex).await?,
                };
                match verify_outcome {
```

Replace `<SOURCE_VAR>` with `&regen.lean_source` for the A-path and `&row.lean_source` for the B-path.

- [ ] **Step 3: Add `axiom_hash_for_row` helper**

In the same file, add inside `impl ReverifyQueue` (after the existing methods):

```rust
    /// Compute the 8-byte axiom-set hash for a theorems row. Walks the
    /// row's `chain_json` (the same source `check_chain` parses) and
    /// collects axiom names from `IntroduceAxiom` / `IntroduceTheorem`
    /// steps, hashing each into a synthetic ID and then BLAKE3-prefixing
    /// the sorted set. Falls back to all-zeros when the row has no chain
    /// (imported / backfilled theorems with empty `chain_json`).
    fn axiom_hash_for_row(&self, row: &nasrudin_pg::entity::theorems::Model) -> [u8; 8] {
        use nasrudin_core::{axiom_id_from_name, axiom_set_hash};
        use nasrudin_derive::RuleStep;
        use std::collections::BTreeSet;

        let steps_value = match &row.chain_json {
            v if v.is_null() => return [0u8; 8],
            serde_json::Value::Array(arr) if arr.is_empty() => return [0u8; 8],
            v => v,
        };
        let steps: Vec<RuleStep> = match serde_json::from_value(steps_value.clone()) {
            Ok(s) => s,
            Err(_) => return [0u8; 8],
        };
        let mut ids: BTreeSet<[u8; 8]> = BTreeSet::new();
        for step in &steps {
            match step {
                RuleStep::IntroduceAxiom { axiom_name } => {
                    ids.insert(axiom_id_from_name(axiom_name));
                }
                RuleStep::IntroduceTheorem { theorem_name } => {
                    ids.insert(axiom_id_from_name(theorem_name));
                }
                _ => {}
            }
        }
        axiom_set_hash(&ids)
    }
```

- [ ] **Step 4: Run tests, verify pass**

```bash
cd engine && cargo test -p physics-api 2>&1 | tail -20
```

Expected: every existing reverify test still passes; no new tests added in this task (the round-trip is covered by Task 12's integration test).

- [ ] **Step 5: Confirm full workspace still compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/reverify.rs
git commit -m "$(cat <<'EOF'
feat(api): reverify queue uses lake.verify_cached when attempts cache is on

Both A-path and B-path now route through LakeBuilder::verify_cached when
NASRUDIN_CACHE_ATTEMPTS=1 is set on the server. axiom_hash_for_row
re-walks the chain to compute the second half of the cache key.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12: End-to-end integration test for cache wiring

**Files:**
- Create: `engine/crates/derive/tests/integration_cache_wiring.rs`

- [ ] **Step 1: Write the test**

Create `engine/crates/derive/tests/integration_cache_wiring.rs`:

```rust
//! End-to-end: feed a synthetic verifier outcome through the cache,
//! then call again with the same key and confirm the verifier is NOT
//! invoked the second time. This is the regression net for "the GA
//! actually skips lake build on a known-rejected canonical".

use chrono::{Duration, Utc};
use nasrudin_derive::lean_verify::{verify_with_cache, LeanVerifier, LeanVerifyResult, VerifyWithCacheCtx};
use nasrudin_rocks::{AttemptOutcome, AttemptRecord, AttemptsCache};
use tempfile::tempdir;

#[test]
fn second_call_with_same_key_short_circuits_via_cache() {
    let dir_cache = tempdir().unwrap();
    let cache = AttemptsCache::open(dir_cache.path().to_str().unwrap()).unwrap();
    let cache_key = [0xab; 16];

    // Pre-populate the cache with a Verified outcome.
    cache
        .put(
            &cache_key,
            &AttemptRecord {
                outcome: AttemptOutcome::Verified {
                    theorem_id: [0u8; 8],
                    tactic: "decide".into(),
                },
                lean_version: "4.27.0".into(),
                timestamp: Utc::now(),
                attempted_by: "fixture".into(),
                elapsed_ms: 1,
            },
        )
        .unwrap();

    // Construct a verifier pointing at /nonexistent: a real
    // verify_file would return ProcessError. Cache hit must short-
    // circuit before that, so we expect Success.
    let verifier = LeanVerifier::new("/nonexistent");
    let ctx = VerifyWithCacheCtx {
        verifier: &verifier,
        cache: &cache,
        cache_key: &cache_key,
        lean_version: "4.27.0",
        worker_id: "test",
        ttl_days: 30,
    };
    let result = verify_with_cache(&ctx, "stub source", "Stub.Module");
    assert!(
        matches!(result, LeanVerifyResult::Success),
        "expected Success from cache hit, got {:?}",
        result
    );
}

#[test]
fn miss_then_hit_short_circuits_after_first_compute() {
    // Confirm the lookup_or_compute path also covers
    // miss-then-hit. We use AttemptsCache::lookup_or_compute directly
    // because we don't want to depend on LeanVerifier's process-spawn.
    let dir = tempdir().unwrap();
    let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
    let key = [0xcd; 16];
    let mut compute_calls = 0;
    let max_age = Duration::days(30);

    let _r1 = cache
        .lookup_or_compute(&key, max_age, "w1", "4.27.0", || {
            compute_calls += 1;
            AttemptOutcome::RejectedTimeout
        })
        .unwrap();

    let _r2 = cache
        .lookup_or_compute(&key, max_age, "w1", "4.27.0", || {
            compute_calls += 1;
            AttemptOutcome::RejectedTimeout
        })
        .unwrap();

    assert_eq!(compute_calls, 1, "second call should hit cache");
}

#[test]
fn cache_skips_persistence_on_process_error() {
    // verify_with_cache must NOT cache ProcessError outcomes
    // (transient — different machine might succeed). Caller is a
    // verifier whose binary is missing; we confirm the cache stays
    // empty.
    let dir = tempdir().unwrap();
    let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
    let key = [0xef; 16];

    let verifier = LeanVerifier::new("/nonexistent");
    let ctx = VerifyWithCacheCtx {
        verifier: &verifier,
        cache: &cache,
        cache_key: &key,
        lean_version: "4.27.0",
        worker_id: "test",
        ttl_days: 30,
    };
    let _ = verify_with_cache(&ctx, "stub source", "Stub.Module");

    // Cache should still be empty for this key (ProcessError not persisted).
    assert!(
        cache.get(&key).unwrap().is_none(),
        "ProcessError must not be cached"
    );
}
```

- [ ] **Step 2: Run the integration test**

```bash
cd engine && cargo test -p nasrudin-derive --test integration_cache_wiring 2>&1 | tail -20
```

Expected: 3 pass.

- [ ] **Step 3: Confirm full workspace test suite still passes**

```bash
cd engine && cargo test --workspace --lib 2>&1 | tail -10
```

Expected: same number as Phase A's final state, plus the new tests added by this plan.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/derive/tests/integration_cache_wiring.rs
git commit -m "$(cat <<'EOF'
test(cache): end-to-end wiring regression test

Covers cache hit short-circuit, miss-then-hit, and ProcessError
non-persistence.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 13: Document the wiring in `CACHE_LAYER.md`

**Files:**
- Modify: `engine/crates/derive/CACHE_LAYER.md`

- [ ] **Step 1: Append the Phase A.5 section**

Open `engine/crates/derive/CACHE_LAYER.md` and append:

```markdown

## Phase A.5 — Wiring (2026-04-29)

The Phase A caches are now wired into both the GA hot path and the
server's reverify queue. With `NASRUDIN_CACHE_ATTEMPTS=1`,
`NASRUDIN_CACHE_TACTIC_PRIORS=1`, and `NASRUDIN_CACHE_PERSISTENT_LEAN=1`
set on a worker or on the API server, verification skips redundant
`lake build` calls.

### Wiring map

| Path | Site | Behaviour when flag is on |
|---|---|---|
| GA in-process / external worker | `nasrudin_ga::chain_engine::run_discovery` → `chain_ga::verify_chain_cached` | Skips `lake build` on attempts-cache hit; records `tactic_priors` on success |
| API reverify queue | `physics_api::reverify::ReverifyQueue::process_one` → `LakeBuilder::verify_cached` | Same skip semantics on the server-side regen + worker-submitted Lean paths |
| Persistent Lean | `nasrudin_lean_bridge::PersistentElaborator` | A-path verification reuses one long-lived process; Fatal drains all pending oneshots |

### Constructing `CacheCtx`

The API server builds a single `CacheCtx` at boot via
`physics_api::cache::CacheCtx::build(&db)`. It carries:

- `config: CacheConfig` — read from env at boot
- `attempts: Arc<AttemptsCache>` — opened against `db.shared_db()`
- `tactic_priors: Arc<TacticPriorsCache>` — same shared DB
- `stats: Arc<CacheStats>` — counter sink, reported via `cache_stats` bin
- `lean_version`, `worker_id` — stamped on every cached `AttemptRecord`

External workers build their own `CacheCtx`-shaped bundle from the
worker-side `TheoremDb` instance and pass it into `DiscoveryConfig`
via `CacheCtxHandle`.

### Reading stats

```bash
cd engine && cargo run --release --bin cache_stats -- --db ./data/theorems.db
```

Reports per-CF row counts plus the live `CacheStats` counters when
attached to a running process (today: file-only; live attach lands in
Phase A.6 if the operator asks for it).

### Disabling

Unset the env vars (or set to `0`/`false`/`no`). All call sites fall
back to direct verification with no behavioural drift.
```

- [ ] **Step 2: Confirm the file reads coherently**

```bash
head -60 /Volumes/CORSAIR/code/personal/nasrudin/engine/crates/derive/CACHE_LAYER.md
```

Expected: the existing Phase A content followed by the new section, no duplicate headers.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/derive/CACHE_LAYER.md
git commit -m "$(cat <<'EOF'
docs(cache): document Phase A.5 wiring

Wiring map, CacheCtx construction recipe, stats invocation, disable
recipe.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Closing checklist

After all 13 tasks land, this should hold:

- `cargo check --workspace` exits 0.
- `cargo test --workspace` passes (203 + new tests from this plan).
- `NASRUDIN_CACHE_ATTEMPTS=1 cargo run --bin cache_stats -- --db ./data/theorems.db` reports `attempts.rows >= 0` and `tactic_priors.rows >= 0` against a real engine DB.
- Setting `NASRUDIN_CACHE_ATTEMPTS=1` on a discovery run reduces `lake build` invocations on a second run with the same input.
- `verify_chain` (legacy signature) still works for callers that haven't migrated.
- `LakeBuilder::verify` (legacy signature) still works — `verify_cached` is additive.

Phase A.5 is done; Phase B (embedding store) can now build on the assumption that "caches work end-to-end".
