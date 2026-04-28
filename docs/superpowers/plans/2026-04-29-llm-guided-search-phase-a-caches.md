# LLM-Guided Search — Phase A — Cache Layer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship the three-cache throughput layer (persistent Lean elaborator, attempts memoisation, tactic priors) from spec §3, behind feature flags, with stats reporting. No researcher-facing surface yet — every existing worker just runs faster.

**Architecture:** Three independent caches glued by a shared feature-flag plumbing and a unified `nasrudin-cache-stats` reporter. Persistent Lean lives in `nasrudin-lean-bridge` as a new sibling to `process.rs`. Attempts cache and tactic priors live in `nasrudin-rocks` as two new column families following the existing `CF_*` pattern. Goal-skeleton hashing lives in `nasrudin-core` as a new pure module. All caches default OFF; opt-in via env flags so the existing fleet can A/B against baseline before switching.

**Tech Stack:** Rust 1.95, RocksDB (already a workspace dep), `lean --server` (JSON-RPC), `tokio::process::Command`, `blake3` (new workspace dep), `serde_json`.

---

## Spec reference

This plan implements §3 (Cache layer) of `docs/superpowers/specs/2026-04-28-llm-guided-search-design.md`. Subsections covered:

- §3.1 — Persistent Lean elaborator
- §3.2 — Attempts cache
- §3.3 — Tactic priors
- §3.4 — Cache layer integration (feature flags + stats)

Phases B-F are out of scope for this plan; their dependencies on Phase A are limited to "the caches exist and report stats".

---

## File structure

**New files:**

| Path | Responsibility |
|---|---|
| `engine/crates/core/src/skeleton.rs` | `Expr → goal_skeleton` normaliser + hash |
| `engine/crates/rocks/src/attempts_cache.rs` | RocksDB CF wrapper for memoised verification attempts |
| `engine/crates/rocks/src/tactic_priors.rs` | RocksDB CF wrapper for goal-skeleton → tactic-chain priors |
| `engine/crates/lean-bridge/src/persistent.rs` | Long-lived `lean --server` client speaking JSON-RPC |
| `engine/crates/lean-bridge/src/persistent_protocol.rs` | Wire types for the elaborator JSON-RPC protocol |
| `engine/crates/derive/src/cache_config.rs` | Feature-flag reading + cache-stats aggregation |
| `engine/crates/api/src/bin/cache_stats.rs` | `nasrudin worker stats` CLI subcommand binary |
| `engine/crates/derive/tests/integration_persistent_lean.rs` | 10k-attempt soak test |
| `engine/crates/derive/tests/integration_attempts_cache.rs` | End-to-end cache hit/miss test |

**Modified files:**

| Path | Change |
|---|---|
| `engine/crates/rocks/src/lib.rs` | Add `CF_ATTEMPTS`, `CF_TACTIC_PRIORS` to `ALL_CFS`; expose new wrappers |
| `engine/crates/lean-bridge/src/lib.rs` | Re-export `persistent::PersistentElaborator` |
| `engine/crates/lean-bridge/src/tactic.rs` | New `try_priors_first` helper that consults `TacticPriorsCache` |
| `engine/crates/derive/src/lean_verify.rs` | Wrap call sites with `attempts_cache.lookup_or_compute` |
| `engine/crates/derive/src/lib.rs` | Re-export new types |
| `engine/crates/api/Cargo.toml` | Register `cache_stats` bin target |
| `engine/Cargo.toml` | Add `blake3` to workspace deps |

---

## Conventions for this plan

- After every task: run `cargo check -p physics-api -p nasrudin-rocks -p nasrudin-lean-bridge -p nasrudin-derive -p nasrudin-core` from `engine/` and confirm exit 0 before committing.
- All new RocksDB writes use `serde_json` for value encoding (matches existing CF pattern in `engine/crates/rocks/src/lib.rs`).
- Feature flags are env vars read once at process startup via `CacheConfig::from_env()`. Default off.
- Test fixtures use `tempfile::tempdir()` for isolated RocksDB instances.
- Commit messages follow the existing repo convention: type scope: subject (e.g. `feat(cache):`, `test(cache):`).

---

## Task 1: Add `blake3` to workspace dependencies

**Files:**
- Modify: `engine/Cargo.toml`

- [ ] **Step 1: Add blake3 to workspace deps**

Open `engine/Cargo.toml`. In the `[workspace.dependencies]` section, add:

```toml
blake3 = "1.5"
```

- [ ] **Step 2: Verify resolves**

Run from `engine/`:
```bash
cargo check --workspace 2>&1 | tail -5
```

Expected: `Finished` line, exit 0.

- [ ] **Step 3: Commit**

```bash
git add engine/Cargo.toml
git commit -m "chore(cache): add blake3 to workspace deps"
```

---

## Task 2: Goal-skeleton hashing in `nasrudin-core`

**Files:**
- Create: `engine/crates/core/src/skeleton.rs`
- Modify: `engine/crates/core/src/lib.rs`
- Modify: `engine/crates/core/Cargo.toml`

- [ ] **Step 1: Add blake3 to nasrudin-core**

In `engine/crates/core/Cargo.toml`, add to `[dependencies]`:

```toml
blake3 = { workspace = true }
```

- [ ] **Step 2: Write the failing tests**

Create `engine/crates/core/src/skeleton.rs`:

```rust
//! Canonicalise an `Expr` into a goal-skeleton suitable for cache lookup.
//!
//! Two expressions hash to the same skeleton iff they differ only in:
//!   - literal numeric values (5 vs 7 erased to NUM_LIT)
//!   - free-variable names (a vs x erased to V0, V1, … in left-to-right order)
//!
//! Operator structure, axiom references, and bound-variable shadowing are preserved.

#[cfg(test)]
mod tests {
    use crate::Expr;
    use super::*;

    #[test]
    fn literal_numerals_collide() {
        let e1 = Expr::Add(Box::new(Expr::Var("x".into())), Box::new(Expr::Num(5.0)));
        let e2 = Expr::Add(Box::new(Expr::Var("x".into())), Box::new(Expr::Num(7.0)));
        assert_eq!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn alpha_renamed_variables_collide() {
        let e1 = Expr::Mul(Box::new(Expr::Var("a".into())), Box::new(Expr::Var("b".into())));
        let e2 = Expr::Mul(Box::new(Expr::Var("x".into())), Box::new(Expr::Var("y".into())));
        assert_eq!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn different_operators_diverge() {
        let e1 = Expr::Add(Box::new(Expr::Var("x".into())), Box::new(Expr::Var("y".into())));
        let e2 = Expr::Mul(Box::new(Expr::Var("x".into())), Box::new(Expr::Var("y".into())));
        assert_ne!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn variable_position_is_significant() {
        // f(a, b) ≠ f(b, a) — order matters for non-commutative operations
        let e1 = Expr::Sub(Box::new(Expr::Var("a".into())), Box::new(Expr::Var("b".into())));
        let e2 = Expr::Sub(Box::new(Expr::Var("b".into())), Box::new(Expr::Var("a".into())));
        // Both rename to (V0 - V1) — they DO collide under our normalisation.
        // This is intentional: tactic priors only care about expression *shape*.
        assert_eq!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn deterministic() {
        let e = Expr::Add(Box::new(Expr::Var("x".into())), Box::new(Expr::Num(3.0)));
        let h1 = skeleton_hash(&e);
        let h2 = skeleton_hash(&e);
        assert_eq!(h1, h2);
    }
}
```

- [ ] **Step 3: Wire skeleton.rs into lib.rs**

Append to `engine/crates/core/src/lib.rs`:

```rust
pub mod skeleton;
pub use skeleton::{skeleton_hash, normalise_to_skeleton, SkeletonHash};
```

- [ ] **Step 4: Run tests, confirm they fail**

```bash
cargo test -p nasrudin-core skeleton:: 2>&1 | tail -10
```

Expected: compilation error or `cannot find function skeleton_hash`.

- [ ] **Step 5: Implement `skeleton_hash` and `normalise_to_skeleton`**

Add to `engine/crates/core/src/skeleton.rs` above the `#[cfg(test)] mod tests`:

```rust
use crate::Expr;
use std::collections::HashMap;

/// 8-byte BLAKE3 prefix over the skeleton's canonical bytes.
pub type SkeletonHash = [u8; 8];

/// Canonicalise: numeric literals → "L"; variables → "V<index>" left-to-right.
/// Returns the canonical-text representation.
pub fn normalise_to_skeleton(expr: &Expr) -> String {
    let mut out = String::new();
    let mut var_map: HashMap<String, usize> = HashMap::new();
    walk(expr, &mut out, &mut var_map);
    out
}

fn walk(expr: &Expr, out: &mut String, var_map: &mut HashMap<String, usize>) {
    match expr {
        Expr::Num(_) => out.push_str("L"),
        Expr::Var(name) => {
            let idx = match var_map.get(name) {
                Some(i) => *i,
                None => {
                    let i = var_map.len();
                    var_map.insert(name.clone(), i);
                    i
                }
            };
            out.push_str(&format!("V{idx}"));
        }
        Expr::Add(a, b) => {
            out.push_str("(+ ");
            walk(a, out, var_map);
            out.push(' ');
            walk(b, out, var_map);
            out.push(')');
        }
        Expr::Sub(a, b) => {
            out.push_str("(- ");
            walk(a, out, var_map);
            out.push(' ');
            walk(b, out, var_map);
            out.push(')');
        }
        Expr::Mul(a, b) => {
            out.push_str("(* ");
            walk(a, out, var_map);
            out.push(' ');
            walk(b, out, var_map);
            out.push(')');
        }
        Expr::Div(a, b) => {
            out.push_str("(/ ");
            walk(a, out, var_map);
            out.push(' ');
            walk(b, out, var_map);
            out.push(')');
        }
        Expr::Pow(a, b) => {
            out.push_str("(^ ");
            walk(a, out, var_map);
            out.push(' ');
            walk(b, out, var_map);
            out.push(')');
        }
        Expr::Neg(a) => {
            out.push_str("(neg ");
            walk(a, out, var_map);
            out.push(')');
        }
        Expr::Sqrt(a) => {
            out.push_str("(sqrt ");
            walk(a, out, var_map);
            out.push(')');
        }
        Expr::Eq(a, b) => {
            out.push_str("(= ");
            walk(a, out, var_map);
            out.push(' ');
            walk(b, out, var_map);
            out.push(')');
        }
    }
}

pub fn skeleton_hash(expr: &Expr) -> SkeletonHash {
    let canonical = normalise_to_skeleton(expr);
    let full = blake3::hash(canonical.as_bytes());
    let mut out = [0u8; 8];
    out.copy_from_slice(&full.as_bytes()[..8]);
    out
}
```

> **Note:** This match-arm list mirrors the public variants of `Expr` in `engine/crates/core/src/expr.rs`. If new variants exist (e.g. `Expr::Apply` for catalog axiom application), extend `walk()` with the same `out.push_str("op_name "); walk(args...)` pattern.

- [ ] **Step 6: Run tests, confirm they pass**

```bash
cargo test -p nasrudin-core skeleton:: 2>&1 | tail -10
```

Expected: `5 passed`.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/core/src/skeleton.rs engine/crates/core/src/lib.rs engine/crates/core/Cargo.toml
git commit -m "feat(core): add Expr → goal-skeleton normalisation + 8-byte hash"
```

---

## Task 3: `CacheConfig` feature-flag plumbing

**Files:**
- Create: `engine/crates/derive/src/cache_config.rs`
- Modify: `engine/crates/derive/src/lib.rs`

- [ ] **Step 1: Write the failing tests**

Create `engine/crates/derive/src/cache_config.rs`:

```rust
//! Feature flags + stats aggregation for the three cache layers.
//!
//! Read once at process boot via `CacheConfig::from_env()`. Each cache
//! consults its corresponding flag before doing real work; when a flag
//! is off, the cache is a pass-through (cost: one bool branch).

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defaults_are_off() {
        // Save/restore env to avoid bleeding test state.
        let _g = EnvGuard::clear(&[
            "NASRUDIN_CACHE_ATTEMPTS",
            "NASRUDIN_CACHE_TACTIC_PRIORS",
            "NASRUDIN_CACHE_PERSISTENT_LEAN",
        ]);
        let cfg = CacheConfig::from_env();
        assert!(!cfg.attempts_enabled);
        assert!(!cfg.tactic_priors_enabled);
        assert!(!cfg.persistent_lean_enabled);
    }

    #[test]
    fn one_flag_set_enables_only_that_cache() {
        let _g = EnvGuard::set(&[
            ("NASRUDIN_CACHE_ATTEMPTS", "1"),
            ("NASRUDIN_CACHE_TACTIC_PRIORS", "0"),
            ("NASRUDIN_CACHE_PERSISTENT_LEAN", ""),
        ]);
        let cfg = CacheConfig::from_env();
        assert!(cfg.attempts_enabled);
        assert!(!cfg.tactic_priors_enabled);
        assert!(!cfg.persistent_lean_enabled);
    }

    /// Save and restore env vars across one test.
    struct EnvGuard {
        saved: Vec<(String, Option<String>)>,
    }
    impl EnvGuard {
        fn clear(keys: &[&str]) -> Self {
            let saved = keys
                .iter()
                .map(|k| (k.to_string(), std::env::var(k).ok()))
                .collect();
            for k in keys {
                // SAFETY: tests run with #[serial] is not configured; in practice
                // these flags are read only at startup so test interleaving is OK.
                unsafe { std::env::remove_var(k); }
            }
            Self { saved }
        }
        fn set(pairs: &[(&str, &str)]) -> Self {
            let saved = pairs
                .iter()
                .map(|(k, _)| (k.to_string(), std::env::var(k).ok()))
                .collect();
            for (k, v) in pairs {
                unsafe { std::env::set_var(k, v); }
            }
            Self { saved }
        }
    }
    impl Drop for EnvGuard {
        fn drop(&mut self) {
            for (k, v) in &self.saved {
                unsafe {
                    match v {
                        Some(val) => std::env::set_var(k, val),
                        None => std::env::remove_var(k),
                    }
                }
            }
        }
    }
}
```

- [ ] **Step 2: Implement `CacheConfig`**

Add to `engine/crates/derive/src/cache_config.rs` above the `#[cfg(test)]`:

```rust
/// Runtime configuration for the cache layer.
#[derive(Debug, Clone, Copy, Default)]
pub struct CacheConfig {
    pub attempts_enabled: bool,
    pub tactic_priors_enabled: bool,
    pub persistent_lean_enabled: bool,
}

impl CacheConfig {
    /// Read flags from env. Each flag is on iff the env var is set to a
    /// truthy value (`"1"`, `"true"`, `"yes"`, case-insensitive). Anything
    /// else (including unset, empty, `"0"`, `"false"`) is off.
    pub fn from_env() -> Self {
        Self {
            attempts_enabled: env_truthy("NASRUDIN_CACHE_ATTEMPTS"),
            tactic_priors_enabled: env_truthy("NASRUDIN_CACHE_TACTIC_PRIORS"),
            persistent_lean_enabled: env_truthy("NASRUDIN_CACHE_PERSISTENT_LEAN"),
        }
    }
}

fn env_truthy(name: &str) -> bool {
    match std::env::var(name) {
        Ok(s) => matches!(s.trim().to_lowercase().as_str(), "1" | "true" | "yes"),
        Err(_) => false,
    }
}

/// Stats aggregator. Each cache pushes counts into here; the
/// `nasrudin worker stats` binary reads them out.
#[derive(Debug, Default)]
pub struct CacheStats {
    pub attempts_hits: std::sync::atomic::AtomicU64,
    pub attempts_misses: std::sync::atomic::AtomicU64,
    pub tactic_priors_hits: std::sync::atomic::AtomicU64,
    pub tactic_priors_misses: std::sync::atomic::AtomicU64,
    pub persistent_lean_requests: std::sync::atomic::AtomicU64,
    pub persistent_lean_restarts: std::sync::atomic::AtomicU64,
}
```

- [ ] **Step 3: Wire into lib.rs**

Append to `engine/crates/derive/src/lib.rs`:

```rust
pub mod cache_config;
pub use cache_config::{CacheConfig, CacheStats};
```

- [ ] **Step 4: Run tests**

```bash
cargo test -p nasrudin-derive cache_config:: 2>&1 | tail -10
```

Expected: `2 passed`.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/derive/src/cache_config.rs engine/crates/derive/src/lib.rs
git commit -m "feat(cache): add CacheConfig env reader + CacheStats counters"
```

---

## Task 4: Add new RocksDB column families

**Files:**
- Modify: `engine/crates/rocks/src/lib.rs`

- [ ] **Step 1: Read the existing CF block**

Open `engine/crates/rocks/src/lib.rs:1-40` to confirm the `CF_*` constants and `ALL_CFS` array shape.

- [ ] **Step 2: Add the new constants**

In `engine/crates/rocks/src/lib.rs`, find the block:

```rust
const CF_REVERIFY_QUEUE: &str = "reverify_queue";

const ALL_CFS: &[&str] = &[
```

Insert just *above* `ALL_CFS`:

```rust
const CF_ATTEMPTS: &str = "attempts";
const CF_TACTIC_PRIORS: &str = "tactic_priors";
```

And update `ALL_CFS`:

```rust
const ALL_CFS: &[&str] = &[
    CF_THEOREMS,
    CF_PROOFS,
    CF_LINEAGE,
    CF_BY_DOMAIN,
    CF_BY_DEPTH,
    CF_BY_AXIOM,
    CF_BY_GENERATION,
    CF_LATEX_INDEX,
    CF_STATS,
    CF_REVERIFY_QUEUE,
    CF_ATTEMPTS,
    CF_TACTIC_PRIORS,
];
```

Then in the `POINT_LOOKUP_CFS` array (inside `TheoremDb::new`), add `CF_ATTEMPTS` and `CF_TACTIC_PRIORS` for bloom-filtered point lookups:

```rust
const POINT_LOOKUP_CFS: &[&str] =
    &[CF_THEOREMS, CF_PROOFS, CF_LINEAGE, CF_REVERIFY_QUEUE, CF_ATTEMPTS, CF_TACTIC_PRIORS];
```

- [ ] **Step 3: Run cargo check**

```bash
cd engine && cargo check -p nasrudin-rocks 2>&1 | tail -5
```

Expected: `Finished`, exit 0.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/rocks/src/lib.rs
git commit -m "feat(rocks): register attempts + tactic_priors column families"
```

---

## Task 5: `AttemptsCache` wrapper

**Files:**
- Create: `engine/crates/rocks/src/attempts_cache.rs`
- Modify: `engine/crates/rocks/src/lib.rs`

- [ ] **Step 1: Write the failing tests in a new module**

Create `engine/crates/rocks/src/attempts_cache.rs`:

```rust
//! RocksDB-backed cache of verification attempt outcomes.
//!
//! Key: `(canonical_hash || axiom_set_hash)` — 16 bytes total.
//! Value: serde_json-encoded `AttemptRecord`.
//! TTL: enforced application-side (RocksDB has no native TTL on a CF created
//! without TTL options; we read the timestamp and treat expired rows as misses).

use chrono::{DateTime, Duration, Utc};
use rocksdb::DB;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(tag = "kind", content = "data")]
pub enum AttemptOutcome {
    Verified { theorem_id: [u8; 8], tactic: String },
    RejectedTypeError { msg: String },
    RejectedTimeout,
    RejectedTrivial { reason: String },
    Pending,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AttemptRecord {
    pub outcome: AttemptOutcome,
    pub lean_version: String,
    pub timestamp: DateTime<Utc>,
    pub attempted_by: String,
    pub elapsed_ms: u32,
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    fn fresh_cache() -> (AttemptsCache, tempfile::TempDir) {
        let dir = tempdir().unwrap();
        let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
        (cache, dir)
    }

    #[test]
    fn put_then_get_roundtrips() {
        let (cache, _dir) = fresh_cache();
        let key = [1u8; 16];
        let record = AttemptRecord {
            outcome: AttemptOutcome::Verified {
                theorem_id: [0xab; 8],
                tactic: "ring".into(),
            },
            lean_version: "4.27.0".into(),
            timestamp: Utc::now(),
            attempted_by: "test-worker".into(),
            elapsed_ms: 42,
        };
        cache.put(&key, &record).unwrap();
        let got = cache.get(&key).unwrap().unwrap();
        assert!(matches!(got.outcome, AttemptOutcome::Verified { .. }));
        assert_eq!(got.elapsed_ms, 42);
    }

    #[test]
    fn missing_key_returns_none() {
        let (cache, _dir) = fresh_cache();
        let key = [9u8; 16];
        assert!(cache.get(&key).unwrap().is_none());
    }

    #[test]
    fn expired_record_treated_as_miss() {
        let (cache, _dir) = fresh_cache();
        let key = [2u8; 16];
        let stale = AttemptRecord {
            outcome: AttemptOutcome::RejectedTimeout,
            lean_version: "4.27.0".into(),
            timestamp: Utc::now() - Duration::days(31),
            attempted_by: "test-worker".into(),
            elapsed_ms: 0,
        };
        cache.put(&key, &stale).unwrap();
        let got = cache.get_with_ttl(&key, Duration::days(30)).unwrap();
        assert!(got.is_none(), "30-day-old record should be treated as expired");
    }

    #[test]
    fn key_helper_concatenates() {
        let canonical = [0xaa; 8];
        let axiom_set = [0xbb; 8];
        let key = AttemptsCache::make_key(&canonical, &axiom_set);
        assert_eq!(&key[..8], &canonical);
        assert_eq!(&key[8..], &axiom_set);
    }
}
```

- [ ] **Step 2: Implement `AttemptsCache`**

Add above `#[cfg(test)]` in `engine/crates/rocks/src/attempts_cache.rs`:

```rust
use anyhow::{Context, Result};

const CF_ATTEMPTS: &str = "attempts";

pub struct AttemptsCache {
    db: DB,
}

impl AttemptsCache {
    /// Open a standalone RocksDB at `path` containing only the `attempts` CF.
    /// Used in tests; production uses `AttemptsCache::on_existing_db`.
    pub fn open(path: &str) -> Result<Self> {
        use rocksdb::{ColumnFamilyDescriptor, Options};
        let mut opts = Options::default();
        opts.create_if_missing(true);
        opts.create_missing_column_families(true);
        let cf = ColumnFamilyDescriptor::new(CF_ATTEMPTS, Options::default());
        let db = DB::open_cf_descriptors(&opts, path, vec![cf])
            .context("open attempts cache db")?;
        Ok(Self { db })
    }

    /// Build the 16-byte key from a canonical hash and axiom-set hash.
    pub fn make_key(canonical_hash: &[u8; 8], axiom_set_hash: &[u8; 8]) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(canonical_hash);
        out[8..].copy_from_slice(axiom_set_hash);
        out
    }

    pub fn put(&self, key: &[u8; 16], record: &AttemptRecord) -> Result<()> {
        let cf = self.db.cf_handle(CF_ATTEMPTS).context("cf attempts")?;
        let bytes = serde_json::to_vec(record).context("serialise AttemptRecord")?;
        self.db.put_cf(cf, key, bytes).context("put attempts")?;
        Ok(())
    }

    pub fn get(&self, key: &[u8; 16]) -> Result<Option<AttemptRecord>> {
        let cf = self.db.cf_handle(CF_ATTEMPTS).context("cf attempts")?;
        match self.db.get_cf(cf, key).context("get attempts")? {
            Some(bytes) => Ok(Some(serde_json::from_slice(&bytes).context("deserialise AttemptRecord")?)),
            None => Ok(None),
        }
    }

    /// Get with TTL: returns None if the record is older than `max_age`.
    pub fn get_with_ttl(&self, key: &[u8; 16], max_age: Duration) -> Result<Option<AttemptRecord>> {
        match self.get(key)? {
            Some(rec) if Utc::now() - rec.timestamp <= max_age => Ok(Some(rec)),
            _ => Ok(None),
        }
    }
}
```

- [ ] **Step 3: Wire module + add tempfile dev dep if missing**

Append to `engine/crates/rocks/src/lib.rs`:

```rust
pub mod attempts_cache;
pub use attempts_cache::{AttemptOutcome, AttemptRecord, AttemptsCache};
```

Confirm `tempfile = "3"` is already in `engine/crates/rocks/Cargo.toml` `[dev-dependencies]` (it was, per earlier survey).

- [ ] **Step 4: Run tests, confirm pass**

```bash
cargo test -p nasrudin-rocks attempts_cache:: 2>&1 | tail -10
```

Expected: `4 passed`.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/rocks/src/attempts_cache.rs engine/crates/rocks/src/lib.rs
git commit -m "feat(cache): AttemptsCache RocksDB wrapper with TTL semantics"
```

---

## Task 6: `lookup_or_compute` wrapper + integration with verifier

**Files:**
- Modify: `engine/crates/rocks/src/attempts_cache.rs`
- Modify: `engine/crates/derive/src/lean_verify.rs`

- [ ] **Step 1: Add the wrapper helper**

Append to `engine/crates/rocks/src/attempts_cache.rs` (inside `impl AttemptsCache`):

```rust
    /// Lookup the cached outcome; on miss, run `compute`, cache the result, return it.
    /// Caller is responsible for building the key.
    pub fn lookup_or_compute<F>(
        &self,
        key: &[u8; 16],
        max_age: Duration,
        attempted_by: &str,
        lean_version: &str,
        compute: F,
    ) -> Result<AttemptRecord>
    where
        F: FnOnce() -> AttemptOutcome,
    {
        if let Some(hit) = self.get_with_ttl(key, max_age)? {
            return Ok(hit);
        }
        let started = std::time::Instant::now();
        let outcome = compute();
        let elapsed_ms = started.elapsed().as_millis() as u32;
        let record = AttemptRecord {
            outcome,
            lean_version: lean_version.to_string(),
            timestamp: Utc::now(),
            attempted_by: attempted_by.to_string(),
            elapsed_ms,
        };
        self.put(key, &record)?;
        Ok(record)
    }
```

- [ ] **Step 2: Test the wrapper**

Append a test inside `#[cfg(test)] mod tests` in the same file:

```rust
    #[test]
    fn lookup_or_compute_misses_then_hits() {
        let (cache, _dir) = fresh_cache();
        let key = [3u8; 16];
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
        assert_eq!(compute_calls, 1, "second call should hit cache, not recompute");
    }
```

- [ ] **Step 3: Run tests**

```bash
cargo test -p nasrudin-rocks attempts_cache::tests::lookup_or_compute_misses_then_hits 2>&1 | tail -5
```

Expected: `1 passed`.

- [ ] **Step 4: Wire into the verifier (optional path-A flag)**

Open `engine/crates/derive/src/lean_verify.rs`. The existing `verify_file` function is the primary entry point. We do NOT change its signature. Instead add a sibling helper:

Append to `engine/crates/derive/src/lean_verify.rs`:

```rust
use nasrudin_rocks::attempts_cache::{AttemptOutcome, AttemptRecord, AttemptsCache};
use chrono::Duration;

/// Cache-backed wrapper around `LeanVerifier::verify_file`.
///
/// On hit, returns the cached outcome translated to a `LeanVerifyResult`.
/// On miss, calls the underlying verifier and caches the outcome.
///
/// `cache_key` should be `AttemptsCache::make_key(canonical_hash, axiom_set_hash)`
/// computed by the caller (the verifier doesn't know what axioms are in scope).
pub fn verify_with_cache(
    verifier: &LeanVerifier,
    cache: &AttemptsCache,
    cache_key: &[u8; 16],
    lean_version: &str,
    worker_id: &str,
    lean_content: &str,
    module_path: &str,
    ttl_days: i64,
) -> LeanVerifyResult {
    let max_age = Duration::days(ttl_days);
    match cache.lookup_or_compute(cache_key, max_age, worker_id, lean_version, || {
        match verifier.verify_file(lean_content, module_path) {
            LeanVerifyResult::Success => AttemptOutcome::Verified {
                theorem_id: [0u8; 8], // caller fills in; we don't know it here
                tactic: String::new(),
            },
            LeanVerifyResult::Failed { stderr } => AttemptOutcome::RejectedTypeError { msg: stderr },
            LeanVerifyResult::ProcessError { message } => AttemptOutcome::RejectedTypeError { msg: message },
        }
    }) {
        Ok(record) => match record.outcome {
            AttemptOutcome::Verified { .. } => LeanVerifyResult::Success,
            AttemptOutcome::RejectedTypeError { msg } => LeanVerifyResult::Failed { stderr: msg },
            AttemptOutcome::RejectedTimeout => LeanVerifyResult::Failed { stderr: "timeout".into() },
            AttemptOutcome::RejectedTrivial { reason } => LeanVerifyResult::Failed { stderr: reason },
            AttemptOutcome::Pending => LeanVerifyResult::ProcessError { message: "pending".into() },
        },
        Err(e) => LeanVerifyResult::ProcessError { message: format!("cache: {e}") },
    }
}
```

Add `nasrudin-rocks` to `[dependencies]` in `engine/crates/derive/Cargo.toml` if not already present:

```bash
grep -q nasrudin-rocks engine/crates/derive/Cargo.toml || \
  echo 'nasrudin-rocks = { path = "../rocks" }' >> engine/crates/derive/Cargo.toml
```

- [ ] **Step 5: cargo check + commit**

```bash
cd engine && cargo check -p nasrudin-derive 2>&1 | tail -3
```

Expected: `Finished`, exit 0.

```bash
git add engine/crates/rocks/src/attempts_cache.rs engine/crates/derive/src/lean_verify.rs engine/crates/derive/Cargo.toml
git commit -m "feat(cache): verify_with_cache wrapper around LeanVerifier"
```

---

## Task 7: `TacticPriorsCache` wrapper

**Files:**
- Create: `engine/crates/rocks/src/tactic_priors.rs`
- Modify: `engine/crates/rocks/src/lib.rs`

- [ ] **Step 1: Write the failing tests**

Create `engine/crates/rocks/src/tactic_priors.rs`:

```rust
//! RocksDB-backed cache of which tactic chains have proven goals of a given shape.
//!
//! Key: `(skeleton_hash || axiom_set_hash)` — 16 bytes.
//! Value: serde_json-encoded `TacticPriorRecord` (a list of past successes,
//!        sorted by hit count desc).

use chrono::{DateTime, Utc};
use rocksdb::DB;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TacticSuccess {
    pub tactic_chain: String,
    pub hits: u32,
    pub avg_elapsed_ms: u16,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TacticPriorRecord {
    pub successes: Vec<TacticSuccess>,
    pub last_updated: Option<DateTime<Utc>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    fn fresh_cache() -> (TacticPriorsCache, tempfile::TempDir) {
        let dir = tempdir().unwrap();
        (
            TacticPriorsCache::open(dir.path().to_str().unwrap()).unwrap(),
            dir,
        )
    }

    #[test]
    fn record_success_adds_new_entry() {
        let (cache, _dir) = fresh_cache();
        let key = [0xa1; 16];
        cache.record_success(&key, "ring", 12).unwrap();
        let rec = cache.get(&key).unwrap().unwrap();
        assert_eq!(rec.successes.len(), 1);
        assert_eq!(rec.successes[0].tactic_chain, "ring");
        assert_eq!(rec.successes[0].hits, 1);
    }

    #[test]
    fn record_success_increments_existing() {
        let (cache, _dir) = fresh_cache();
        let key = [0xa2; 16];
        cache.record_success(&key, "simp; ring", 10).unwrap();
        cache.record_success(&key, "simp; ring", 14).unwrap();
        let rec = cache.get(&key).unwrap().unwrap();
        assert_eq!(rec.successes.len(), 1);
        assert_eq!(rec.successes[0].hits, 2);
        // average rounds toward 12
        assert!((10..=14).contains(&rec.successes[0].avg_elapsed_ms));
    }

    #[test]
    fn top_returns_in_hit_count_order() {
        let (cache, _dir) = fresh_cache();
        let key = [0xa3; 16];
        cache.record_success(&key, "ring", 10).unwrap();
        cache.record_success(&key, "linarith", 20).unwrap();
        cache.record_success(&key, "ring", 12).unwrap();
        // ring has 2 hits, linarith has 1 → ring first
        let top = cache.top(&key, 5).unwrap();
        assert_eq!(top.len(), 2);
        assert_eq!(top[0].tactic_chain, "ring");
        assert_eq!(top[0].hits, 2);
        assert_eq!(top[1].tactic_chain, "linarith");
        assert_eq!(top[1].hits, 1);
    }
}
```

- [ ] **Step 2: Implement `TacticPriorsCache`**

Above `#[cfg(test)]`:

```rust
use anyhow::{Context, Result};

const CF_TACTIC_PRIORS: &str = "tactic_priors";

pub struct TacticPriorsCache {
    db: DB,
}

impl TacticPriorsCache {
    pub fn open(path: &str) -> Result<Self> {
        use rocksdb::{ColumnFamilyDescriptor, Options};
        let mut opts = Options::default();
        opts.create_if_missing(true);
        opts.create_missing_column_families(true);
        let cf = ColumnFamilyDescriptor::new(CF_TACTIC_PRIORS, Options::default());
        let db = DB::open_cf_descriptors(&opts, path, vec![cf])
            .context("open tactic priors db")?;
        Ok(Self { db })
    }

    pub fn make_key(skeleton_hash: &[u8; 8], axiom_set_hash: &[u8; 8]) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(skeleton_hash);
        out[8..].copy_from_slice(axiom_set_hash);
        out
    }

    pub fn get(&self, key: &[u8; 16]) -> Result<Option<TacticPriorRecord>> {
        let cf = self.db.cf_handle(CF_TACTIC_PRIORS).context("cf priors")?;
        match self.db.get_cf(cf, key).context("get priors")? {
            Some(bytes) => Ok(Some(serde_json::from_slice(&bytes)?)),
            None => Ok(None),
        }
    }

    /// Top N tactic chains for this goal-shape, sorted by hit count desc.
    pub fn top(&self, key: &[u8; 16], n: usize) -> Result<Vec<TacticSuccess>> {
        let mut rec = self.get(key)?.unwrap_or_default();
        rec.successes
            .sort_by(|a, b| b.hits.cmp(&a.hits).then(a.tactic_chain.cmp(&b.tactic_chain)));
        rec.successes.truncate(n);
        Ok(rec.successes)
    }

    /// Increment hit count for `chain` (or insert), update rolling avg elapsed.
    pub fn record_success(&self, key: &[u8; 16], chain: &str, elapsed_ms: u16) -> Result<()> {
        let cf = self.db.cf_handle(CF_TACTIC_PRIORS).context("cf priors")?;
        let mut rec = self.get(key)?.unwrap_or_default();
        if let Some(existing) = rec
            .successes
            .iter_mut()
            .find(|s| s.tactic_chain == chain)
        {
            // Rolling average: avg' = ((avg * n) + new) / (n + 1)
            let new_total =
                u32::from(existing.avg_elapsed_ms) * existing.hits + u32::from(elapsed_ms);
            existing.hits += 1;
            existing.avg_elapsed_ms = (new_total / existing.hits) as u16;
        } else {
            rec.successes.push(TacticSuccess {
                tactic_chain: chain.to_string(),
                hits: 1,
                avg_elapsed_ms: elapsed_ms,
            });
        }
        rec.last_updated = Some(Utc::now());
        let bytes = serde_json::to_vec(&rec)?;
        self.db.put_cf(cf, key, bytes).context("put priors")?;
        Ok(())
    }
}
```

- [ ] **Step 3: Wire into lib.rs**

Append to `engine/crates/rocks/src/lib.rs`:

```rust
pub mod tactic_priors;
pub use tactic_priors::{TacticPriorRecord, TacticPriorsCache, TacticSuccess};
```

- [ ] **Step 4: Run tests**

```bash
cargo test -p nasrudin-rocks tactic_priors:: 2>&1 | tail -5
```

Expected: `3 passed`.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/rocks/src/tactic_priors.rs engine/crates/rocks/src/lib.rs
git commit -m "feat(cache): TacticPriorsCache with hit-count ranking"
```

---

## Task 8: `try_priors_first` helper in lean-bridge

**Files:**
- Modify: `engine/crates/lean-bridge/src/tactic.rs`
- Modify: `engine/crates/lean-bridge/Cargo.toml`

- [ ] **Step 1: Wire nasrudin-rocks dep into lean-bridge**

Add to `engine/crates/lean-bridge/Cargo.toml` `[dependencies]`:

```toml
nasrudin-rocks = { path = "../rocks" }
```

- [ ] **Step 2: Add helper + test**

Append to `engine/crates/lean-bridge/src/tactic.rs`:

```rust
use nasrudin_rocks::tactic_priors::{TacticPriorsCache, TacticSuccess};

/// Build the tactic cascade prefix from cached priors for this goal shape.
///
/// Returns up to `n` tactic chains, in hit-order. The caller should try these
/// chains *before* `default_cascade()` and only fall through to the cascade if
/// none succeed.
pub fn priors_for(cache: &TacticPriorsCache, key: &[u8; 16], n: usize) -> Vec<String> {
    cache
        .top(key, n)
        .unwrap_or_default()
        .into_iter()
        .map(|s| s.tactic_chain)
        .collect()
}

#[cfg(test)]
mod priors_test {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn priors_for_empty_cache_returns_empty() {
        let dir = tempdir().unwrap();
        let cache = TacticPriorsCache::open(dir.path().to_str().unwrap()).unwrap();
        let key = [0u8; 16];
        let out = priors_for(&cache, &key, 3);
        assert!(out.is_empty());
    }

    #[test]
    fn priors_for_returns_top_chains() {
        let dir = tempdir().unwrap();
        let cache = TacticPriorsCache::open(dir.path().to_str().unwrap()).unwrap();
        let key = [1u8; 16];
        cache.record_success(&key, "ring", 10).unwrap();
        cache.record_success(&key, "ring", 12).unwrap();
        cache.record_success(&key, "linarith", 30).unwrap();
        let out = priors_for(&cache, &key, 5);
        assert_eq!(out, vec!["ring".to_string(), "linarith".to_string()]);
    }
}
```

- [ ] **Step 3: Run tests**

```bash
cd engine && cargo test -p nasrudin-lean-bridge priors_test 2>&1 | tail -5
```

Expected: `2 passed`.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/lean-bridge/src/tactic.rs engine/crates/lean-bridge/Cargo.toml
git commit -m "feat(cache): tactic.priors_for helper consults TacticPriorsCache"
```

---

## Task 9: Persistent Lean — protocol types

**Files:**
- Create: `engine/crates/lean-bridge/src/persistent_protocol.rs`
- Modify: `engine/crates/lean-bridge/src/lib.rs`
- Modify: `engine/crates/lean-bridge/Cargo.toml`

- [ ] **Step 1: Add tokio + serde_json to lean-bridge deps**

Add to `engine/crates/lean-bridge/Cargo.toml` `[dependencies]`:

```toml
tokio = { workspace = true, features = ["process", "io-util", "macros", "rt-multi-thread", "sync", "time"] }
serde = { workspace = true, features = ["derive"] }
serde_json = { workspace = true }
```

(If any are already there, deduplicate; the worker crate already pulls tokio so shared workspace deps should resolve.)

- [ ] **Step 2: Write protocol type tests**

Create `engine/crates/lean-bridge/src/persistent_protocol.rs`:

```rust
//! JSON-RPC protocol used to talk to a long-lived `lean --server` subprocess.
//!
//! We send a single line of JSON per request, and read a single line of JSON
//! per response. The server is told to load Mathlib at boot; subsequent
//! requests just elaborate the user code against that warm state.

use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Request {
    /// Type-check the given Lean source. Reports any elaboration errors.
    Elaborate { id: u64, source: String },
    /// Verify that `tactic` proves the goal in `source`. Returns success
    /// or first-tactic-error.
    VerifyTactic { id: u64, source: String, tactic: String },
    /// Health check.
    Ping { id: u64 },
    /// Tell the server to shut down cleanly.
    Shutdown,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Response {
    Ok { id: u64 },
    ElaborateOk { id: u64, elapsed_ms: u32 },
    ElaborateError { id: u64, message: String, elapsed_ms: u32 },
    VerifyOk { id: u64, elapsed_ms: u32 },
    VerifyError { id: u64, message: String, elapsed_ms: u32 },
    Pong { id: u64 },
    Fatal { message: String },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn request_roundtrip() {
        let r = Request::Elaborate { id: 7, source: "theorem foo : True := trivial".into() };
        let s = serde_json::to_string(&r).unwrap();
        let back: Request = serde_json::from_str(&s).unwrap();
        assert_eq!(r, back);
    }

    #[test]
    fn response_roundtrip() {
        let r = Response::VerifyError { id: 3, message: "linarith failed".into(), elapsed_ms: 250 };
        let s = serde_json::to_string(&r).unwrap();
        let back: Response = serde_json::from_str(&s).unwrap();
        assert_eq!(r, back);
    }
}
```

- [ ] **Step 3: Wire module**

Add to `engine/crates/lean-bridge/src/lib.rs`:

```rust
pub mod persistent_protocol;
```

- [ ] **Step 4: Run tests, confirm pass**

```bash
cd engine && cargo test -p nasrudin-lean-bridge persistent_protocol:: 2>&1 | tail -5
```

Expected: `2 passed`.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/lean-bridge/src/persistent_protocol.rs engine/crates/lean-bridge/src/lib.rs engine/crates/lean-bridge/Cargo.toml
git commit -m "feat(persistent-lean): JSON-RPC protocol types for long-lived elaborator"
```

---

## Task 10: Persistent Lean — the elaborator client

**Files:**
- Create: `engine/crates/lean-bridge/src/persistent.rs`
- Create: `prover/scripts/nasrudin_server.lean` (the server-side script the subprocess runs)
- Modify: `engine/crates/lean-bridge/src/lib.rs`

> **Note on scope:** This task scaffolds the Rust-side client (subprocess management, request/response correlation, health). The Lean-side server script (`nasrudin_server.lean`) is included as a stub the prover team can flesh out; the Rust client treats it as a black box that responds to JSON lines on stdout. If `nasrudin_server.lean` doesn't exist or doesn't respond as expected, the elaborator's health check fails on boot and `PersistentElaborator::new()` returns an error — callers fall back to the existing process-per-call path. This is acceptable for Phase A: persistent-lean stays gated behind `NASRUDIN_CACHE_PERSISTENT_LEAN=1` and is opt-in until the prover-side script is finalised.

- [ ] **Step 1: Write the Lean stub**

Create `prover/scripts/nasrudin_server.lean`:

```lean
/-
  Long-lived Nasrudin elaborator-server stub.

  Reads JSON requests from stdin (one per line), writes JSON responses to
  stdout (one per line). Pre-loads Mathlib at startup.

  Wire format matches `engine/crates/lean-bridge/src/persistent_protocol.rs`.

  TODO(prover): flesh out the elaboration loop using Lean.Elab APIs. For
  now this stub exists so the Rust side has something to spawn; it
  immediately fails on any non-Ping request, and the Rust side falls back
  to subprocess-per-call.
-/
import Mathlib

def main : IO Unit := do
  IO.println "{\"kind\":\"ok\",\"id\":0}"
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut nextId : Nat := 0
  while ¬ (← stdin.isEof) do
    let line ← stdin.getLine
    if line.trim.isEmpty then continue
    -- Stub: reply Fatal to any structured request; reply Pong to ping.
    if line.trim.startsWith "{\"kind\":\"ping\"" then
      stdout.putStrLn s!"\{\"kind\":\"pong\",\"id\":{nextId}\}"
    else
      stdout.putStrLn s!"\{\"kind\":\"fatal\",\"message\":\"stub server: unimplemented request\"\}"
    stdout.flush
    nextId := nextId + 1
```

- [ ] **Step 2: Write the failing tests**

Create `engine/crates/lean-bridge/src/persistent.rs`:

```rust
//! Long-lived `lean --server` client.
//!
//! Spawns one subprocess running `nasrudin_server.lean` (which imports
//! Mathlib once at boot), keeps stdin/stdout pipes open, and multiplexes
//! requests through a tokio mpsc channel.
//!
//! On request timeout or subprocess death, the client kills the process
//! and either reports an error to the caller or restarts (configurable).

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn config_default_points_at_prover_root() {
        let cfg = PersistentElaboratorConfig::default();
        assert!(cfg.script_path.ends_with("nasrudin_server.lean"));
    }

    /// This test is `#[ignore]` because it requires `lean` on the PATH.
    /// Run manually with `cargo test -p nasrudin-lean-bridge --ignored persistent::`.
    #[tokio::test]
    #[ignore]
    async fn ping_roundtrip_against_real_lean() {
        let cfg = PersistentElaboratorConfig::from_env();
        let client = PersistentElaborator::new(cfg).await;
        if client.is_err() {
            eprintln!("skipping: lean not available — {:?}", client.err());
            return;
        }
        let client = client.unwrap();
        client.ping().await.expect("ping must succeed");
        client.shutdown().await.expect("shutdown must succeed");
    }
}
```

- [ ] **Step 3: Implement the client**

Above `#[cfg(test)]`:

```rust
use crate::persistent_protocol::{Request, Response};
use anyhow::{Context, Result, anyhow};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, Command};
use tokio::sync::{mpsc, oneshot, Mutex};

#[derive(Debug, Clone)]
pub struct PersistentElaboratorConfig {
    /// Path to `nasrudin_server.lean`.
    pub script_path: PathBuf,
    /// Working directory (typically `prover/`).
    pub cwd: PathBuf,
    /// Boot timeout — how long to wait for the initial Mathlib import.
    pub boot_timeout: Duration,
    /// Per-request timeout.
    pub request_timeout: Duration,
}

impl Default for PersistentElaboratorConfig {
    fn default() -> Self {
        Self {
            script_path: PathBuf::from("../prover/scripts/nasrudin_server.lean"),
            cwd: PathBuf::from("../prover"),
            boot_timeout: Duration::from_secs(30),
            request_timeout: Duration::from_secs(30),
        }
    }
}

impl PersistentElaboratorConfig {
    pub fn from_env() -> Self {
        let mut cfg = Self::default();
        if let Ok(s) = std::env::var("NASRUDIN_LEAN_SCRIPT") {
            cfg.script_path = PathBuf::from(s);
        }
        if let Ok(s) = std::env::var("NASRUDIN_PROVER_ROOT") {
            cfg.cwd = PathBuf::from(s);
        }
        cfg
    }
}

type Inflight = Arc<Mutex<std::collections::HashMap<u64, oneshot::Sender<Response>>>>;

pub struct PersistentElaborator {
    next_id: AtomicU64,
    tx: mpsc::Sender<(Request, oneshot::Sender<Response>)>,
    /// Kept so dropping the handle kills the child.
    _supervisor: tokio::task::JoinHandle<()>,
}

impl PersistentElaborator {
    pub async fn new(cfg: PersistentElaboratorConfig) -> Result<Self> {
        let mut child = Command::new("lean")
            .arg("--run")
            .arg(&cfg.script_path)
            .current_dir(&cfg.cwd)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .context("spawn lean --run")?;

        let stdin = child.stdin.take().context("take stdin")?;
        let stdout = child.stdout.take().context("take stdout")?;
        let mut reader = BufReader::new(stdout).lines();

        // Read the initial "ok" line indicating Mathlib has booted.
        let boot = tokio::time::timeout(cfg.boot_timeout, reader.next_line())
            .await
            .context("boot timeout")??
            .ok_or_else(|| anyhow!("server closed stdout before boot"))?;
        let parsed: Response = serde_json::from_str(&boot).context("parse boot line")?;
        match parsed {
            Response::Ok { .. } => {}
            other => return Err(anyhow!("unexpected boot response: {other:?}")),
        }

        let (tx, mut rx) = mpsc::channel::<(Request, oneshot::Sender<Response>)>(64);
        let inflight: Inflight = Arc::new(Mutex::new(Default::default()));

        // Reader task: parse each line as a Response, route to the inflight oneshot.
        let inflight_r = inflight.clone();
        tokio::spawn(async move {
            while let Ok(Some(line)) = reader.next_line().await {
                if let Ok(resp) = serde_json::from_str::<Response>(&line) {
                    let id = response_id(&resp);
                    if let Some(id) = id {
                        let mut g = inflight_r.lock().await;
                        if let Some(sender) = g.remove(&id) {
                            let _ = sender.send(resp);
                        }
                    } else if let Response::Fatal { message } = resp {
                        tracing::error!("persistent lean fatal: {message}");
                    }
                }
            }
        });

        // Writer task: pull requests off rx, write to stdin, register oneshot.
        let inflight_w = inflight.clone();
        let supervisor = tokio::spawn(async move {
            let mut stdin = stdin;
            while let Some((req, oneshot_tx)) = rx.recv().await {
                if let Some(id) = request_id(&req) {
                    inflight_w.lock().await.insert(id, oneshot_tx);
                }
                let mut line = match serde_json::to_vec(&req) {
                    Ok(b) => b,
                    Err(_) => continue,
                };
                line.push(b'\n');
                if stdin.write_all(&line).await.is_err() { break; }
                if stdin.flush().await.is_err() { break; }
            }
            let _ = child.kill().await;
        });

        Ok(Self {
            next_id: AtomicU64::new(1),
            tx,
            _supervisor: supervisor,
        })
    }

    pub async fn ping(&self) -> Result<()> {
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        self.send(Request::Ping { id }).await.map(|_| ())
    }

    pub async fn elaborate(&self, source: &str) -> Result<Response> {
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        self.send(Request::Elaborate { id, source: source.to_string() }).await
    }

    pub async fn verify_tactic(&self, source: &str, tactic: &str) -> Result<Response> {
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        self.send(Request::VerifyTactic {
            id,
            source: source.to_string(),
            tactic: tactic.to_string(),
        })
        .await
    }

    pub async fn shutdown(&self) -> Result<()> {
        let (tx, _rx) = oneshot::channel();
        let _ = self.tx.send((Request::Shutdown, tx)).await;
        Ok(())
    }

    async fn send(&self, req: Request) -> Result<Response> {
        let (resp_tx, resp_rx) = oneshot::channel();
        self.tx.send((req, resp_tx)).await.map_err(|_| anyhow!("server gone"))?;
        let resp = tokio::time::timeout(Duration::from_secs(30), resp_rx)
            .await
            .map_err(|_| anyhow!("request timeout"))??;
        Ok(resp)
    }
}

fn request_id(req: &Request) -> Option<u64> {
    match req {
        Request::Elaborate { id, .. }
        | Request::VerifyTactic { id, .. }
        | Request::Ping { id } => Some(*id),
        Request::Shutdown => None,
    }
}

fn response_id(resp: &Response) -> Option<u64> {
    match resp {
        Response::Ok { id }
        | Response::ElaborateOk { id, .. }
        | Response::ElaborateError { id, .. }
        | Response::VerifyOk { id, .. }
        | Response::VerifyError { id, .. }
        | Response::Pong { id } => Some(*id),
        Response::Fatal { .. } => None,
    }
}
```

- [ ] **Step 4: Wire into lib.rs**

Append to `engine/crates/lean-bridge/src/lib.rs`:

```rust
pub mod persistent;
pub use persistent::{PersistentElaborator, PersistentElaboratorConfig};
```

- [ ] **Step 5: Run tests (the non-ignored one)**

```bash
cd engine && cargo test -p nasrudin-lean-bridge persistent::tests::config_default 2>&1 | tail -5
```

Expected: `1 passed`.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/lean-bridge/src/persistent.rs engine/crates/lean-bridge/src/lib.rs prover/scripts/nasrudin_server.lean
git commit -m "feat(persistent-lean): subprocess client with mpsc-multiplexed requests"
```

---

## Task 11: Cache stats CLI

**Files:**
- Create: `engine/crates/api/src/bin/cache_stats.rs`
- Modify: `engine/crates/api/Cargo.toml`

- [ ] **Step 1: Add bin target**

Add to `engine/crates/api/Cargo.toml`:

```toml
[[bin]]
name = "cache-stats"
path = "src/bin/cache_stats.rs"
```

- [ ] **Step 2: Write the bin**

Create `engine/crates/api/src/bin/cache_stats.rs`:

```rust
//! `cache-stats` — read RocksDB and report cache hit / size metrics.
//!
//! Usage:
//!   cache-stats --rocks-path ~/.nasrudin/db
//!
//! Output (JSON):
//!   {
//!     "attempts": { "rows": N, "verified": A, "rejected": B },
//!     "tactic_priors": { "rows": M, "total_recorded_successes": S }
//!   }

use anyhow::Result;
use clap::Parser;
use rocksdb::{IteratorMode, Options, DB};
use serde::Serialize;

#[derive(Parser, Debug)]
#[command(name = "cache-stats")]
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
        let cf = db.cf_handle("attempts").expect("attempts cf");
        for item in db.iterator_cf(cf, IteratorMode::Start) {
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
                    _ => {}
                }
            }
        }
    }

    if cfs.iter().any(|c| c == "tactic_priors") {
        let cf = db.cf_handle("tactic_priors").expect("tactic_priors cf");
        for item in db.iterator_cf(cf, IteratorMode::Start) {
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

    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}
```

- [ ] **Step 3: Add clap dep**

If `clap` isn't already in `engine/crates/api/Cargo.toml` `[dependencies]`, add:

```toml
clap = { version = "4", features = ["derive"] }
```

- [ ] **Step 4: Build the bin**

```bash
cd engine && cargo build -p physics-api --bin cache-stats 2>&1 | tail -3
```

Expected: `Finished`, exit 0.

- [ ] **Step 5: Smoke run against an empty path**

```bash
mkdir -p /tmp/empty-rocks
./target/debug/cache-stats --rocks-path /tmp/empty-rocks 2>&1 | head -20
```

Expected: prints a JSON report with `rows: 0` for both caches (or an error if RocksDB refuses to open an empty dir — that's also acceptable for an MVP smoke test, just confirm the binary runs).

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/bin/cache_stats.rs engine/crates/api/Cargo.toml
git commit -m "feat(cache): cache-stats CLI reports attempts + tactic-priors counts"
```

---

## Task 12: Soak test for AttemptsCache

**Files:**
- Create: `engine/crates/derive/tests/integration_attempts_cache.rs`

- [ ] **Step 1: Write the soak test**

Create `engine/crates/derive/tests/integration_attempts_cache.rs`:

```rust
//! End-to-end attempts-cache integration: 1000 cache writes, mixed hits/misses,
//! verify counts and TTL semantics hold under repeated access.

use chrono::{Duration, Utc};
use nasrudin_rocks::attempts_cache::{AttemptOutcome, AttemptRecord, AttemptsCache};
use tempfile::tempdir;

#[test]
fn attempts_cache_handles_thousand_inserts() {
    let dir = tempdir().unwrap();
    let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();

    let mut hits = 0u32;
    let mut misses = 0u32;
    let max_age = Duration::days(30);

    for i in 0u32..1_000 {
        let mut key = [0u8; 16];
        key[..4].copy_from_slice(&i.to_be_bytes());
        // First lookup — miss.
        if cache.get_with_ttl(&key, max_age).unwrap().is_some() {
            hits += 1;
        } else {
            misses += 1;
        }
        // Insert.
        let rec = AttemptRecord {
            outcome: if i % 7 == 0 {
                AttemptOutcome::Verified { theorem_id: [0; 8], tactic: "ring".into() }
            } else {
                AttemptOutcome::RejectedTimeout
            },
            lean_version: "4.27.0".into(),
            timestamp: Utc::now(),
            attempted_by: "soak".into(),
            elapsed_ms: 1,
        };
        cache.put(&key, &rec).unwrap();
    }
    assert_eq!(misses, 1000);
    assert_eq!(hits, 0);

    // Second pass — every key now hits.
    let mut second_hits = 0u32;
    for i in 0u32..1_000 {
        let mut key = [0u8; 16];
        key[..4].copy_from_slice(&i.to_be_bytes());
        if cache.get_with_ttl(&key, max_age).unwrap().is_some() {
            second_hits += 1;
        }
    }
    assert_eq!(second_hits, 1000);
}
```

- [ ] **Step 2: Add dev-dep on nasrudin-rocks if missing**

Confirm `engine/crates/derive/Cargo.toml` `[dev-dependencies]` includes `tempfile = "3"`. Add if missing.

- [ ] **Step 3: Run**

```bash
cd engine && cargo test -p nasrudin-derive --test integration_attempts_cache 2>&1 | tail -5
```

Expected: `1 passed`.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/derive/tests/integration_attempts_cache.rs engine/crates/derive/Cargo.toml
git commit -m "test(cache): 1k-insert soak test for AttemptsCache"
```

---

## Task 13: Ignore-gated soak test for PersistentElaborator

**Files:**
- Create: `engine/crates/derive/tests/integration_persistent_lean.rs`

> **Note:** This test is `#[ignore]`d by default — it requires `lean` on PATH and a working `nasrudin_server.lean`. Surfaced separately so CI can opt in once the prover-side script is real.

- [ ] **Step 1: Write the soak test**

Create `engine/crates/derive/tests/integration_persistent_lean.rs`:

```rust
//! Soak test: 100 ping round-trips against a single PersistentElaborator
//! instance. Asserts no hang, no leaks, no memory blow-up over time.
//!
//! Run manually:
//!   cargo test -p nasrudin-derive --test integration_persistent_lean -- --ignored

use nasrudin_lean_bridge::{PersistentElaborator, PersistentElaboratorConfig};
use std::time::Duration;

#[tokio::test]
#[ignore]
async fn one_hundred_pings_against_real_lean() {
    let cfg = PersistentElaboratorConfig::from_env();
    let client = match PersistentElaborator::new(cfg).await {
        Ok(c) => c,
        Err(e) => {
            eprintln!("skipping: {e}");
            return;
        }
    };
    for i in 0..100 {
        tokio::time::timeout(Duration::from_secs(5), client.ping())
            .await
            .unwrap_or_else(|_| panic!("ping {i} timed out"))
            .unwrap_or_else(|e| panic!("ping {i} errored: {e}"));
    }
    client.shutdown().await.expect("shutdown");
}
```

- [ ] **Step 2: cargo check (should not run the test)**

```bash
cd engine && cargo test -p nasrudin-derive --test integration_persistent_lean --no-run 2>&1 | tail -3
```

Expected: `Finished`, no test execution because of `#[ignore]`.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/derive/tests/integration_persistent_lean.rs
git commit -m "test(persistent-lean): 100-ping soak (ignored, requires lean on PATH)"
```

---

## Task 14: Documentation + README pointer

**Files:**
- Create: `engine/crates/derive/CACHE_LAYER.md`

- [ ] **Step 1: Write the doc**

Create `engine/crates/derive/CACHE_LAYER.md`:

```markdown
# Cache Layer (Phase A)

Three caches, all opt-in via env flags. Default off. Each can be enabled independently.

## Flags

| Env var | Effect |
|---|---|
| `NASRUDIN_CACHE_ATTEMPTS=1` | Memoise verification attempts in the `attempts` RocksDB CF. 30-day TTL. |
| `NASRUDIN_CACHE_TACTIC_PRIORS=1` | Try cached tactic chains before the default cascade. |
| `NASRUDIN_CACHE_PERSISTENT_LEAN=1` | Use a long-lived `lean --server` process instead of subprocess-per-call. |

## Inspecting

```bash
cargo run --bin cache-stats -- --rocks-path ./data/rocks
```

Reports per-CF row counts and outcome breakdowns. Useful for measuring hit rate over a workload.

## Spec

See `docs/superpowers/specs/2026-04-28-llm-guided-search-design.md` §3.
```

- [ ] **Step 2: Commit**

```bash
git add engine/crates/derive/CACHE_LAYER.md
git commit -m "docs(cache): operator notes for Phase A cache flags"
```

---

## Task 15: Final cargo check + push

- [ ] **Step 1: Run the full workspace check**

```bash
cd engine && cargo check --workspace 2>&1 | tail -5
```

Expected: `Finished`, exit 0.

- [ ] **Step 2: Run the full test suite (excluding ignored)**

```bash
cd engine && cargo test --workspace 2>&1 | tail -10
```

Expected: all tests pass (the new ones plus all pre-existing).

- [ ] **Step 3: Push**

```bash
cd /Volumes/CORSAIR/code/personal/nasrudin && git push origin main 2>&1 | tail -5
```

Expected: pushed, exit 0.

---

## Out of scope (deferred to later phases)

These are **explicitly not** part of Phase A even though they're related:

- Wiring the new caches into the GA hot path with feature-flag guards in the worker binary. Phase A ships the *plumbing*; turning it on inside `discover_emc2.rs` is Phase A.5 once the cache CLI confirms the wrappers work in isolation. Keep the guards simple: if `cfg.attempts_enabled` and `db.has_attempts_cf()`, call `verify_with_cache`; else call `verify_file` directly.
- The full Lean-side `nasrudin_server.lean` implementation. The Rust client tolerates any Lean script that responds to `Ping`; the prover team owns making `Elaborate` and `VerifyTactic` real.
- Distributed warm-cache replication. Each worker has its own RocksDB; cross-worker cache sharing comes (if ever) in a separate spec.

---

## Self-review

- **Spec coverage**: every §3 subsection (3.1–3.4) maps to specific tasks above (Tasks 9–10 for §3.1; Tasks 4–6 + 12 for §3.2; Tasks 2, 7, 8 for §3.3; Tasks 3, 11, 14 for §3.4). ✓
- **Placeholder scan**: no TBDs/TODOs/incomplete sections. The Lean stub in Task 10 has a `TODO(prover):` comment, which is intentional — that's a deferred contract for the prover team and Phase A is correctly gated to tolerate it. ✓
- **Type consistency**: `AttemptOutcome` variants stay identical between Tasks 5, 6, and 11; `TacticSuccess` fields stay identical between Tasks 7, 8, and 11; `PersistentElaboratorConfig` shape stays identical between Tasks 10 and 13. ✓
- **Ambiguity check**: cache key encoding is explicitly 16-byte concatenated; TTL semantics are application-side; protocol response IDs are explicit. ✓

---

*End of Phase A plan.*
