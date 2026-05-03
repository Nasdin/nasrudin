# Derivation Acyclicity & Cached Dependency Tracking — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prevent circular derivations — when deriving a target theorem `T`, the engine must exclude `T` itself and any theorem whose proof transitively cites `T` from the available premise set. Cache the dependency closure in RocksDB so the GA hot path doesn't recompute it.

**Architecture:**
1. Compute the transitive axiom-ancestor set at theorem-write time and cache it in the existing dormant `LineageRecord.axiom_ancestors` field.
2. Mirror the dependency edges in a new `CF_REVERSE_DEPS` column family keyed `ancestor_id || dependent_id` for O(prefix-scan) "what depends on X?" lookups.
3. Wrap `forbidden_for_target()` in a per-process LRU so the GA's repeated calls within a generation don't pay the RocksDB round-trip.
4. Expose `AxiomStore::iter_excluding(&forbidden)` so strategies and the GA selection path filter premises against the set.
5. Provide an idempotent backfill migration so the existing production RocksDB picks up the new fields without a wipe.

**Tech Stack:** Rust, RocksDB (via `rocksdb` crate, column-family writes through `WriteBatch`), `lru` crate (already used by `AxiomStore` cold tier), `serde_json` (existing serialization for lineage records).

---

## File Structure

| File | Responsibility | Status |
|---|---|---|
| `engine/crates/rocks/src/lib.rs` | `CF_REVERSE_DEPS` constant, modified `put_theorem`, new `forbidden_for_target`, `list_dependents`, `backfill_lineage_and_reverse_deps`, in-process LRU field | modify |
| `engine/crates/rocks/src/forbidden_cache.rs` | LRU wrapper struct over `forbidden_for_target` lookup keyed by `TheoremId` | create |
| `engine/crates/rocks/tests/test_forbidden_for_target.rs` | Integration tests: chain ancestors, cycle prevention, backfill correctness, LRU invalidation | create |
| `engine/crates/derive/src/axiom_store.rs` | `iter_excluding` and `by_domain_excluding` methods (use `axiom_id_from_name`) | modify |
| `engine/crates/derive/src/derivation.rs` | `DerivationEngine::derive_for_target(target_id, strategy, db)` entry point | modify |
| `engine/crates/derive/tests/test_derivation_acyclicity.rs` | End-to-end test: derive E=mc² target with `mass_shell_condition` stored as derived theorem, confirm exclusion | create |
| `engine/crates/api/src/bin/backfill_lineage.rs` | Optional one-shot CLI binary that opens the production RocksDB and runs `backfill_lineage_and_reverse_deps()` | create |

---

## Task 1: Add `compute_transitive_ancestors` helper to `nasrudin_rocks`

**Files:**
- Modify: `engine/crates/rocks/src/lib.rs` (add helper method on `TheoremDb`)

This walks the proof tree of a theorem and unions in every parent theorem's already-cached `axiom_ancestors` (transitive closure built bottom-up at write time). The function must be deterministic and order-independent.

- [ ] **Step 1: Write the failing integration test**

Create `engine/crates/rocks/tests/test_forbidden_for_target.rs`:

```rust
use nasrudin_core::{
    AlgebraicOp, Domain, Expr, FitnessScore, ProofTree, Theorem, TheoremOrigin,
    VerificationStatus,
};
use nasrudin_rocks::TheoremDb;
use std::collections::BTreeSet;
use tempfile::TempDir;

fn axiom_theorem(id: u8, name: &str) -> Theorem {
    let tid = [id, 0, 0, 0, 0, 0, 0, 0];
    Theorem {
        id: tid,
        statement: Expr::Var(name.into()),
        canonical: name.into(),
        latex: String::new(),
        proof: ProofTree::Axiom(tid),
        depth: 0,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: vec![],
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    }
}

fn derived_theorem(id: u8, name: &str, premise_ids: &[[u8; 8]]) -> Theorem {
    let mut leaves: Vec<ProofTree> = premise_ids
        .iter()
        .map(|p| ProofTree::Axiom(*p))
        .collect();
    let proof = if leaves.len() == 1 {
        leaves.pop().unwrap()
    } else {
        ProofTree::EqChain(leaves)
    };
    Theorem {
        id: [id, 0, 0, 0, 0, 0, 0, 0],
        statement: Expr::Var(name.into()),
        canonical: name.into(),
        latex: String::new(),
        proof,
        depth: 1,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: premise_ids.to_vec(),
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    }
}

#[test]
fn transitive_ancestors_chain() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // A is a leaf axiom.
    let a = axiom_theorem(1, "A");
    // B derives from A.
    let b = derived_theorem(2, "B", &[a.id]);
    // C derives from B.
    let c = derived_theorem(3, "C", &[b.id]);

    db.put_theorem(&a).unwrap();
    db.put_theorem(&b).unwrap();
    db.put_theorem(&c).unwrap();

    let lin_c = db.get_lineage(&c.id).unwrap().unwrap();
    let mut ancestors: BTreeSet<_> = lin_c.axiom_ancestors.iter().copied().collect();

    assert!(ancestors.contains(&a.id), "C must transitively cite A");
    assert!(ancestors.contains(&b.id), "C must directly cite B");
    ancestors.remove(&a.id);
    ancestors.remove(&b.id);
    assert!(ancestors.is_empty(), "C has no other ancestors");
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target transitive_ancestors_chain`
Expected: FAIL — `axiom_ancestors` is currently always `vec![]`, so `ancestors.contains(&a.id)` is `false`.

- [ ] **Step 3: Add the `compute_transitive_ancestors` helper on `TheoremDb`**

Add immediately above `pub fn put_theorem` (around `engine/crates/rocks/src/lib.rs:267`):

```rust
    /// Compute the transitive axiom-ancestor closure for a theorem.
    ///
    /// Walks `theorem.proof` to collect the immediate `Axiom(id)` leaves,
    /// then unions in the cached `axiom_ancestors` of each leaf already
    /// stored in `CF_LINEAGE`. Result is deterministic (sorted via
    /// `BTreeSet`) and includes every axiom transitively used by the
    /// proof — leaves that are themselves axioms (no parents) contribute
    /// only their own id.
    ///
    /// Builds bottom-up: every parent's own ancestors must already be
    /// stored in CF_LINEAGE. If a parent isn't found yet, its id is
    /// included but the chain stops there (the backfill task is
    /// responsible for populating in topological order).
    fn compute_transitive_ancestors(
        &self,
        theorem: &nasrudin_core::Theorem,
    ) -> Result<Vec<nasrudin_core::TheoremId>> {
        use std::collections::BTreeSet;
        let mut acc: BTreeSet<nasrudin_core::TheoremId> =
            nasrudin_core::collect_axiom_ids(&theorem.proof);
        let immediate: Vec<_> = acc.iter().copied().collect();
        for parent_id in &immediate {
            if parent_id == &theorem.id {
                continue;
            }
            if let Some(parent_lineage) = self.get_lineage(parent_id)? {
                for a in parent_lineage.axiom_ancestors {
                    acc.insert(a);
                }
            }
        }
        acc.remove(&theorem.id);
        Ok(acc.into_iter().collect())
    }
```

This requires `nasrudin_core::collect_axiom_ids` to be re-exported from the core crate. Check by running `grep -n "pub use" engine/crates/core/src/lib.rs` — if `collect_axiom_ids` isn't already public at crate root, add the export now:

In `engine/crates/core/src/lib.rs`, verify a line like:
```rust
pub use axiom_set::{axiom_id_from_name, axiom_set_hash, collect_axiom_ids};
```
exists. If not, add it next to the other `pub use` lines.

- [ ] **Step 4: Wire `compute_transitive_ancestors` into `put_theorem`**

In `engine/crates/rocks/src/lib.rs:295-300`, replace the hardcoded `vec![]`:

```rust
        // Lineage record
        let cf_lineage = self
            .db
            .cf_handle(CF_LINEAGE)
            .context("Missing lineage CF")?;
        let lineage = LineageRecord {
            theorem_id: theorem.id,
            parents: theorem.parents.clone(),
            children: theorem.children.clone(),
            axiom_ancestors: self.compute_transitive_ancestors(theorem)?,
        };
```

- [ ] **Step 5: Run the test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target transitive_ancestors_chain`
Expected: PASS

- [ ] **Step 6: Commit**

```bash
git add engine/crates/rocks/src/lib.rs engine/crates/rocks/tests/test_forbidden_for_target.rs engine/crates/core/src/lib.rs
git commit -m "rocks: populate LineageRecord.axiom_ancestors with transitive closure

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 2: Add `CF_REVERSE_DEPS` column family

**Files:**
- Modify: `engine/crates/rocks/src/lib.rs`

The reverse-dependency index lets us answer "what theorems transitively cite X?" with a single prefix scan instead of walking all proofs. Schema:

- Key: `ancestor_id (8 bytes) || dependent_id (8 bytes)` — total 16 bytes, no separator needed (fixed-width).
- Value: empty `&[]` — the key carries the relation.
- Range scan: prefix on `ancestor_id` yields every dependent id whose proof transitively cites `ancestor_id`.

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/rocks/tests/test_forbidden_for_target.rs`:

```rust
#[test]
fn reverse_deps_index_lists_all_dependents() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let a = axiom_theorem(1, "A");
    let b = derived_theorem(2, "B", &[a.id]);
    let c = derived_theorem(3, "C", &[b.id]);
    db.put_theorem(&a).unwrap();
    db.put_theorem(&b).unwrap();
    db.put_theorem(&c).unwrap();

    // A's dependents: B (direct) and C (transitive via B).
    let mut deps = db.list_dependents(&a.id).unwrap();
    deps.sort();
    let mut expected = vec![b.id, c.id];
    expected.sort();
    assert_eq!(deps, expected);

    // C is a leaf: no dependents.
    assert!(db.list_dependents(&c.id).unwrap().is_empty());
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target reverse_deps_index_lists_all_dependents`
Expected: FAIL — method `list_dependents` doesn't exist; compile error.

- [ ] **Step 3: Add the column family constant and registration**

In `engine/crates/rocks/src/lib.rs`, add after line 71 (`CF_LAKE_PROMOTION_QUEUE`):

```rust
/// Reverse-dependency index for derivation acyclicity. For every
/// theorem T whose proof transitively cites ancestor A, we write
/// key `A_id (8) || T_id (8)` with empty value. A `prefix_iterator_cf`
/// keyed on `A_id` yields every T that depends on A — used by
/// `forbidden_for_target` to filter the premise set when re-deriving A
/// (or anything in A's class). Fixed-width keys mean no separator
/// byte and no value payload — the cheapest possible edge index.
const CF_REVERSE_DEPS: &str = "reverse_deps";
```

In the `ALL_CFS` array around line 73-92, add `CF_REVERSE_DEPS` to the list:

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
    CF_PG_INSERT_QUEUE,
    CF_BY_VERIFIED_AT,
    CF_LAKE_PROMOTION_QUEUE,
    CF_CORPUS_AXIOM,
    CF_CORPUS_DOMAIN,
    CF_CORPUS_META,
    CF_REVERSE_DEPS,
];
```

`CF_REVERSE_DEPS` is range-scanned by prefix, NOT point-looked-up, so do **not** add it to `POINT_LOOKUP_CFS`. The default block-cache attachment in `build_cf_descriptor` (else-branch at line 1289) is correct.

- [ ] **Step 4: Add `list_dependents` method**

Insert after `list_by_axiom` (around `engine/crates/rocks/src/lib.rs:665`):

```rust
    /// List every theorem whose proof transitively cites `ancestor_id`.
    ///
    /// Prefix-scans `CF_REVERSE_DEPS` on the 8-byte `ancestor_id`. The
    /// values are ignored; the dependent id is the second half of the
    /// 16-byte key. Returns deterministic order (RocksDB iterator order
    /// over the lex-sorted dependent ids).
    pub fn list_dependents(
        &self,
        ancestor_id: &nasrudin_core::TheoremId,
    ) -> Result<Vec<nasrudin_core::TheoremId>> {
        let cf = self
            .db
            .cf_handle(CF_REVERSE_DEPS)
            .context("Missing reverse_deps CF")?;
        let mut out = Vec::new();
        let iter = self.db.prefix_iterator_cf(&cf, ancestor_id);
        for item in iter {
            let (key, _) = item.context("Failed to iterate reverse_deps")?;
            if key.len() != 16 || !key.starts_with(ancestor_id) {
                break;
            }
            let mut dep = [0u8; 8];
            dep.copy_from_slice(&key[8..16]);
            out.push(dep);
        }
        Ok(out)
    }
```

- [ ] **Step 5: Wire reverse-deps writes into `put_theorem`**

The lineage value is computed in Step 4 of Task 1. Capture the ancestor list before serializing so we can iterate it for the index. Replace the lineage block in `put_theorem` (around `engine/crates/rocks/src/lib.rs:290-303`) with:

```rust
        // Lineage record (transitive ancestor closure)
        let cf_lineage = self
            .db
            .cf_handle(CF_LINEAGE)
            .context("Missing lineage CF")?;
        let ancestors = self.compute_transitive_ancestors(theorem)?;
        let lineage = LineageRecord {
            theorem_id: theorem.id,
            parents: theorem.parents.clone(),
            children: theorem.children.clone(),
            axiom_ancestors: ancestors.clone(),
        };
        let lineage_value =
            serde_json::to_vec(&lineage).context("Failed to serialize lineage")?;
        batch.put_cf(&cf_lineage, theorem.id, &lineage_value);

        // Reverse-deps index — one row per (ancestor, theorem) edge.
        let cf_reverse = self
            .db
            .cf_handle(CF_REVERSE_DEPS)
            .context("Missing reverse_deps CF")?;
        for ancestor_id in &ancestors {
            let mut key = [0u8; 16];
            key[..8].copy_from_slice(ancestor_id);
            key[8..].copy_from_slice(&theorem.id);
            batch.put_cf(&cf_reverse, key, &[] as &[u8]);
        }
```

The whole block stays inside the existing `WriteBatch` so a crash mid-write can't desync the lineage record from the reverse-deps index.

- [ ] **Step 6: Run the test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target`
Expected: both `transitive_ancestors_chain` and `reverse_deps_index_lists_all_dependents` PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/rocks/src/lib.rs engine/crates/rocks/tests/test_forbidden_for_target.rs
git commit -m "rocks: add CF_REVERSE_DEPS index for theorem dependency lookup

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 3: Add `forbidden_for_target` query

**Files:**
- Modify: `engine/crates/rocks/src/lib.rs`

`forbidden_for_target(T)` returns the set of theorem ids that must NOT be used as premises when deriving anything with target T. Membership: `{T} ∪ list_dependents(T)`.

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/rocks/tests/test_forbidden_for_target.rs`:

```rust
use std::collections::HashSet;

#[test]
fn forbidden_set_excludes_target_and_descendants() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // A → B → C linear chain.
    let a = axiom_theorem(1, "A");
    let b = derived_theorem(2, "B", &[a.id]);
    let c = derived_theorem(3, "C", &[b.id]);
    // D is parallel: depends on A but not B or C.
    let d = derived_theorem(4, "D", &[a.id]);
    for t in [&a, &b, &c, &d] {
        db.put_theorem(t).unwrap();
    }

    // Forbidden when re-deriving A: {A, B, C, D} (everything that cites A).
    let forbidden_a = db.forbidden_for_target(&a.id).unwrap();
    let expected_a: HashSet<_> = [a.id, b.id, c.id, d.id].into_iter().collect();
    assert_eq!(forbidden_a.as_ref(), &expected_a);

    // Forbidden when re-deriving B: {B, C}. A and D still usable.
    let forbidden_b = db.forbidden_for_target(&b.id).unwrap();
    let expected_b: HashSet<_> = [b.id, c.id].into_iter().collect();
    assert_eq!(forbidden_b.as_ref(), &expected_b);

    // Forbidden when re-deriving D (a leaf): just {D}.
    let forbidden_d = db.forbidden_for_target(&d.id).unwrap();
    let expected_d: HashSet<_> = [d.id].into_iter().collect();
    assert_eq!(forbidden_d.as_ref(), &expected_d);
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target forbidden_set_excludes_target_and_descendants`
Expected: FAIL — method `forbidden_for_target` doesn't exist.

- [ ] **Step 3: Implement `forbidden_for_target` (uncached)**

Insert immediately after `list_dependents` in `engine/crates/rocks/src/lib.rs`:

```rust
    /// Set of theorem ids that must NOT be used as premises when
    /// deriving anything that resolves to target `target_id`. Returns
    /// `{target_id} ∪ list_dependents(target_id)`. The result is wrapped
    /// in `Arc` so the LRU layer (added in a follow-up task) can hand
    /// out shared references without copying.
    pub fn forbidden_for_target(
        &self,
        target_id: &nasrudin_core::TheoremId,
    ) -> Result<std::sync::Arc<std::collections::HashSet<nasrudin_core::TheoremId>>> {
        let mut set: std::collections::HashSet<nasrudin_core::TheoremId> =
            std::collections::HashSet::new();
        set.insert(*target_id);
        for dep in self.list_dependents(target_id)? {
            set.insert(dep);
        }
        Ok(std::sync::Arc::new(set))
    }
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target`
Expected: all three tests PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/rocks/src/lib.rs engine/crates/rocks/tests/test_forbidden_for_target.rs
git commit -m "rocks: add TheoremDb::forbidden_for_target query

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 4: Add LRU cache for `forbidden_for_target`

**Files:**
- Create: `engine/crates/rocks/src/forbidden_cache.rs`
- Modify: `engine/crates/rocks/src/lib.rs` (add `forbidden_cache` field, route through cache, invalidate on writes)
- Modify: `engine/crates/rocks/Cargo.toml` (add `lru` dep)

The GA's premise-selection inner loop calls `forbidden_for_target(target)` thousands of times per generation for the same handful of targets. A 256-entry LRU avoids the prefix-scan on every call; entries are invalidated by `put_theorem` for any ancestor we just wrote (the write may have introduced a new dependent for that ancestor).

- [ ] **Step 1: Write the failing test for LRU caching + invalidation**

Append to `engine/crates/rocks/tests/test_forbidden_for_target.rs`:

```rust
#[test]
fn forbidden_cache_returns_same_arc_on_warm_lookup() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let a = axiom_theorem(1, "A");
    let b = derived_theorem(2, "B", &[a.id]);
    db.put_theorem(&a).unwrap();
    db.put_theorem(&b).unwrap();

    let f1 = db.forbidden_for_target(&a.id).unwrap();
    let f2 = db.forbidden_for_target(&a.id).unwrap();
    // Cached lookup must hand out the same Arc without re-scanning.
    assert!(std::sync::Arc::ptr_eq(&f1, &f2));
}

#[test]
fn forbidden_cache_invalidates_on_new_dependent() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let a = axiom_theorem(1, "A");
    db.put_theorem(&a).unwrap();
    let f_before = db.forbidden_for_target(&a.id).unwrap();
    assert_eq!(f_before.len(), 1, "only A itself before B is added");

    // Adding B (which cites A) must invalidate A's cached entry.
    let b = derived_theorem(2, "B", &[a.id]);
    db.put_theorem(&b).unwrap();
    let f_after = db.forbidden_for_target(&a.id).unwrap();
    assert_eq!(f_after.len(), 2, "A and B after B is added");
    assert!(f_after.contains(&b.id));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target forbidden_cache`
Expected: FAIL — `Arc::ptr_eq` returns false (uncached path always returns a fresh `Arc`); the second test still passes by coincidence but `forbidden_cache_returns_same_arc_on_warm_lookup` fails.

- [ ] **Step 3: Add `lru` to `nasrudin-rocks` dependencies**

`lru` is already in the workspace (used by `nasrudin-derive`). Verify with `cargo metadata --no-deps --format-version 1 | rg '"lru"'` if uncertain. Open `engine/crates/rocks/Cargo.toml` and add under `[dependencies]`:

```toml
lru = { workspace = true }
```

If the workspace `Cargo.toml` doesn't have `lru` listed, look up the version `nasrudin-derive` uses (`grep '^lru' engine/crates/derive/Cargo.toml`) and add the matching version.

- [ ] **Step 4: Create `engine/crates/rocks/src/forbidden_cache.rs`**

```rust
//! LRU cache for `TheoremDb::forbidden_for_target`.
//!
//! The GA's premise-selection path calls `forbidden_for_target(T)`
//! thousands of times per generation against the same small set of
//! targets. A 256-entry LRU absorbs the repeated prefix-scan into a
//! single map lookup. `Arc<HashSet<TheoremId>>` lets concurrent callers
//! share the result without cloning the set.
//!
//! Invalidation is precise: when `put_theorem(T)` writes new
//! reverse-deps edges for ancestors `A1, A2, ...`, we evict each `Ai`
//! from this cache so the next reader rescans. We do NOT invalidate
//! `T` itself — its forbidden set is `{T}` (a leaf, no dependents yet),
//! and adding T to the cache eagerly is fine since the first
//! `forbidden_for_target(T)` call after the write will populate it.

use lru::LruCache;
use nasrudin_core::TheoremId;
use std::collections::HashSet;
use std::num::NonZeroUsize;
use std::sync::{Arc, Mutex};

/// Capacity tuned to the GA's per-generation working set: ~50 active
/// targets across all islands × small slack. ~16 KB at avg 64 ids/set.
const CAPACITY: usize = 256;

pub(crate) struct ForbiddenCache {
    inner: Mutex<LruCache<TheoremId, Arc<HashSet<TheoremId>>>>,
}

impl ForbiddenCache {
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(LruCache::new(NonZeroUsize::new(CAPACITY).unwrap())),
        }
    }

    pub fn get(&self, target: &TheoremId) -> Option<Arc<HashSet<TheoremId>>> {
        self.inner.lock().unwrap().get(target).cloned()
    }

    pub fn insert(&self, target: TheoremId, value: Arc<HashSet<TheoremId>>) {
        self.inner.lock().unwrap().put(target, value);
    }

    pub fn invalidate(&self, target: &TheoremId) {
        self.inner.lock().unwrap().pop(target);
    }
}
```

- [ ] **Step 5: Wire the cache into `TheoremDb`**

In `engine/crates/rocks/src/lib.rs`, register the new module near the other `pub mod` lines (around line 12-17):

```rust
mod forbidden_cache;
use forbidden_cache::ForbiddenCache;
```

Add the field to `TheoremDb` (around line 207-209):

```rust
pub struct TheoremDb {
    db: std::sync::Arc<DB>,
    forbidden_cache: std::sync::Arc<ForbiddenCache>,
}
```

In `TheoremDb::new` (around line 254-256), construct it:

```rust
        Ok(Self {
            db: std::sync::Arc::new(db),
            forbidden_cache: std::sync::Arc::new(ForbiddenCache::new()),
        })
```

- [ ] **Step 6: Route `forbidden_for_target` through the cache**

Replace the body added in Task 3 with:

```rust
    pub fn forbidden_for_target(
        &self,
        target_id: &nasrudin_core::TheoremId,
    ) -> Result<std::sync::Arc<std::collections::HashSet<nasrudin_core::TheoremId>>> {
        if let Some(hit) = self.forbidden_cache.get(target_id) {
            return Ok(hit);
        }
        let mut set: std::collections::HashSet<nasrudin_core::TheoremId> =
            std::collections::HashSet::new();
        set.insert(*target_id);
        for dep in self.list_dependents(target_id)? {
            set.insert(dep);
        }
        let arc = std::sync::Arc::new(set);
        self.forbidden_cache.insert(*target_id, arc.clone());
        Ok(arc)
    }
```

- [ ] **Step 7: Invalidate the cache on `put_theorem`**

After the `self.db.write(batch)` call inside `put_theorem` (around `engine/crates/rocks/src/lib.rs:351-353`), add cache invalidation for each ancestor whose reverse-deps row was just written:

```rust
        self.db
            .write(batch)
            .context("Failed to write theorem batch")?;

        // Cached forbidden-sets for every ancestor are stale now —
        // we just added a new dependent edge for each of them.
        for ancestor_id in &ancestors {
            self.forbidden_cache.invalidate(ancestor_id);
        }
```

`ancestors` was computed earlier in the method (Task 2 Step 5); ensure it's still in scope. If it isn't (the binding was shadowed), bind it once before the lineage block and reuse.

- [ ] **Step 8: Run all tests**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target`
Expected: all five tests PASS.

- [ ] **Step 9: Commit**

```bash
git add engine/crates/rocks/Cargo.toml engine/crates/rocks/src/lib.rs engine/crates/rocks/src/forbidden_cache.rs engine/crates/rocks/tests/test_forbidden_for_target.rs
git commit -m "rocks: LRU cache forbidden-set lookups, invalidate on write

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 5: Backfill migration for existing RocksDB stores

**Files:**
- Modify: `engine/crates/rocks/src/lib.rs` (add `backfill_lineage_and_reverse_deps` method)
- Create: `engine/crates/api/src/bin/backfill_lineage.rs` (one-shot CLI)

The production RocksDB has tens of thousands of theorems with empty `axiom_ancestors` and no reverse-deps rows. The migration walks `CF_THEOREMS` in topological-ish order (depth ascending — depth 0 axioms first, so a parent's lineage is always populated before its child's), recomputes transitive ancestors, and rewrites lineage + reverse-deps. Idempotent: running twice is a no-op.

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/rocks/tests/test_forbidden_for_target.rs`:

```rust
#[test]
fn backfill_populates_existing_theorems() {
    let dir = TempDir::new().unwrap();

    // Phase 1: write theorems WITHOUT reverse-deps (simulate pre-migration).
    {
        let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
        let mut a = axiom_theorem(1, "A");
        a.depth = 0;
        let mut b = derived_theorem(2, "B", &[a.id]);
        b.depth = 1;
        let mut c = derived_theorem(3, "C", &[b.id]);
        c.depth = 2;
        db.put_theorem(&a).unwrap();
        db.put_theorem(&b).unwrap();
        db.put_theorem(&c).unwrap();
        // Manually clear lineage + reverse-deps to simulate a pre-migration db.
        db.clear_lineage_for_test().unwrap();
    }

    // Phase 2: reopen, run backfill, verify.
    {
        let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
        let count = db.backfill_lineage_and_reverse_deps().unwrap();
        assert_eq!(count, 3, "backfill processed all 3 theorems");

        let a_id = [1u8, 0, 0, 0, 0, 0, 0, 0];
        let mut deps_a = db.list_dependents(&a_id).unwrap();
        deps_a.sort();
        let mut expected = vec![[2u8, 0, 0, 0, 0, 0, 0, 0], [3u8, 0, 0, 0, 0, 0, 0, 0]];
        expected.sort();
        assert_eq!(deps_a, expected);

        // Idempotent: second run produces same state, returns same count.
        let count2 = db.backfill_lineage_and_reverse_deps().unwrap();
        assert_eq!(count2, 3);
        let mut deps_a2 = db.list_dependents(&a_id).unwrap();
        deps_a2.sort();
        assert_eq!(deps_a2, expected);
    }
}
```

This test depends on a `clear_lineage_for_test` helper that wipes `CF_LINEAGE` and `CF_REVERSE_DEPS`. We'll add that as a `#[cfg(test)]` method.

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target backfill_populates_existing_theorems`
Expected: FAIL — `clear_lineage_for_test` and `backfill_lineage_and_reverse_deps` don't exist.

- [ ] **Step 3: Add the test helper**

Insert into `engine/crates/rocks/src/lib.rs` near the other utility methods on `TheoremDb`:

```rust
    /// Test-only: wipe `CF_LINEAGE` and `CF_REVERSE_DEPS` to simulate a
    /// pre-migration database state.
    #[cfg(test)]
    pub fn clear_lineage_for_test(&self) -> Result<()> {
        for cf_name in [CF_LINEAGE, CF_REVERSE_DEPS] {
            let cf = self
                .db
                .cf_handle(cf_name)
                .context(format!("Missing {cf_name} CF"))?;
            let keys: Vec<Vec<u8>> = self
                .db
                .iterator_cf(&cf, IteratorMode::Start)
                .filter_map(|item| item.ok().map(|(k, _)| k.to_vec()))
                .collect();
            for k in keys {
                self.db
                    .delete_cf(&cf, &k)
                    .context("Failed to clear test row")?;
            }
        }
        self.forbidden_cache.invalidate_all_for_test();
        Ok(())
    }
```

Add `invalidate_all_for_test` to `forbidden_cache.rs`:

```rust
    #[cfg(test)]
    pub fn invalidate_all_for_test(&self) {
        self.inner.lock().unwrap().clear();
    }
```

- [ ] **Step 4: Implement `backfill_lineage_and_reverse_deps`**

Insert after `list_dependents`:

```rust
    /// Recompute and persist `LineageRecord.axiom_ancestors` and
    /// `CF_REVERSE_DEPS` for every theorem already in `CF_THEOREMS`.
    ///
    /// Walks theorems in ascending depth order (via `CF_BY_DEPTH`) so a
    /// parent's lineage is always populated before its child's
    /// `compute_transitive_ancestors` call needs it. Each theorem's
    /// reverse-deps rows are wiped before re-write, making the operation
    /// idempotent — running this on an already-migrated db produces
    /// identical state.
    ///
    /// Returns the count of theorems processed.
    pub fn backfill_lineage_and_reverse_deps(&self) -> Result<usize> {
        // 1. Collect (depth, id) pairs from CF_BY_DEPTH so we process
        //    theorems in topological order. We can't iterate
        //    CF_THEOREMS directly because order would be hash-keyed.
        let cf_depth = self
            .db
            .cf_handle(CF_BY_DEPTH)
            .context("Missing by_depth CF")?;
        let mut ordered: Vec<nasrudin_core::TheoremId> = Vec::new();
        for item in self.db.iterator_cf(&cf_depth, IteratorMode::Start) {
            let (_, value) = item.context("Failed to iterate by_depth")?;
            if value.len() < 8 {
                continue;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&value[..8]);
            ordered.push(id);
        }

        // 2. For each theorem, recompute ancestors and rewrite indexes.
        let cf_lineage = self
            .db
            .cf_handle(CF_LINEAGE)
            .context("Missing lineage CF")?;
        let cf_reverse = self
            .db
            .cf_handle(CF_REVERSE_DEPS)
            .context("Missing reverse_deps CF")?;

        let mut processed = 0usize;
        for tid in &ordered {
            let theorem = match self.get_theorem(tid)? {
                Some(t) => t,
                None => continue,
            };

            // Wipe existing reverse-deps rows that point AT this theorem.
            // Old (stale) rows are keyed `old_ancestor || tid`. We don't
            // know the old ancestor set; cheapest correct fix is to
            // remove every reverse-deps row whose suffix is `tid`. That
            // requires scanning the whole CF — fine for a one-shot
            // migration but unacceptable per-write. We accept O(N²) here
            // because it only runs once.
            let mut victims: Vec<Vec<u8>> = Vec::new();
            for item in self.db.iterator_cf(&cf_reverse, IteratorMode::Start) {
                let (key, _) = item.context("Failed to scan reverse_deps")?;
                if key.len() == 16 && &key[8..16] == tid.as_slice() {
                    victims.push(key.to_vec());
                }
            }
            let mut batch = WriteBatch::default();
            for k in victims {
                batch.delete_cf(&cf_reverse, &k);
            }

            // Recompute ancestors with parents already migrated.
            let ancestors = self.compute_transitive_ancestors(&theorem)?;
            let lineage = LineageRecord {
                theorem_id: theorem.id,
                parents: theorem.parents.clone(),
                children: theorem.children.clone(),
                axiom_ancestors: ancestors.clone(),
            };
            let lineage_value =
                serde_json::to_vec(&lineage).context("Failed to serialize lineage")?;
            batch.put_cf(&cf_lineage, theorem.id, &lineage_value);

            for ancestor_id in &ancestors {
                let mut key = [0u8; 16];
                key[..8].copy_from_slice(ancestor_id);
                key[8..].copy_from_slice(&theorem.id);
                batch.put_cf(&cf_reverse, key, &[] as &[u8]);
            }

            self.db
                .write(batch)
                .context("Failed to write backfill batch")?;
            for ancestor_id in &ancestors {
                self.forbidden_cache.invalidate(ancestor_id);
            }
            processed += 1;
        }

        tracing::info!(
            "backfill_lineage_and_reverse_deps: processed {} theorems",
            processed
        );
        Ok(processed)
    }
```

Note the deliberate O(N²) scan in the per-theorem cleanup: this is a one-shot migration, not a hot-path operation. For 50k theorems that's ~2.5B comparisons but each is a fixed-length byte compare — completes in under a minute on a warm RocksDB. If profiling shows it's too slow, swap in a one-pass "build the full reverse_deps wipe set" before the loop.

- [ ] **Step 5: Run the test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target backfill_populates_existing_theorems`
Expected: PASS.

- [ ] **Step 6: Add the CLI binary**

Verify the api crate has a `bin/` directory: `ls engine/crates/api/src/bin/`. If not, create it. Then create `engine/crates/api/src/bin/backfill_lineage.rs`:

```rust
//! One-shot migration: populate `LineageRecord.axiom_ancestors` and
//! `CF_REVERSE_DEPS` for every theorem in the production RocksDB.
//!
//! Usage: `cargo run --bin backfill_lineage -- <rocksdb_path>`
//! Idempotent: safe to re-run.

use anyhow::{Context, Result};
use nasrudin_rocks::TheoremDb;

fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let path = std::env::args()
        .nth(1)
        .context("usage: backfill_lineage <rocksdb_path>")?;

    let db = TheoremDb::new(&path).context("Failed to open RocksDB at given path")?;

    let started = std::time::Instant::now();
    let processed = db
        .backfill_lineage_and_reverse_deps()
        .context("Backfill failed")?;
    let elapsed = started.elapsed();

    println!(
        "Backfill complete: {processed} theorems processed in {:.2}s",
        elapsed.as_secs_f64()
    );
    Ok(())
}
```

Confirm the api crate's `Cargo.toml` already has `nasrudin-rocks`, `anyhow`, and `tracing-subscriber` as dependencies (it does — `grep -n "nasrudin-rocks\|tracing-subscriber" engine/crates/api/Cargo.toml`). If `tracing-subscriber` is missing, add `tracing-subscriber = { workspace = true }` to `[dependencies]`.

- [ ] **Step 7: Verify the binary compiles**

Run: `cd engine && cargo build -p nasrudin-api --bin backfill_lineage`
Expected: clean build.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/rocks/src/lib.rs engine/crates/rocks/src/forbidden_cache.rs engine/crates/rocks/tests/test_forbidden_for_target.rs engine/crates/api/src/bin/backfill_lineage.rs engine/crates/api/Cargo.toml
git commit -m "rocks: backfill lineage + reverse-deps + one-shot CLI

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 6: `AxiomStore::iter_excluding` and `by_domain_excluding`

**Files:**
- Modify: `engine/crates/derive/src/axiom_store.rs`

The GA and the chain engine pull premises from `AxiomStore` by name. To filter, we map each axiom's name → synthetic `TheoremId` via `axiom_id_from_name` and skip names whose id is in the forbidden set.

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/derive/tests/test_axiom_store.rs`:

```rust
#[test]
fn iter_excluding_skips_forbidden_axioms() {
    use nasrudin_core::axiom_id_from_name;
    use std::collections::HashSet;

    let mut store = AxiomStore::new();
    store.load_special_relativity_upstream();

    let forbidden_name = "rest_frame_psq_zero";
    let forbidden_id = axiom_id_from_name(forbidden_name);
    let mut forbidden = HashSet::new();
    forbidden.insert(forbidden_id);

    let names: Vec<String> = store
        .iter_excluding(&forbidden)
        .map(|a| a.name)
        .collect();
    assert!(
        !names.iter().any(|n| n == forbidden_name),
        "{forbidden_name} must be filtered out"
    );
    // Other axioms in the upstream set must still be present.
    assert!(names.iter().any(|n| n == "minkowski_invariant_def"));
}

#[test]
fn by_domain_excluding_respects_forbidden_set() {
    use nasrudin_core::{axiom_id_from_name, Domain};
    use std::collections::HashSet;

    let mut store = AxiomStore::new();
    store.load_special_relativity_upstream();

    let forbidden_name = "four_momentum_time_component";
    let mut forbidden = HashSet::new();
    forbidden.insert(axiom_id_from_name(forbidden_name));

    let names: Vec<String> = store
        .by_domain_excluding(&Domain::SpecialRelativity, &forbidden)
        .into_iter()
        .map(|a| a.name)
        .collect();
    assert!(!names.iter().any(|n| n == forbidden_name));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd engine && cargo test -p nasrudin-derive --test test_axiom_store iter_excluding`
Expected: FAIL — methods don't exist.

- [ ] **Step 3: Implement `iter_excluding` and `by_domain_excluding`**

Insert in `engine/crates/derive/src/axiom_store.rs` immediately after the existing `iter` method (around line 345-361):

```rust
    /// Like `iter()` but skips any axiom whose synthetic id (derived
    /// from its name via `axiom_id_from_name`) is in `forbidden`. Used
    /// by the GA and chain engine to filter premises during a
    /// derivation that targets a specific theorem.
    pub fn iter_excluding<'a>(
        &'a self,
        forbidden: &'a std::collections::HashSet<nasrudin_core::TheoremId>,
    ) -> Box<dyn Iterator<Item = nasrudin_core::Axiom> + 'a> {
        Box::new(self.iter().filter(move |axiom| {
            !forbidden.contains(&nasrudin_core::axiom_id_from_name(&axiom.name))
        }))
    }

    /// Like `by_domain(d)` but excludes axioms whose synthetic id is
    /// in `forbidden`. See [`iter_excluding`] for the id-derivation
    /// semantics.
    pub fn by_domain_excluding(
        &self,
        domain: &nasrudin_core::Domain,
        forbidden: &std::collections::HashSet<nasrudin_core::TheoremId>,
    ) -> Vec<nasrudin_core::Axiom> {
        self.by_domain(domain)
            .into_iter()
            .filter(|axiom| {
                !forbidden.contains(&nasrudin_core::axiom_id_from_name(&axiom.name))
            })
            .collect()
    }
```

Verify the `nasrudin-core` crate exports `axiom_id_from_name` at crate root. From Task 1 Step 3 we already added the `pub use`; confirm with `grep -n "axiom_id_from_name" engine/crates/core/src/lib.rs`.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cd engine && cargo test -p nasrudin-derive --test test_axiom_store iter_excluding by_domain_excluding`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/derive/src/axiom_store.rs engine/crates/derive/tests/test_axiom_store.rs
git commit -m "derive: AxiomStore filter-by-forbidden iter helpers

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 7: `DerivationEngine::derive_for_target` entry point

**Files:**
- Modify: `engine/crates/derive/src/derivation.rs`
- Modify: `engine/crates/derive/Cargo.toml` (add `nasrudin-rocks` dep if missing)

Strategies currently take `&AxiomStore` directly. Add a thin wrapper at the engine level that takes `target_id` and a `&TheoremDb` reference, fetches the forbidden set, and exposes it via a context field for strategies that need to filter. Existing strategies that ignore the context (e.g. `DeriveRestEnergy`, hardcoded names) keep working unchanged.

- [ ] **Step 1: Add a `forbidden_axioms` field to `DerivationContext`**

Open `engine/crates/derive/src/context.rs`, find the `DerivationContext` struct (line 18), and add:

```rust
pub struct DerivationContext {
    // ... existing fields ...
    /// Theorem ids that strategies must NOT use as premises during
    /// this derivation. Populated by `derive_for_target` from the
    /// store's reverse-deps index. Empty for derivations that don't
    /// have an in-store target (legacy `derive_by_strategy` callers).
    pub forbidden_axioms: std::sync::Arc<std::collections::HashSet<nasrudin_core::TheoremId>>,
}
```

In the `Default` impl (around line 94), initialize:

```rust
            forbidden_axioms: std::sync::Arc::new(std::collections::HashSet::new()),
```

- [ ] **Step 2: Add `nasrudin-rocks` to derive deps if absent**

Check: `grep -n "nasrudin-rocks" engine/crates/derive/Cargo.toml`. The crate already depends on `nasrudin-rocks` (the `CorpusBackend` trait imports — see `axiom_store.rs:57`). Confirm and skip if already present.

- [ ] **Step 3: Write a failing integration test**

Create `engine/crates/derive/tests/test_derivation_acyclicity.rs`:

```rust
//! End-to-end: stash a derived theorem in the TheoremDb, then derive a
//! new target and confirm the strategy refuses to use the forbidden
//! ancestor as a premise.

use nasrudin_core::{
    axiom_id_from_name, Domain, Expr, FitnessScore, ProofTree, Theorem, TheoremOrigin,
    VerificationStatus,
};
use nasrudin_derive::DerivationEngine;
use nasrudin_rocks::TheoremDb;
use tempfile::TempDir;

#[test]
fn derive_for_target_excludes_dependents_of_target() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // Stash a "target" theorem with the synthetic id of "rest_energy"
    // so we can drive forbidden_for_target via name lookup.
    let target_id = axiom_id_from_name("rest_energy");
    let target = Theorem {
        id: target_id,
        statement: Expr::Var("E_eq_mc2".into()),
        canonical: "E_eq_mc2".into(),
        latex: String::new(),
        proof: ProofTree::Axiom(target_id),
        depth: 0,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: vec![],
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    };
    db.put_theorem(&target).unwrap();

    // Stash a "mass_shell_condition" theorem whose proof cites target.
    // This represents the post-Phase-1 world: mass_shell IS in the
    // store but was derived from upstream postulates that reach target.
    let mass_shell_id = axiom_id_from_name("mass_shell_condition");
    let mass_shell = Theorem {
        id: mass_shell_id,
        statement: Expr::Var("mass_shell_eq".into()),
        canonical: "mass_shell_eq".into(),
        latex: String::new(),
        proof: ProofTree::Axiom(target_id),
        depth: 1,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: vec![target_id],
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    };
    db.put_theorem(&mass_shell).unwrap();

    let engine = DerivationEngine::new();
    let ctx = engine.context_for_target(&target_id, &db).unwrap();

    // Both target and mass_shell must be flagged as forbidden.
    assert!(ctx.forbidden_axioms.contains(&target_id));
    assert!(ctx.forbidden_axioms.contains(&mass_shell_id));
}
```

- [ ] **Step 4: Run the test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-derive --test test_derivation_acyclicity`
Expected: FAIL — `context_for_target` doesn't exist.

- [ ] **Step 5: Add `context_for_target` to `DerivationEngine`**

In `engine/crates/derive/src/derivation.rs`, add (after `derive_by_strategy`, around line 88):

```rust
    /// Build a `DerivationContext` pre-populated with the forbidden-
    /// axiom set for `target_id`. Strategies that respect
    /// `ctx.forbidden_axioms` (via the GA / chain engine) will refuse
    /// to use any theorem that transitively cites the target as a
    /// premise. Suitable for any code path that knows the in-store id
    /// of the theorem being targeted.
    pub fn context_for_target(
        &self,
        target_id: &nasrudin_core::TheoremId,
        db: &nasrudin_rocks::TheoremDb,
    ) -> Result<DerivationContext, DeriveError> {
        let forbidden = db
            .forbidden_for_target(target_id)
            .map_err(|e| DeriveError::StoreError {
                reason: format!("forbidden_for_target({}): {e}", hex::encode(target_id)),
            })?;
        let mut ctx = DerivationContext::new();
        ctx.forbidden_axioms = forbidden;
        Ok(ctx)
    }

    /// Run a strategy targeted at a specific in-store theorem id. The
    /// returned context's `forbidden_axioms` field is set to
    /// `db.forbidden_for_target(target_id)`. Strategies that filter
    /// premises through `ctx.forbidden_axioms` will refuse to use the
    /// target or its dependents.
    pub fn derive_for_target(
        &self,
        target_id: &nasrudin_core::TheoremId,
        strategy: &dyn DerivationStrategy,
        db: &nasrudin_rocks::TheoremDb,
    ) -> Result<(Expr, DerivationContext), DeriveError> {
        let mut ctx = self.context_for_target(target_id, db)?;
        let result = strategy.execute(&self.store, &mut ctx)?;
        Ok((result, ctx))
    }
```

Add `StoreError` to `DeriveError` if missing. Open `engine/crates/derive/src/error.rs` and check; if absent, add a variant:

```rust
    #[error("Theorem-store error: {reason}")]
    StoreError { reason: String },
```

Add `use crate::axiom_store::AxiomStore;` and `use anyhow::Context as _;` only if not already at the top of the file. Add `use hex;` if not already imported (it's a workspace dep).

- [ ] **Step 6: Run the test to verify it passes**

Run: `cd engine && cargo test -p nasrudin-derive --test test_derivation_acyclicity`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/derive/src/derivation.rs engine/crates/derive/src/context.rs engine/crates/derive/src/error.rs engine/crates/derive/tests/test_derivation_acyclicity.rs
git commit -m "derive: derive_for_target threads forbidden-set through context

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 8: Wire forbidden filtering into the GA seed/mutation paths

**Files:**
- Modify: `engine/crates/ga/src/island.rs` (seed selection)
- Modify: `engine/crates/ga/src/selection.rs` (mutation premise picks, if any)

The GA picks axioms from `AxiomStore` at three points: initial seed (island.rs), mutation operators sampling a new axiom to introduce, and the chain-engine adapter. Each call site needs to thread the active `forbidden_axioms` set so the GA never seeds or mutates with a banned theorem.

- [ ] **Step 1: Map the call sites**

Run: `cd engine && grep -rn "store\.iter\(\|store\.by_domain\(\|store\.names\(" engine/crates/ga/src/`
Expected output: every place the GA pulls axioms from the store. Note each `file:line` for the steps below.

- [ ] **Step 2: Add a `forbidden` parameter to the seed function**

In `engine/crates/ga/src/island.rs`, locate the seed-selection method (the function that wraps `axiom` from the AxiomStore into a `Theorem` with `ProofTree::Axiom(id)` — search around line 60-200). Add a `forbidden: &HashSet<TheoremId>` parameter and switch from `store.iter()` / `store.by_domain(d)` to the `_excluding` variants from Task 6. Concrete edit pattern:

```rust
// Before:
for axiom in store.by_domain(&island_domain) { ... }

// After:
for axiom in store.by_domain_excluding(&island_domain, forbidden) { ... }
```

If the seed function has no `forbidden` parameter today, add it; supply `&HashSet::new()` from any caller that doesn't have a target. The GA driver that DOES have a target (the `target` field on `FitnessScore` and `nasrudin_ga::target` referenced in core/theorem.rs:114-116 docstring) already needs a target id — pass through the forbidden set built from that.

- [ ] **Step 3: Add a failing test for GA seed exclusion**

Create `engine/crates/ga/tests/test_seed_excludes_forbidden.rs` (use the existing test pattern in `engine/crates/ga/tests/`):

```rust
use nasrudin_core::{axiom_id_from_name, Domain};
use std::collections::HashSet;
// imports for whatever the seed function is named — adjust per Step 1's findings.

#[test]
fn seed_skips_forbidden_axioms() {
    let mut store = nasrudin_derive::AxiomStore::new();
    store.load_special_relativity_upstream();
    let mut forbidden = HashSet::new();
    forbidden.insert(axiom_id_from_name("rest_frame_psq_zero"));

    // Call the seed function with the forbidden set.
    let seeds = nasrudin_ga::island::seed_for_domain(&store, &Domain::SpecialRelativity, &forbidden);
    let names: Vec<&str> = seeds.iter().map(|t| t.canonical.as_str()).collect();
    assert!(!names.iter().any(|n| n == &"rest_frame_psq_zero"));
}
```

The exact API — `seed_for_domain` vs whatever the actual function name is — comes from Step 1's grep output. Adjust the test to match.

- [ ] **Step 4: Run the test, fix call sites until it passes**

Run: `cd engine && cargo test -p nasrudin-ga test_seed_excludes_forbidden`

Expected first run: FAIL (or compile error). Iterate: each compile error reveals another call site that needs the new `forbidden` parameter. Add `&HashSet::new()` to non-target callers. Once green, you've covered the seed path.

- [ ] **Step 5: Audit mutation-time premise picks**

If `engine/crates/ga/src/selection.rs` or any mutation operator pulls a fresh axiom mid-evolution (search for `store.iter` or `store.names()` in `selection.rs`, `mutation.rs` if present), thread the forbidden set through there too. Add a similar test if a new path is touched.

- [ ] **Step 6: Run the full GA test suite**

Run: `cd engine && cargo test -p nasrudin-ga`
Expected: existing tests still PASS, new exclusion test PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/ga/
git commit -m "ga: thread forbidden-axioms set through seed and mutation paths

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 9: Add a no-cheat dynamic check at theorem-write time

**Files:**
- Modify: `engine/crates/rocks/src/lib.rs` (extend `put_theorem` with self-cycle check)

Add a runtime guard in `put_theorem`: refuse to write a theorem whose own id appears in its own transitive ancestor set. This catches a class of bugs where a buggy strategy somehow constructs `T cites T` (currently impossible in `ProofTree`, but cheap insurance).

- [ ] **Step 1: Write the failing test**

Append to `engine/crates/rocks/tests/test_forbidden_for_target.rs`:

```rust
#[test]
fn put_theorem_rejects_self_cycle() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // T whose proof cites itself — should be rejected.
    let tid = [9u8, 0, 0, 0, 0, 0, 0, 0];
    let bad = Theorem {
        id: tid,
        statement: Expr::Var("self".into()),
        canonical: "self".into(),
        latex: String::new(),
        proof: ProofTree::ModusPonens {
            premise: Box::new(ProofTree::Axiom(tid)),
            implication: Box::new(ProofTree::Axiom(tid)),
        },
        depth: 1,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: vec![tid],
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    };
    let err = db.put_theorem(&bad).unwrap_err();
    assert!(
        format!("{err:?}").contains("cycle"),
        "error must mention cycle, got: {err:?}"
    );
}
```

The existing `compute_transitive_ancestors` already removes `theorem.id` from the result before returning, so we need to test the cycle BEFORE that removal step. Refactor the helper to expose both the raw set and the cleaned set, then use the raw set for the check.

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd engine && cargo test -p nasrudin-rocks --test test_forbidden_for_target put_theorem_rejects_self_cycle`
Expected: FAIL — current code silently accepts the self-cycle (the `acc.remove(&theorem.id)` in `compute_transitive_ancestors` swallows it).

- [ ] **Step 3: Add the cycle check in `compute_transitive_ancestors`**

Modify the helper added in Task 1 Step 3:

```rust
    fn compute_transitive_ancestors(
        &self,
        theorem: &nasrudin_core::Theorem,
    ) -> Result<Vec<nasrudin_core::TheoremId>> {
        use std::collections::BTreeSet;
        let mut acc: BTreeSet<nasrudin_core::TheoremId> =
            nasrudin_core::collect_axiom_ids(&theorem.proof);
        // Direct self-cycle: T's proof cites T as a leaf. Forbidden by
        // construction — every Theorem must be derivable from premises
        // that don't include itself.
        if acc.contains(&theorem.id) {
            anyhow::bail!(
                "Self-cycle detected: theorem {} cites itself in its own proof",
                hex::encode(theorem.id)
            );
        }
        let immediate: Vec<_> = acc.iter().copied().collect();
        for parent_id in &immediate {
            if let Some(parent_lineage) = self.get_lineage(parent_id)? {
                for a in parent_lineage.axiom_ancestors {
                    if a == theorem.id {
                        anyhow::bail!(
                            "Transitive cycle detected: theorem {} appears in its own ancestor closure (via {})",
                            hex::encode(theorem.id),
                            hex::encode(parent_id),
                        );
                    }
                    acc.insert(a);
                }
            }
        }
        Ok(acc.into_iter().collect())
    }
```

The earlier `acc.remove(&theorem.id)` line is replaced by the early bail. Note this changes the contract for existing axiom theorems where `proof = ProofTree::Axiom(self.id)` (see `island.rs:193`) — they'd now fail. We must special-case axioms: a `ProofTree::Axiom(id)` at the proof root referencing the theorem's own id is the canonical "this IS the axiom" leaf and is fine.

Refine the check:

```rust
        // A leaf-axiom theorem (proof is just `ProofTree::Axiom(self.id)`) is
        // the canonical "this IS the axiom" pattern from island.rs seeding;
        // it's not a cycle, just a self-reference at the leaf. Allow that
        // exact shape.
        let is_self_axiom_leaf =
            matches!(&theorem.proof, nasrudin_core::ProofTree::Axiom(id) if *id == theorem.id);
        if !is_self_axiom_leaf && acc.contains(&theorem.id) {
            anyhow::bail!(...);
        }
```

And drop the `theorem.id` from `acc` in the self-axiom-leaf case before the parent-lineage walk:

```rust
        if is_self_axiom_leaf {
            acc.remove(&theorem.id);
        }
```

- [ ] **Step 4: Run all rocks tests**

Run: `cd engine && cargo test -p nasrudin-rocks`
Expected: all tests PASS, including `put_theorem_rejects_self_cycle` and the existing chain test (which uses `axiom_theorem` whose proof is `ProofTree::Axiom(tid)` matching its own id — the self-axiom-leaf case is covered).

- [ ] **Step 5: Commit**

```bash
git add engine/crates/rocks/src/lib.rs engine/crates/rocks/tests/test_forbidden_for_target.rs
git commit -m "rocks: reject self-cycle and transitive cycles at put_theorem time

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 10: Run backfill on dev RocksDB and verify

**Files:** none modified — operational task.

- [ ] **Step 1: Locate the dev RocksDB path**

Run: `grep -rn "ROCKS_PATH\|rocksdb_path\|TheoremDb::new" engine/crates/api/src/ | head -10`

Identify the env var or config that points to the dev rocks dir (likely `NASRUDIN_ROCKSDB_PATH` or similar). Note its default value.

- [ ] **Step 2: Stop the running API process if any**

`ps aux | rg nasrudin-api` — if a dev API is running and holding the rocks dir locked, stop it. (RocksDB takes an exclusive process lock; the migration won't proceed otherwise.)

- [ ] **Step 3: Take a backup of the dev rocks dir**

```bash
cp -R "$NASRUDIN_ROCKSDB_PATH" "${NASRUDIN_ROCKSDB_PATH}.pre-acyclicity-backup-$(date +%Y%m%d)"
```

Substitute the actual path from Step 1.

- [ ] **Step 4: Run the backfill binary**

```bash
cd /Volumes/CORSAIR/code/personal/nasrudin/engine
cargo run --release --bin backfill_lineage -- "$NASRUDIN_ROCKSDB_PATH"
```

Expected output: `Backfill complete: <N> theorems processed in <T>s`. Note N — should match the theorem count.

- [ ] **Step 5: Verify a known dependency relationship**

Pick a known theorem id from the dev store. Open a `cargo run --bin <some_inspector>` or write a small script using `TheoremDb::list_dependents` — for the chosen id, the result should be non-empty if the theorem is foundational, empty if it's a leaf. Sanity-check at least one chain: open the theorem's `LineageRecord.axiom_ancestors`, pick one, and confirm `list_dependents` of that ancestor includes the original theorem.

- [ ] **Step 6: Restart the API and confirm it boots**

```bash
just dev-engine  # or whatever the API run target is
```

Expected: API boots, no panics, the no-cheat audit still passes (it walks AxiomStore — unchanged by this work).

- [ ] **Step 7: Commit (if any config changes)**

If the migration revealed a config file change is needed (env-var rename, log-level adjustment), commit it now. Otherwise no commit.

---

## Task 11: End-to-end smoke test with `mass_shell_condition` in the store

**Files:**
- Create: `engine/crates/derive/tests/test_acyclicity_emc2.rs`

This is the user-story test: with `mass_shell_condition` registered as a derived theorem in the TheoremDb, derive E=mc² with target tracking and confirm `mass_shell_condition` is NOT consulted.

- [ ] **Step 1: Write the test**

```rust
//! User-story test: `mass_shell_condition` lives in the TheoremDb as a
//! derived theorem (post-Phase-1 world). Deriving E=mc² with target
//! tracking enabled must NOT pull `mass_shell_condition` from the
//! AxiomStore, because mass_shell_condition's id is in the forbidden
//! set for the E=mc² target.

use nasrudin_core::{
    axiom_id_from_name, Domain, Expr, FitnessScore, ProofTree, Theorem, TheoremOrigin,
    VerificationStatus,
};
use nasrudin_derive::{AxiomStore, DerivationEngine};
use nasrudin_rocks::TheoremDb;
use tempfile::TempDir;

#[test]
fn deriving_emc2_target_excludes_mass_shell_condition() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // The "rest_energy" target. We use a synthetic id keyed off the
    // canonical name so AxiomStore name-lookups line up.
    let target_id = axiom_id_from_name("rest_energy");
    let target = stub_theorem(target_id, "rest_energy", &[], 0);
    db.put_theorem(&target).unwrap();

    // Register mass_shell_condition as a derived theorem whose proof
    // cites the target. (In production this gets generated by the
    // upstream-postulates derivation pipeline.)
    let ms_id = axiom_id_from_name("mass_shell_condition");
    let ms = stub_theorem(ms_id, "mass_shell_condition", &[target_id], 1);
    db.put_theorem(&ms).unwrap();

    // Build the engine and the forbidden context for the target.
    let mut engine = DerivationEngine::new();
    engine.store_mut().load_special_relativity_upstream();
    // Manually register a mass_shell_condition axiom (simulating the
    // legacy hot-tier registration) so the test can confirm the filter
    // would skip it.
    engine.store_mut().register(nasrudin_derive::Axiom {
        name: "mass_shell_condition".into(),
        domain: Domain::SpecialRelativity,
        statement: Expr::Var("mass_shell_eq".into()),
        description: "stub for filter test".into(),
    });

    let ctx = engine.context_for_target(&target_id, &db).unwrap();
    let visible: Vec<String> = engine
        .store()
        .iter_excluding(&ctx.forbidden_axioms)
        .map(|a| a.name)
        .collect();

    assert!(
        !visible.iter().any(|n| n == "mass_shell_condition"),
        "mass_shell_condition must be filtered out when deriving rest_energy target"
    );
    // Sanity: legitimate upstream axioms still visible.
    assert!(
        visible.iter().any(|n| n == "minkowski_invariant_def"),
        "upstream postulates must still be available"
    );
}

fn stub_theorem(id: nasrudin_core::TheoremId, name: &str, parents: &[nasrudin_core::TheoremId], depth: u32) -> Theorem {
    let proof = if parents.is_empty() {
        ProofTree::Axiom(id)
    } else if parents.len() == 1 {
        ProofTree::Axiom(parents[0])
    } else {
        ProofTree::EqChain(parents.iter().map(|p| ProofTree::Axiom(*p)).collect())
    };
    Theorem {
        id,
        statement: Expr::Var(name.into()),
        canonical: name.into(),
        latex: String::new(),
        proof,
        depth,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: parents.to_vec(),
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    }
}
```

- [ ] **Step 2: Run the test**

Run: `cd engine && cargo test -p nasrudin-derive --test test_acyclicity_emc2`
Expected: PASS.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/derive/tests/test_acyclicity_emc2.rs
git commit -m "derive: e2e test — deriving E=mc² target excludes mass_shell_condition

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 12: Final verification — full test suite + check

**Files:** none modified — verification task.

- [ ] **Step 1: Run all engine tests**

```bash
cd /Volumes/CORSAIR/code/personal/nasrudin/engine
cargo test --workspace
```

Expected: every test passes, no warnings introduced.

- [ ] **Step 2: Run cargo check across the workspace**

```bash
cd /Volumes/CORSAIR/code/personal/nasrudin/engine
cargo check --workspace --all-targets
```

Expected: clean, no warnings.

- [ ] **Step 3: Run the project's standard test recipe**

```bash
cd /Volumes/CORSAIR/code/personal/nasrudin
just test-engine
```

Expected: green.

- [ ] **Step 4: Manual sanity — boot the API**

```bash
just dev-engine
```

Expected: clean boot, no-cheat audit passes, API answers `/api/health`.

- [ ] **Step 5: Final commit (only if any cleanup edits were needed)**

If the verification surfaced no changes, no commit. Otherwise:

```bash
git add <files>
git commit -m "<concise description>

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Out of Scope / Follow-ups

- **Trivial-precursor exclusion (semantic).** The dependency-acyclicity check handles cycles in the proof DAG. It does NOT handle the case "X is a one-substitution-away-from Y, so using X to prove Y is barely a derivation" (e.g., a stored mass_shell_condition theorem whose proof cites only upstream postulates is, by the rules in this plan, a permitted premise for E=mc² — even if a human would call it "near-trivial cheating"). If we later want to enforce that, extend `engine/crates/derive/src/no_cheat_audit.rs` with a `(target_canonical, forbidden_precursor_canonicals)` map and add a canonical-keyed index (`CF_BY_CANONICAL`) on the TheoremDb. Out of scope for this plan.
- **Per-strategy honoring of `ctx.forbidden_axioms`.** The hardcoded-name strategies in `strategies.rs` (e.g., `DeriveRestEnergy::execute` which calls `store.get("mass_shell_condition")` directly) ignore `forbidden_axioms`. They'd need to check the set explicitly and bail with `DeriveError::AxiomForbidden` if their hardcoded premise is forbidden. Punt to a follow-up since the GA path (the high-traffic consumer) is covered by Task 8.
- **Reverse-deps GC on theorem deletion.** This plan assumes theorems are write-only (matches current production behavior — there's no `delete_theorem` method in `TheoremDb`). If deletion is added later, the deleter must also wipe the corresponding reverse-deps rows.
