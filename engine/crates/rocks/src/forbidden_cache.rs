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
//! from this cache so the next reader rescans. We do NOT pre-warm `T`
//! itself — its forbidden set is `{T}` (a leaf, no dependents yet),
//! and the first `forbidden_for_target(T)` call after the write will
//! populate it on demand.

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

    #[cfg(test)]
    pub fn invalidate_all_for_test(&self) {
        self.inner.lock().unwrap().clear();
    }
}
