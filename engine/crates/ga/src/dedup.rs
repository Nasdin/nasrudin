//! Deduplication filter using xxHash64 canonical hashes.
//!
//! Tracks seen theorem IDs to prevent duplicate candidates from
//! consuming compute resources.

use std::collections::HashSet;

use nasrudin_core::TheoremId;

/// Fast deduplication filter for theorem candidates.
#[derive(Debug, Clone)]
pub struct DedupFilter {
    seen: HashSet<TheoremId>,
}

impl DedupFilter {
    /// Create a new empty dedup filter.
    pub fn new() -> Self {
        Self {
            seen: HashSet::new(),
        }
    }

    /// Create a dedup filter with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            seen: HashSet::with_capacity(capacity),
        }
    }

    /// Check if a theorem ID has been seen before.
    /// Returns `true` if it was already seen (duplicate).
    pub fn is_duplicate(&self, id: &TheoremId) -> bool {
        self.seen.contains(id)
    }

    /// Mark a theorem ID as seen. Returns `true` if it was new.
    pub fn insert(&mut self, id: TheoremId) -> bool {
        self.seen.insert(id)
    }

    /// Check and insert in one operation.
    /// Returns `true` if the ID is new (not a duplicate).
    pub fn check_and_insert(&mut self, id: TheoremId) -> bool {
        self.seen.insert(id)
    }

    /// Number of unique IDs seen so far.
    pub fn len(&self) -> usize {
        self.seen.len()
    }

    /// Check if the filter is empty.
    pub fn is_empty(&self) -> bool {
        self.seen.is_empty()
    }

    /// Clear all seen entries.
    pub fn clear(&mut self) {
        self.seen.clear();
    }
}

impl Default for DedupFilter {
    fn default() -> Self {
        Self::new()
    }
}
