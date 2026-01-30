//! Deduplication filter using a Bloom filter for memory-efficient duplicate detection.
//!
//! Tracks seen theorem IDs to prevent duplicate candidates from
//! consuming compute resources. Uses a probabilistic Bloom filter
//! instead of a HashSet to support millions of candidates per island
//! with bounded memory (~12 MB per island at 10M capacity).
//!
//! False positives (skipping a novel candidate) are acceptable in the
//! GA context since we generate far more candidates than we need.

use bloomfilter::Bloom;
use nasrudin_core::TheoremId;

/// Default capacity if none specified.
const DEFAULT_BLOOM_CAPACITY: usize = 10_000_000;

/// False positive rate: 1%. A false positive just means we skip a
/// candidate that could have been novel — acceptable tradeoff for GA.
const FALSE_POSITIVE_RATE: f64 = 0.01;

/// Memory-efficient deduplication filter for theorem candidates.
///
/// Backed by a Bloom filter, which is probabilistic: `is_duplicate`
/// may return `true` for items never inserted (false positive), but
/// will never return `false` for items that were inserted.
pub struct DedupFilter {
    bloom: Bloom<TheoremId>,
    count: usize,
}

impl DedupFilter {
    /// Create a new dedup filter with default capacity (10M items).
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_BLOOM_CAPACITY)
    }

    /// Create a dedup filter with the given item capacity.
    ///
    /// Memory usage scales with capacity: ~12 MB at 10M items with 1% FPR.
    pub fn with_capacity(capacity: usize) -> Self {
        let bloom = Bloom::new_for_fp_rate(capacity, FALSE_POSITIVE_RATE);
        Self { bloom, count: 0 }
    }

    /// Check if a theorem ID has been seen before.
    /// Returns `true` if it was already seen (or a false positive).
    pub fn is_duplicate(&self, id: &TheoremId) -> bool {
        self.bloom.check(id)
    }

    /// Mark a theorem ID as seen. Returns `true` if it appeared new
    /// (was not already in the filter).
    pub fn insert(&mut self, id: TheoremId) -> bool {
        if self.bloom.check(&id) {
            false
        } else {
            self.bloom.set(&id);
            self.count += 1;
            true
        }
    }

    /// Check and insert in one operation.
    /// Returns `true` if the ID is new (not a duplicate).
    pub fn check_and_insert(&mut self, id: TheoremId) -> bool {
        if self.bloom.check(&id) {
            false
        } else {
            self.bloom.set(&id);
            self.count += 1;
            true
        }
    }

    /// Approximate number of unique IDs inserted.
    ///
    /// This is exact for insertions but does not account for
    /// false-positive rejections in `insert`/`check_and_insert`.
    pub fn len(&self) -> usize {
        self.count
    }

    /// Check if the filter is empty.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Clear the filter, resetting to empty state.
    pub fn clear(&mut self) {
        self.bloom.clear();
        self.count = 0;
    }
}

impl Default for DedupFilter {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for DedupFilter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DedupFilter")
            .field("count", &self.count)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bloom_dedup_basics() {
        let mut filter = DedupFilter::with_capacity(1000);

        let id1: TheoremId = [1, 2, 3, 4, 5, 6, 7, 8];
        let id2: TheoremId = [8, 7, 6, 5, 4, 3, 2, 1];

        // New IDs should not be duplicates
        assert!(!filter.is_duplicate(&id1));
        assert!(!filter.is_duplicate(&id2));

        // Insert returns true for new items
        assert!(filter.insert(id1));
        assert_eq!(filter.len(), 1);

        // Now it's a duplicate
        assert!(filter.is_duplicate(&id1));
        // Insert returns false for duplicates
        assert!(!filter.insert(id1));
        assert_eq!(filter.len(), 1);

        // id2 is still new
        assert!(filter.check_and_insert(id2));
        assert_eq!(filter.len(), 2);

        // id2 is now a duplicate
        assert!(!filter.check_and_insert(id2));
        assert_eq!(filter.len(), 2);
    }

    #[test]
    fn bloom_dedup_clear() {
        let mut filter = DedupFilter::with_capacity(1000);
        let id: TheoremId = [1, 0, 0, 0, 0, 0, 0, 0];
        filter.insert(id);
        assert!(!filter.is_empty());

        filter.clear();
        assert!(filter.is_empty());
        assert_eq!(filter.len(), 0);
        // After clear, the ID should no longer be detected
        assert!(!filter.is_duplicate(&id));
    }
}
