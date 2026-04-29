//! Memory-mapped read-only `corpus.embed` + HNSW lookup.
//!
//! `EmbeddingIndex::open(path)` mmaps the index file and loads the
//! sidecar HNSW. `nearest(vec, k)` returns the top-`k` (TheoremId,
//! cosine-distance) pairs.

use anyhow::{Context, Result};
use instant_distance::{HnswMap, Search};
use memmap2::Mmap;
use nasrudin_core::TheoremId;
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::format::{IndexHeader, EMBED_DIM, HEADER_SIZE, RECORD_SIZE};

/// Cosine-distance (1 − cosine_similarity) between unit-normalised
/// vectors. fastembed's BGE outputs are L2-normalised, so this is
/// equivalent to using dot-product as similarity.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CosinePoint(pub Vec<f32>);

impl instant_distance::Point for CosinePoint {
    fn distance(&self, other: &Self) -> f32 {
        let mut dot = 0.0f32;
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            dot += a * b;
        }
        // Distance = 1 − similarity; assumes L2-normalised inputs.
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

    use instant_distance::Point;

    #[test]
    fn cosine_point_distance_zero_for_identical() {
        let p = CosinePoint(vec![0.5, 0.5, 0.5, 0.5]);
        let q = CosinePoint(vec![0.5, 0.5, 0.5, 0.5]);
        let d = p.distance(&q);
        assert!((d - 0.0).abs() < 1e-6);
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
