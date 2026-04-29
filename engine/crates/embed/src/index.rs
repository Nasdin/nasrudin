// stub — implemented in Task 5
use anyhow::Result;
use nasrudin_core::TheoremId;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

use crate::format::IndexHeader;

#[derive(Debug, Clone)]
pub struct CosinePoint(pub Vec<f32>);

impl instant_distance::Point for CosinePoint {
    fn distance(&self, other: &Self) -> f32 {
        let mut dot = 0.0f32;
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            dot += a * b;
        }
        1.0 - dot
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct NearestHit {
    pub theorem_id: TheoremId,
    pub distance: f32,
}

pub struct EmbeddingIndex;

impl EmbeddingIndex {
    pub fn open(_path: impl AsRef<Path>) -> Result<Self> {
        anyhow::bail!("EmbeddingIndex::open not yet implemented")
    }
    pub fn len(&self) -> usize {
        0
    }
    pub fn is_empty(&self) -> bool {
        true
    }
    pub fn nearest(&self, _query: &[f32], _k: usize) -> Vec<NearestHit> {
        Vec::new()
    }
    pub fn header(&self) -> IndexHeader {
        IndexHeader {
            version: 1,
            dim: 384,
            count: 0,
            built_at_millis: 0,
        }
    }
}

pub fn sidecar_path(main: &Path) -> PathBuf {
    let mut p = main.as_os_str().to_owned();
    p.push(".hnsw");
    PathBuf::from(p)
}
