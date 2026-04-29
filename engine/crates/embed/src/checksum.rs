// stub — implemented in Task 3
use anyhow::Result;
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexChecksum {
    pub hex: String,
    pub bytes: u64,
}

pub fn compute_index_checksum(_path: &Path) -> Result<IndexChecksum> {
    Ok(IndexChecksum {
        hex: String::new(),
        bytes: 0,
    })
}
