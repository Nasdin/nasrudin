//! BLAKE3 checksum over a built `corpus.embed`.
//!
//! Workers download `/api/embed/index.bin` and compare the `Sha-Embed`
//! HTTP header (which carries the BLAKE3 hex digest) against this
//! function's output before swapping the file in. Mismatch =
//! corrupted transfer = retry.

use anyhow::Result;
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexChecksum {
    /// Hex-encoded BLAKE3-256 digest.
    pub hex: String,
    /// Total bytes hashed.
    pub bytes: u64,
}

/// Stream-hash the entire file at `path`.
pub fn compute_index_checksum(path: &Path) -> Result<IndexChecksum> {
    use std::io::Read;
    let mut file = std::fs::File::open(path)?;
    let mut hasher = blake3::Hasher::new();
    let mut buf = [0u8; 64 * 1024];
    let mut total: u64 = 0;
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
        total += n as u64;
    }
    Ok(IndexChecksum {
        hex: hasher.finalize().to_hex().to_string(),
        bytes: total,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::tempdir;

    #[test]
    fn empty_file_has_known_blake3_digest() {
        let dir = tempdir().unwrap();
        let p = dir.path().join("empty.bin");
        std::fs::write(&p, []).unwrap();
        let cs = compute_index_checksum(&p).unwrap();
        assert_eq!(
            cs.hex,
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
            "BLAKE3 of empty input is well-known"
        );
        assert_eq!(cs.bytes, 0);
    }

    #[test]
    fn deterministic_across_calls() {
        let dir = tempdir().unwrap();
        let p = dir.path().join("data.bin");
        let mut f = std::fs::File::create(&p).unwrap();
        f.write_all(b"hello, embeddings").unwrap();
        let a = compute_index_checksum(&p).unwrap();
        let b = compute_index_checksum(&p).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn different_content_diverges() {
        let dir = tempdir().unwrap();
        let p1 = dir.path().join("a.bin");
        let p2 = dir.path().join("b.bin");
        std::fs::write(&p1, b"alpha").unwrap();
        std::fs::write(&p2, b"beta").unwrap();
        let a = compute_index_checksum(&p1).unwrap();
        let b = compute_index_checksum(&p2).unwrap();
        assert_ne!(a.hex, b.hex);
    }
}
