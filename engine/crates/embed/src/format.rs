//! On-disk format for `corpus.embed`.
//!
//! ```text
//! ┌─ Header (64 bytes, little-endian) ──────────────────────┐
//! │  0..4    magic     b"NEMB"                              │
//! │  4..8    version   u32 = 1                              │
//! │  8..12   dim       u32 = 384                            │
//! │  12..16  count     u32 — number of records              │
//! │  16..24  built_at  i64 unix-millis                      │
//! │  24..32  reserved  must be 0                            │
//! │  32..64  padding   must be 0                            │
//! ├─ Records (count × 1544 bytes) ───────────────────────────┤
//! │   8     TheoremId       [u8; 8]                         │
//! │   1536  vector          [f32; 384] little-endian        │
//! └──────────────────────────────────────────────────────────┘
//! ```
//!
//! The header is 64 bytes (cache-line aligned) so records start at a
//! 64-byte boundary. The flat layout means `EmbeddingIndex` can mmap
//! the file and slice records by offset without parsing.

pub const INDEX_MAGIC: [u8; 4] = *b"NEMB";
pub const INDEX_VERSION: u32 = 1;
pub const EMBED_DIM: u32 = 384;
pub const HEADER_SIZE: usize = 64;
pub const RECORD_SIZE: usize = 8 + (EMBED_DIM as usize) * 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IndexHeader {
    pub version: u32,
    pub dim: u32,
    pub count: u32,
    pub built_at_millis: i64,
}

impl IndexHeader {
    pub fn encode(&self) -> [u8; HEADER_SIZE] {
        let mut out = [0u8; HEADER_SIZE];
        out[0..4].copy_from_slice(&INDEX_MAGIC);
        out[4..8].copy_from_slice(&self.version.to_le_bytes());
        out[8..12].copy_from_slice(&self.dim.to_le_bytes());
        out[12..16].copy_from_slice(&self.count.to_le_bytes());
        out[16..24].copy_from_slice(&self.built_at_millis.to_le_bytes());
        out
    }

    pub fn decode(bytes: &[u8]) -> anyhow::Result<Self> {
        if bytes.len() < HEADER_SIZE {
            anyhow::bail!("header too short: {} < {HEADER_SIZE}", bytes.len());
        }
        if bytes[0..4] != INDEX_MAGIC {
            anyhow::bail!("bad magic: {:?}", &bytes[0..4]);
        }
        let version = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        if version != INDEX_VERSION {
            anyhow::bail!("unsupported index version {version} (this build supports {INDEX_VERSION})");
        }
        let dim = u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]);
        if dim != EMBED_DIM {
            anyhow::bail!("dim mismatch: file has {dim}, build expects {EMBED_DIM}");
        }
        let count = u32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]);
        let built_at_millis = i64::from_le_bytes([
            bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
        ]);
        Ok(Self {
            version,
            dim,
            count,
            built_at_millis,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_round_trips() {
        let h = IndexHeader {
            version: 1,
            dim: 384,
            count: 12345,
            built_at_millis: 1_700_000_000_000,
        };
        let encoded = h.encode();
        assert_eq!(encoded.len(), HEADER_SIZE);
        assert_eq!(&encoded[0..4], &INDEX_MAGIC);
        let decoded = IndexHeader::decode(&encoded).unwrap();
        assert_eq!(decoded, h);
    }

    #[test]
    fn header_rejects_wrong_magic() {
        let mut bad = IndexHeader {
            version: 1,
            dim: 384,
            count: 0,
            built_at_millis: 0,
        }
        .encode();
        bad[0] = b'X';
        assert!(IndexHeader::decode(&bad).is_err());
    }

    #[test]
    fn header_rejects_wrong_version() {
        let mut bad = IndexHeader {
            version: 999,
            dim: 384,
            count: 0,
            built_at_millis: 0,
        }
        .encode();
        bad[0..4].copy_from_slice(&INDEX_MAGIC);
        assert!(IndexHeader::decode(&bad).is_err());
    }

    #[test]
    fn header_rejects_wrong_dim() {
        let mut bad = IndexHeader {
            version: 1,
            dim: 256,
            count: 0,
            built_at_millis: 0,
        }
        .encode();
        bad[0..4].copy_from_slice(&INDEX_MAGIC);
        bad[4..8].copy_from_slice(&1u32.to_le_bytes());
        assert!(IndexHeader::decode(&bad).is_err());
    }

    #[test]
    fn record_size_is_8_plus_dim_bytes() {
        assert_eq!(RECORD_SIZE, 8 + 384 * 4);
    }
}
