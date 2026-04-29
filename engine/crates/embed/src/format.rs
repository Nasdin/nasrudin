// stub — implemented in Task 2
pub const INDEX_MAGIC: [u8; 4] = *b"NEMB";
pub const INDEX_VERSION: u32 = 1;
pub const EMBED_DIM: u32 = 384;

#[derive(Debug, Clone, Copy)]
pub struct IndexHeader {
    pub version: u32,
    pub dim: u32,
    pub count: u32,
    pub built_at_millis: i64,
}
