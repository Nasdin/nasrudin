use crate::theorem::TheoremId;
use xxhash_rust::xxh64::xxh64;

/// Compute a stable 8-byte theorem ID from the canonical expression string.
///
/// Uses xxHash64 for fast, high-quality hashing of the canonical form.
pub fn compute_theorem_id(canonical: &str) -> TheoremId {
    let hash = xxh64(canonical.as_bytes(), 0);
    hash.to_le_bytes()
}

/// Convert a TheoremId to its hex string representation.
pub fn theorem_id_to_hex(id: &TheoremId) -> String {
    hex::encode(id)
}

/// Parse a hex string back into a TheoremId.
pub fn hex_to_theorem_id(hex_str: &str) -> Result<TheoremId, hex::FromHexError> {
    let bytes = hex::decode(hex_str)?;
    let mut id = [0u8; 8];
    id.copy_from_slice(&bytes[..8]);
    Ok(id)
}
