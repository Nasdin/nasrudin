//! Generate `nsk_<kind>_<base32-secret>` keys.

use data_encoding::BASE32_NOPAD;
use rand::RngCore;

pub struct GeneratedKey {
    /// Full key as the user sees it. Only returned to the client once.
    pub full: String,
    /// First 12 chars (or 14 for worker keys), stored cleartext for lookup.
    pub prefix: String,
    /// Argon2 hash of `full` — what we persist.
    pub hash: String,
}

pub fn generate(kind: &str) -> anyhow::Result<GeneratedKey> {
    let mut buf = [0u8; 24];
    rand::rng().fill_bytes(&mut buf);
    let secret = BASE32_NOPAD.encode(&buf).to_lowercase();
    let full = format!("nsk_{kind}_{secret}");
    let prefix_len = match kind {
        "worker" => 14,
        _ => 12,
    };
    let prefix: String = full.chars().take(prefix_len).collect();
    let hash = password_auth::generate_hash(&full);
    Ok(GeneratedKey { full, prefix, hash })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn live_key_prefix_is_12_chars() {
        let k = generate("live").unwrap();
        assert!(k.full.starts_with("nsk_live_"));
        assert_eq!(k.prefix.len(), 12);
        assert!(k.full.starts_with(&k.prefix));
    }

    #[test]
    fn worker_key_prefix_is_14_chars() {
        let k = generate("worker").unwrap();
        assert!(k.full.starts_with("nsk_worker_"));
        assert_eq!(k.prefix.len(), 14);
        assert!(k.full.starts_with(&k.prefix));
    }

    #[test]
    fn hash_verifies() {
        let k = generate("live").unwrap();
        assert!(password_auth::verify_password(&k.full, &k.hash).is_ok());
    }
}
