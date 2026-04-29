//! AES-256-GCM helpers for encrypting BYO API keys at rest.
//!
//! Wire format: `[12-byte nonce][ciphertext + 16-byte auth tag]`.
//! Key: 32 bytes from `NASRUDIN_KEY_ENCRYPT` (base64-encoded in env).

use aes_gcm::aead::{Aead, KeyInit};
use aes_gcm::{Aes256Gcm, Key, Nonce};
use anyhow::{Context, Result};
use rand_core::{OsRng, RngCore};

/// Wire-format ciphertext + nonce.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncryptedKey(pub Vec<u8>);

const NONCE_LEN: usize = 12;

pub fn encrypt(plaintext: &str, key_bytes: &[u8; 32]) -> Result<EncryptedKey> {
    let key: &Key<Aes256Gcm> = key_bytes.into();
    let cipher = Aes256Gcm::new(key);
    let mut nonce = [0u8; NONCE_LEN];
    OsRng.fill_bytes(&mut nonce);
    let ct = cipher
        .encrypt(Nonce::from_slice(&nonce), plaintext.as_bytes())
        .map_err(|e| anyhow::anyhow!("aes-gcm encrypt: {e}"))?;
    let mut out = Vec::with_capacity(NONCE_LEN + ct.len());
    out.extend_from_slice(&nonce);
    out.extend_from_slice(&ct);
    Ok(EncryptedKey(out))
}

pub fn decrypt(encrypted: &EncryptedKey, key_bytes: &[u8; 32]) -> Result<String> {
    if encrypted.0.len() < NONCE_LEN {
        anyhow::bail!("encrypted key too short");
    }
    let key: &Key<Aes256Gcm> = key_bytes.into();
    let cipher = Aes256Gcm::new(key);
    let (nonce, ct) = encrypted.0.split_at(NONCE_LEN);
    let pt = cipher
        .decrypt(Nonce::from_slice(nonce), ct)
        .map_err(|e| anyhow::anyhow!("aes-gcm decrypt: {e}"))?;
    String::from_utf8(pt).context("decrypted bytes are not utf-8")
}

/// Last 4 chars of the plaintext key, for UI display. Truncates safely
/// for short keys.
pub fn key_hint(plaintext: &str) -> String {
    let n = plaintext.chars().count();
    if n <= 4 {
        plaintext.to_string()
    } else {
        plaintext.chars().skip(n - 4).collect()
    }
}

/// Decode a base64-encoded 32-byte key from the env var. Returns None
/// when the var is unset or invalid; callers gate the endpoints
/// accordingly.
pub fn load_encrypt_key_from_env() -> Option<[u8; 32]> {
    use base64::Engine;
    let raw = std::env::var("NASRUDIN_KEY_ENCRYPT").ok()?;
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return None;
    }
    let decoded = base64::engine::general_purpose::STANDARD
        .decode(trimmed)
        .ok()?;
    if decoded.len() != 32 {
        tracing::warn!(
            "NASRUDIN_KEY_ENCRYPT decoded to {} bytes; expected 32",
            decoded.len()
        );
        return None;
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&decoded);
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn k() -> [u8; 32] {
        [7u8; 32]
    }

    #[test]
    fn round_trip_roundtrips() {
        let pt = "sk-ant-api03-1234567890abcdef".to_string();
        let enc = encrypt(&pt, &k()).unwrap();
        let dec = decrypt(&enc, &k()).unwrap();
        assert_eq!(dec, pt);
    }

    #[test]
    fn different_nonces_yield_different_ciphertexts() {
        let pt = "same-input";
        let a = encrypt(pt, &k()).unwrap();
        let b = encrypt(pt, &k()).unwrap();
        assert_ne!(a, b, "fresh nonce per call ⇒ different ciphertext");
    }

    #[test]
    fn wrong_key_fails_decryption() {
        let pt = "secret";
        let enc = encrypt(pt, &k()).unwrap();
        let mut wrong = k();
        wrong[0] ^= 0xff;
        assert!(decrypt(&enc, &wrong).is_err());
    }

    #[test]
    fn truncated_ciphertext_fails_decryption() {
        let enc = encrypt("hello", &k()).unwrap();
        let truncated = EncryptedKey(enc.0[..8].to_vec());
        assert!(decrypt(&truncated, &k()).is_err());
    }

    #[test]
    fn key_hint_returns_last_4_chars() {
        assert_eq!(key_hint("sk-ant-api03-1234"), "1234");
        assert_eq!(key_hint("ab"), "ab");
        assert_eq!(key_hint(""), "");
    }
}
