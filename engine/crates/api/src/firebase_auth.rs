//! Firebase ID token verification.
//!
//! Verifies short-lived (≤1h) Google-signed RS256 JWTs against Google's
//! published JWKs. Used exactly once per session by
//! `POST /api/auth/firebase-session` to exchange an ID token for an
//! axum-login session cookie. After exchange, the cookie is the source of
//! truth and Firebase is not consulted again.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

use jsonwebtoken::DecodingKey;
use serde::Deserialize;
use thiserror::Error;
use tokio::sync::RwLock;

const GOOGLE_JWKS_URL: &str =
    "https://www.googleapis.com/robot/v1/metadata/x509/securetoken@system.gserviceaccount.com";
const JWKS_REFRESH_INTERVAL: Duration = Duration::from_secs(3600);
const ISS_PREFIX: &str = "https://securetoken.google.com/";

/// Verified claims extracted from a Firebase ID token. Subset of the
/// fields Firebase emits — only what we use.
#[derive(Debug, Clone)]
pub struct FirebaseClaims {
    /// JWT `sub` — Firebase's stable user id.
    pub uid: String,
    pub email: String,
    pub email_verified: bool,
    pub name: Option<String>,
    pub picture: Option<String>,
    /// e.g. `"password"`, `"google.com"`. From `firebase.sign_in_provider`.
    pub sign_in_provider: String,
}

#[derive(Debug, Error)]
pub enum VerifyError {
    #[error("token expired")]
    Expired,
    #[error("wrong issuer")]
    WrongIssuer,
    #[error("wrong audience")]
    WrongAudience,
    #[error("bad signature")]
    BadSignature,
    #[error("malformed token: {0}")]
    MalformedToken(String),
    #[error("missing required claim: {0}")]
    MissingClaim(&'static str),
    #[error("jwks fetch failed: {0}")]
    JwksFetch(String),
}

/// Cache of Google's public keys, keyed by `kid` (key id from the JWT
/// header). Fetched lazily on first use; refreshed when an unknown `kid`
/// is encountered or when the cache is older than `JWKS_REFRESH_INTERVAL`.
///
/// Tests can construct a pre-populated cache with `for_test` to inject
/// their own keypair without hitting the network.
pub struct JwksCache {
    inner: RwLock<JwksCacheInner>,
}

struct JwksCacheInner {
    keys: HashMap<String, DecodingKey>,
    fetched_at: Option<Instant>,
}

impl JwksCache {
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(JwksCacheInner {
                keys: HashMap::new(),
                fetched_at: None,
            }),
        }
    }

    /// Build a cache pre-populated with a known keyset. Exposed for tests
    /// and for the test_app harness to inject keypairs without network IO.
    pub fn for_test(keys: HashMap<String, DecodingKey>) -> Self {
        Self {
            inner: RwLock::new(JwksCacheInner {
                keys,
                fetched_at: Some(Instant::now()),
            }),
        }
    }

    /// Force a fetch (used at boot to surface JWKs-fetch errors early).
    pub async fn warm(&self) -> Result<(), VerifyError> {
        self.refresh().await
    }

    /// Look up a decoding key by `kid`. If absent and the cache is older
    /// than 1 hour OR was never fetched, re-fetch and try once more.
    pub(crate) async fn get(&self, kid: &str) -> Option<DecodingKey> {
        {
            let guard = self.inner.read().await;
            if let Some(k) = guard.keys.get(kid) {
                return Some(k.clone());
            }
            if guard
                .fetched_at
                .map(|t| t.elapsed() < JWKS_REFRESH_INTERVAL)
                .unwrap_or(false)
            {
                return None;
            }
        }
        // Cache miss + stale (or empty) → refresh and look again.
        if self.refresh().await.is_err() {
            return None;
        }
        let guard = self.inner.read().await;
        guard.keys.get(kid).cloned()
    }

    async fn refresh(&self) -> Result<(), VerifyError> {
        let resp = reqwest::get(GOOGLE_JWKS_URL)
            .await
            .map_err(|e| VerifyError::JwksFetch(format!("{e}")))?
            .error_for_status()
            .map_err(|e| VerifyError::JwksFetch(format!("{e}")))?;
        let body: HashMap<String, String> = resp
            .json()
            .await
            .map_err(|e| VerifyError::JwksFetch(format!("{e}")))?;
        // Google's secure-token endpoint returns `{ kid: x509-pem-string }`.
        let mut keys = HashMap::with_capacity(body.len());
        for (kid, pem) in body {
            match DecodingKey::from_rsa_pem(pem.as_bytes()) {
                Ok(k) => {
                    keys.insert(kid, k);
                }
                Err(e) => {
                    tracing::warn!(kid = %kid, error = %e, "jwks: failed to parse pem; skipping");
                }
            }
        }
        if keys.is_empty() {
            return Err(VerifyError::JwksFetch("no usable keys in response".into()));
        }
        let mut guard = self.inner.write().await;
        guard.keys = keys;
        guard.fetched_at = Some(Instant::now());
        Ok(())
    }
}

impl Default for JwksCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Re-exported for callers (handlers + tests) that need to construct a
/// shared cache.
pub type SharedJwks = Arc<JwksCache>;

/// Wire shape of the JWT claims, before mapping into `FirebaseClaims`.
/// Standard JWT claims (iss, aud, exp, iat) are validated by jsonwebtoken
/// itself; we only deserialize the fields we need to expose.
#[derive(Deserialize)]
struct WireClaims {
    sub: String,
    email: Option<String>,
    email_verified: Option<bool>,
    name: Option<String>,
    picture: Option<String>,
    firebase: WireFirebaseExt,
}

#[derive(Deserialize)]
struct WireFirebaseExt {
    sign_in_provider: String,
}

/// Verify a Firebase ID token (RS256 JWT). Returns the verified claims on
/// success. See `VerifyError` for failure modes.
pub async fn verify_id_token(
    token: &str,
    project_id: &str,
    jwks: &JwksCache,
) -> Result<FirebaseClaims, VerifyError> {
    use jsonwebtoken::{Algorithm, Validation, decode, decode_header};

    // 1. Parse header → grab kid.
    let header =
        decode_header(token).map_err(|e| VerifyError::MalformedToken(format!("{e}")))?;
    if header.alg != Algorithm::RS256 {
        // Algorithm-confusion defense: refuse anything that's not RS256.
        return Err(VerifyError::BadSignature);
    }
    let kid = header
        .kid
        .ok_or_else(|| VerifyError::MalformedToken("missing kid".into()))?;

    // 2. Look up the public key (refreshes JWKs if needed).
    let key = jwks
        .get(&kid)
        .await
        .ok_or(VerifyError::BadSignature)?;

    // 3. Validate signature + standard claims.
    let mut validation = Validation::new(Algorithm::RS256);
    validation.set_audience(&[project_id]);
    validation.set_issuer(&[format!("{ISS_PREFIX}{project_id}")]);
    validation.leeway = 60; // small clock-skew tolerance on iat / nbf
    validation.validate_exp = true;
    validation.required_spec_claims =
        std::collections::HashSet::from(["exp".into(), "iat".into(), "aud".into(), "iss".into()]);

    let data = match decode::<WireClaims>(token, &key, &validation) {
        Ok(d) => d,
        Err(e) => {
            return Err(match e.kind() {
                jsonwebtoken::errors::ErrorKind::ExpiredSignature => VerifyError::Expired,
                jsonwebtoken::errors::ErrorKind::InvalidIssuer => VerifyError::WrongIssuer,
                jsonwebtoken::errors::ErrorKind::InvalidAudience => VerifyError::WrongAudience,
                jsonwebtoken::errors::ErrorKind::InvalidSignature
                | jsonwebtoken::errors::ErrorKind::InvalidAlgorithm => VerifyError::BadSignature,
                _ => VerifyError::MalformedToken(format!("{e}")),
            });
        }
    };

    let wire = data.claims;
    if wire.sub.is_empty() {
        return Err(VerifyError::MissingClaim("sub"));
    }
    let email = wire.email.ok_or(VerifyError::MissingClaim("email"))?;

    Ok(FirebaseClaims {
        uid: wire.sub,
        email,
        email_verified: wire.email_verified.unwrap_or(false),
        name: wire.name,
        picture: wire.picture,
        sign_in_provider: wire.firebase.sign_in_provider,
    })
}
