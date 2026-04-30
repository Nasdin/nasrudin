//! Unit tests for `firebase_auth::verify_id_token`.
//!
//! Generates a fresh RSA keypair per test, mints test tokens with it,
//! injects the public key into a JwksCache via `for_test`, and verifies.
//! No network access; no Firebase emulator required.

use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use jsonwebtoken::{Algorithm, DecodingKey, EncodingKey, Header, encode};
use rsa::{
    RsaPrivateKey,
    pkcs1::EncodeRsaPrivateKey,
    pkcs8::{EncodePublicKey, LineEnding},
};
use serde::Serialize;

use physics_api::firebase_auth::{JwksCache, VerifyError, verify_id_token};

const TEST_PROJECT_ID: &str = "test-project";
const TEST_KID: &str = "test-kid-1";

#[derive(Serialize)]
struct WireClaims {
    sub: String,
    email: String,
    email_verified: bool,
    name: Option<String>,
    iss: String,
    aud: String,
    exp: usize,
    iat: usize,
    firebase: WireFirebase,
}

#[derive(Serialize)]
struct WireFirebase {
    sign_in_provider: String,
}

struct Keypair {
    encoding: EncodingKey,
    decoding: DecodingKey,
}

fn gen_keypair() -> Keypair {
    let mut rng = rand::thread_rng();
    let priv_key = RsaPrivateKey::new(&mut rng, 2048).expect("rsa keygen");
    let priv_pem = priv_key
        .to_pkcs1_pem(LineEnding::LF)
        .expect("priv pem")
        .to_string();
    let pub_pem = priv_key
        .to_public_key()
        .to_public_key_pem(LineEnding::LF)
        .expect("pub pem");
    let encoding = EncodingKey::from_rsa_pem(priv_pem.as_bytes()).expect("decode priv");
    let decoding = DecodingKey::from_rsa_pem(pub_pem.as_bytes()).expect("decode pub");
    Keypair { encoding, decoding }
}

fn make_jwks(decoding: DecodingKey) -> JwksCache {
    let mut keys = HashMap::new();
    keys.insert(TEST_KID.to_owned(), decoding);
    JwksCache::for_test(keys)
}

fn now_secs() -> usize {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs() as usize
}

fn default_claims() -> WireClaims {
    let now = now_secs();
    WireClaims {
        sub: "fb-uid-1".into(),
        email: "alice@example.test".into(),
        email_verified: true,
        name: Some("Alice".into()),
        iss: format!("https://securetoken.google.com/{TEST_PROJECT_ID}"),
        aud: TEST_PROJECT_ID.into(),
        exp: now + 3600,
        iat: now - 10,
        firebase: WireFirebase {
            sign_in_provider: "password".into(),
        },
    }
}

fn header_with_kid(alg: Algorithm) -> Header {
    let mut h = Header::new(alg);
    h.kid = Some(TEST_KID.into());
    h
}

fn sign(claims: &WireClaims, encoding: &EncodingKey) -> String {
    encode(&header_with_kid(Algorithm::RS256), claims, encoding).unwrap()
}

#[tokio::test]
async fn accepts_valid_token() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let token = sign(&default_claims(), &kp.encoding);
    let claims = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap();
    assert_eq!(claims.uid, "fb-uid-1");
    assert_eq!(claims.email, "alice@example.test");
    assert!(claims.email_verified);
    assert_eq!(claims.sign_in_provider, "password");
    assert_eq!(claims.name.as_deref(), Some("Alice"));
}

#[tokio::test]
async fn rejects_expired_token() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let mut c = default_claims();
    c.exp = now_secs() - 60;
    c.iat = now_secs() - 3600;
    let token = sign(&c, &kp.encoding);
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::Expired));
}

#[tokio::test]
async fn rejects_wrong_audience() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let mut c = default_claims();
    c.aud = "another-project".into();
    let token = sign(&c, &kp.encoding);
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::WrongAudience));
}

#[tokio::test]
async fn rejects_wrong_issuer() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let mut c = default_claims();
    c.iss = "https://evil.example.com/test-project".into();
    let token = sign(&c, &kp.encoding);
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::WrongIssuer));
}

#[tokio::test]
async fn rejects_token_signed_with_wrong_key() {
    let kp_real = gen_keypair();
    let kp_attacker = gen_keypair();
    // JWKs cache holds the *real* public key.
    let jwks = make_jwks(kp_real.decoding);
    // Token signed with the *attacker's* private key.
    let token = sign(&default_claims(), &kp_attacker.encoding);
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::BadSignature));
}

#[tokio::test]
async fn rejects_malformed_token() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let err = verify_id_token("not.a.jwt", TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::MalformedToken(_)));
}

#[tokio::test]
async fn rejects_kid_not_in_jwks() {
    let kp_real = gen_keypair();
    let kp_other = gen_keypair();
    // JWKs cache only knows about the real key.
    let jwks = make_jwks(kp_real.decoding);
    // Token claims to be signed by an unknown kid.
    let mut header = Header::new(Algorithm::RS256);
    header.kid = Some("unknown-kid".into());
    let token = encode(&header, &default_claims(), &kp_other.encoding).unwrap();
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::BadSignature));
}

#[tokio::test]
async fn rejects_missing_kid_in_header() {
    let kp = gen_keypair();
    let jwks = make_jwks(kp.decoding);
    let header_no_kid = Header::new(Algorithm::RS256);
    let token = encode(&header_no_kid, &default_claims(), &kp.encoding).unwrap();
    let err = verify_id_token(&token, TEST_PROJECT_ID, &jwks).await.unwrap_err();
    assert!(matches!(err, VerifyError::MalformedToken(_)));
}
