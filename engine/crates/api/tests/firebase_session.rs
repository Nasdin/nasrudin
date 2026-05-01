//! End-to-end test: POST /api/auth/firebase-session creates a user, issues
//! a session cookie, and subsequent /api/auth/me returns the user.

mod test_app;

use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use axum::body::{Body, to_bytes};
use axum::http::{Request, StatusCode, header};
use jsonwebtoken::{Algorithm, DecodingKey, EncodingKey, Header, encode};
use rsa::{
    RsaPrivateKey,
    pkcs1::EncodeRsaPrivateKey,
    pkcs8::{EncodePublicKey, LineEnding},
};
use serde::Serialize;
use tower::util::ServiceExt;

const TEST_PROJECT: &str = "test-project";
const TEST_KID: &str = "kid-test-1";

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

struct Kp {
    enc: EncodingKey,
    dec: DecodingKey,
}

fn gen_kp() -> Kp {
    let mut rng = rand_08::thread_rng();
    let pk = RsaPrivateKey::new(&mut rng, 2048).expect("rsa keygen");
    let priv_pem = pk.to_pkcs1_pem(LineEnding::LF).unwrap().to_string();
    let pub_pem = pk.to_public_key().to_public_key_pem(LineEnding::LF).unwrap();
    Kp {
        enc: EncodingKey::from_rsa_pem(priv_pem.as_bytes()).unwrap(),
        dec: DecodingKey::from_rsa_pem(pub_pem.as_bytes()).unwrap(),
    }
}

fn now() -> usize {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs() as usize
}

fn mint(uid: &str, email: &str, provider: &str, verified: bool, kp: &Kp) -> String {
    let claims = WireClaims {
        sub: uid.into(),
        email: email.into(),
        email_verified: verified,
        name: Some("Test User".into()),
        iss: format!("https://securetoken.google.com/{TEST_PROJECT}"),
        aud: TEST_PROJECT.into(),
        exp: now() + 3600,
        iat: now() - 5,
        firebase: WireFirebase { sign_in_provider: provider.into() },
    };
    let mut h = Header::new(Algorithm::RS256);
    h.kid = Some(TEST_KID.into());
    encode(&h, &claims, &kp.enc).unwrap()
}

#[tokio::test]
async fn google_user_creates_row_and_session() {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let Some(app) = test_app::build_with_jwks(TEST_PROJECT, jwks).await else { return };

    let token = mint("fb-uid-google-1", "google.user@example.test", "google.com", true, &kp);

    let req = Request::builder()
        .method("POST")
        .uri("/api/auth/firebase-session")
        .header(header::CONTENT_TYPE, "application/json")
        .body(Body::from(format!(r#"{{"id_token":"{token}"}}"#)))
        .unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);

    let cookie = resp
        .headers()
        .get(header::SET_COOKIE)
        .expect("set-cookie present")
        .to_str()
        .unwrap()
        .split(';')
        .next()
        .unwrap()
        .to_owned();

    let body = to_bytes(resp.into_body(), 1 << 16).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(v["email"], "google.user@example.test");
    assert_eq!(v["firebase_uid"], "fb-uid-google-1");

    let me = Request::builder()
        .uri("/api/auth/me")
        .header(header::COOKIE, &cookie)
        .body(Body::empty())
        .unwrap();
    let me_resp = app.router.clone().oneshot(me).await.unwrap();
    assert_eq!(me_resp.status(), StatusCode::OK);
    let body = to_bytes(me_resp.into_body(), 1 << 16).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(v["firebase_uid"], "fb-uid-google-1");
    // The effort-slider UI on /research bounds the slider's max by
    // research_credits — surface it on /api/auth/me so the frontend
    // can read the wallet without a separate round-trip.
    assert!(
        v.get("research_credits").is_some()
            && !v["research_credits"].is_null(),
        "research_credits must be present on /api/auth/me; body: {v}"
    );
    assert_eq!(
        v["research_credits"].as_i64(),
        Some(0),
        "new users default to 0 research credits"
    );
}

#[tokio::test]
async fn returning_user_reuses_existing_row() {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let Some(app) = test_app::build_with_jwks(TEST_PROJECT, jwks).await else { return };

    let token = mint("fb-uid-returning", "ret@example.test", "google.com", true, &kp);
    let r1 = app.router.clone().oneshot(
        Request::builder()
            .method("POST")
            .uri("/api/auth/firebase-session")
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from(format!(r#"{{"id_token":"{token}"}}"#)))
            .unwrap(),
    ).await.unwrap();
    assert_eq!(r1.status(), StatusCode::OK);
    let v1: serde_json::Value = serde_json::from_slice(&to_bytes(r1.into_body(), 1<<16).await.unwrap()).unwrap();

    let r2 = app.router.clone().oneshot(
        Request::builder()
            .method("POST")
            .uri("/api/auth/firebase-session")
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from(format!(r#"{{"id_token":"{token}"}}"#)))
            .unwrap(),
    ).await.unwrap();
    assert_eq!(r2.status(), StatusCode::OK);
    let v2: serde_json::Value = serde_json::from_slice(&to_bytes(r2.into_body(), 1<<16).await.unwrap()).unwrap();

    assert_eq!(v1["id"], v2["id"], "same users.id reused on second call");
}

#[tokio::test]
async fn rejects_unverified_password_user() {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let Some(app) = test_app::build_with_jwks(TEST_PROJECT, jwks).await else { return };

    let token = mint("fb-uid-unverified", "noverify@example.test", "password", false, &kp);
    let resp = app.router.clone().oneshot(
        Request::builder()
            .method("POST")
            .uri("/api/auth/firebase-session")
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from(format!(r#"{{"id_token":"{token}"}}"#)))
            .unwrap(),
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::FORBIDDEN);
    let v: serde_json::Value = serde_json::from_slice(&to_bytes(resp.into_body(), 1<<16).await.unwrap()).unwrap();
    assert_eq!(v["error"], "email_not_verified");
}

#[tokio::test]
async fn rejects_invalid_token() {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let Some(app) = test_app::build_with_jwks(TEST_PROJECT, jwks).await else { return };

    let resp = app.router.clone().oneshot(
        Request::builder()
            .method("POST")
            .uri("/api/auth/firebase-session")
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from(r#"{"id_token":"not.a.real.jwt"}"#))
            .unwrap(),
    ).await.unwrap();
    assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
}
