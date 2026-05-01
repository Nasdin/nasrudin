//! Integration tests for `POST /api/research/jobs` with the new
//! `credits_budget` / `rush` fields and transactional decrement+insert.
//!
//! Auth setup mirrors `firebase_session.rs`: we mint a Firebase ID
//! token against an in-process JWKs and exchange it for a session
//! cookie, then issue the actual POST with that cookie. The whole
//! submit handler runs inside one PG transaction; the assertions
//! verify the row state, ledger state, and 4xx body shape.

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
use sea_orm::{ConnectionTrait, DatabaseBackend, Statement};
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

fn mint(uid: &str, email: &str, kp: &Kp) -> String {
    let claims = WireClaims {
        sub: uid.into(),
        email: email.into(),
        email_verified: true,
        name: Some("Test User".into()),
        iss: format!("https://securetoken.google.com/{TEST_PROJECT}"),
        aud: TEST_PROJECT.into(),
        exp: now() + 3600,
        iat: now() - 5,
        firebase: WireFirebase { sign_in_provider: "google.com".into() },
    };
    let mut h = Header::new(Algorithm::RS256);
    h.kid = Some(TEST_KID.into());
    encode(&h, &claims, &kp.enc).unwrap()
}

/// Sign in a fresh user via /api/auth/firebase-session and grant them
/// `credits` research credits. Returns (TestApp, session-cookie string).
async fn signed_in_with_credits(
    app: &test_app::TestApp,
    kp: &Kp,
    uid: &str,
    credits: i32,
) -> String {
    let token = mint(uid, &format!("{uid}@example.test"), kp);
    let resp = app
        .router
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/api/auth/firebase-session")
                .header(header::CONTENT_TYPE, "application/json")
                .body(Body::from(format!(r#"{{"id_token":"{token}"}}"#)))
                .unwrap(),
        )
        .await
        .unwrap();
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
    // Set the credit balance. The user was just inserted with 0
    // credits; any test that needs N > 0 calls this with credits=N.
    if credits != 0 {
        app.pg
            .execute_raw(Statement::from_sql_and_values(
                DatabaseBackend::Postgres,
                "UPDATE users SET research_credits = $2 WHERE firebase_uid = $1",
                [uid.into(), credits.into()],
            ))
            .await
            .unwrap();
    }
    cookie
}

async fn build_app() -> Option<(test_app::TestApp, Kp)> {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let app = test_app::build_with_jwks(TEST_PROJECT, jwks).await?;
    Some((app, kp))
}

async fn post_json(
    app: &test_app::TestApp,
    path: &str,
    cookie: &str,
    body: &serde_json::Value,
) -> (StatusCode, serde_json::Value) {
    let resp = app
        .router
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(path)
                .header(header::CONTENT_TYPE, "application/json")
                .header(header::COOKIE, cookie)
                .body(Body::from(serde_json::to_vec(body).unwrap()))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = resp.status();
    let body = to_bytes(resp.into_body(), 1 << 16).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body).unwrap_or(serde_json::Value::Null);
    (status, v)
}

async fn read_credits(app: &test_app::TestApp, uid: &str) -> i32 {
    let row = app
        .pg
        .query_one_raw(Statement::from_sql_and_values(
            DatabaseBackend::Postgres,
            "SELECT research_credits FROM users WHERE firebase_uid = $1",
            [uid.into()],
        ))
        .await
        .unwrap()
        .unwrap();
    row.try_get_by_index::<i32>(0).unwrap()
}

async fn read_job(app: &test_app::TestApp, job_id: &str) -> (i32, i32) {
    // Returns (lake_slot_hours_quota, slice_priority).
    let job_uuid: uuid::Uuid = job_id.parse().unwrap();
    let row = app
        .pg
        .query_one_raw(Statement::from_sql_and_values(
            DatabaseBackend::Postgres,
            "SELECT lake_slot_hours_quota, slice_priority FROM conjecture_jobs WHERE id = $1",
            [job_uuid.into()],
        ))
        .await
        .unwrap()
        .unwrap();
    (
        row.try_get_by_index::<i32>(0).unwrap(),
        row.try_get_by_index::<i32>(1).unwrap(),
    )
}

#[tokio::test]
async fn submit_defaults_to_one_credit_and_priority_5() {
    let Some((app, kp)) = build_app().await else { return };
    let cookie = signed_in_with_credits(&app, &kp, "fb-default", 3).await;

    let (status, body) = post_json(
        &app,
        "/api/research/jobs",
        &cookie,
        &serde_json::json!({ "hunch": "E = m c^2" }),
    )
    .await;
    assert_eq!(status, StatusCode::CREATED, "body: {body}");

    let job_id = body["job_id"].as_str().unwrap().to_string();
    let (quota, priority) = read_job(&app, &job_id).await;
    assert_eq!(quota, 96, "default budget = 1 credit = 96 slot-h");
    assert_eq!(priority, 5);
    assert_eq!(read_credits(&app, "fb-default").await, 2);
}

#[tokio::test]
async fn submit_with_credits_budget_3_sets_quota_288() {
    let Some((app, kp)) = build_app().await else { return };
    let cookie = signed_in_with_credits(&app, &kp, "fb-budget3", 5).await;

    let (status, body) = post_json(
        &app,
        "/api/research/jobs",
        &cookie,
        &serde_json::json!({
            "hunch": "test conjecture",
            "credits_budget": 3,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::CREATED, "body: {body}");
    let job_id = body["job_id"].as_str().unwrap().to_string();
    let (quota, priority) = read_job(&app, &job_id).await;
    assert_eq!(
        quota, 288,
        "credits_budget=3 must produce quota 288, got {quota}"
    );
    assert_ne!(quota, 96, "must not fall back to default 96 quota");
    assert_eq!(priority, 5);
    assert_eq!(read_credits(&app, "fb-budget3").await, 2);
}

#[tokio::test]
async fn submit_with_rush_charges_extra_credit_and_priority_6() {
    let Some((app, kp)) = build_app().await else { return };
    let cookie = signed_in_with_credits(&app, &kp, "fb-rush", 5).await;

    let (status, body) = post_json(
        &app,
        "/api/research/jobs",
        &cookie,
        &serde_json::json!({
            "hunch": "test",
            "credits_budget": 2,
            "rush": true,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::CREATED, "body: {body}");
    let job_id = body["job_id"].as_str().unwrap().to_string();
    let (quota, priority) = read_job(&app, &job_id).await;
    assert_eq!(quota, 192);
    assert_eq!(priority, 6, "rush bumps slice_priority by 1");
    assert_eq!(
        read_credits(&app, "fb-rush").await,
        2,
        "5 - (2 budget + 1 rush) = 2"
    );
}

#[tokio::test]
async fn submit_with_zero_credits_budget_returns_400_and_does_not_decrement() {
    let Some((app, kp)) = build_app().await else { return };
    let cookie = signed_in_with_credits(&app, &kp, "fb-zero-budget", 5).await;

    let (status, body) = post_json(
        &app,
        "/api/research/jobs",
        &cookie,
        &serde_json::json!({
            "hunch": "test",
            "credits_budget": 0,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "body: {body}");
    assert_eq!(body["error"], "invalid_credits_budget");
    assert_eq!(read_credits(&app, "fb-zero-budget").await, 5);
}

#[tokio::test]
async fn submit_402_when_insufficient_credits_with_required_remaining_body() {
    let Some((app, kp)) = build_app().await else { return };
    let cookie = signed_in_with_credits(&app, &kp, "fb-poor", 2).await;

    let (status, body) = post_json(
        &app,
        "/api/research/jobs",
        &cookie,
        &serde_json::json!({
            "hunch": "test",
            "credits_budget": 5,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::PAYMENT_REQUIRED, "body: {body}");
    assert_eq!(body["error"], "insufficient_research_credits");
    assert_eq!(body["required"], 5);
    assert_eq!(body["remaining"], 2);
    assert_eq!(read_credits(&app, "fb-poor").await, 2, "ledger untouched");
}

#[tokio::test]
async fn submit_402_when_rush_pushes_total_over_remaining() {
    let Some((app, kp)) = build_app().await else { return };
    let cookie = signed_in_with_credits(&app, &kp, "fb-rush-poor", 1).await;

    // 1 budget + 1 rush = 2 needed, only 1 remaining.
    let (status, body) = post_json(
        &app,
        "/api/research/jobs",
        &cookie,
        &serde_json::json!({
            "hunch": "test",
            "credits_budget": 1,
            "rush": true,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::PAYMENT_REQUIRED, "body: {body}");
    assert_eq!(body["required"], 2);
    assert_eq!(body["remaining"], 1);
}

#[tokio::test]
async fn submit_with_empty_hunch_returns_400_does_not_decrement() {
    let Some((app, kp)) = build_app().await else { return };
    let cookie = signed_in_with_credits(&app, &kp, "fb-empty-hunch", 5).await;

    let (status, _) = post_json(
        &app,
        "/api/research/jobs",
        &cookie,
        &serde_json::json!({
            "hunch": "   ",
            "credits_budget": 3,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
    assert_eq!(read_credits(&app, "fb-empty-hunch").await, 5);
}
