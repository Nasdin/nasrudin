//! Integration tests for `POST /api/research/jobs/{id}/cancel`.
//!
//! Mirrors `research_jobs_submit.rs` for auth setup. Behavioural
//! coverage of the underlying SQL transaction lives in
//! `nasrudin-pg/tests/paid_researcher_queries.rs`; these tests
//! exercise the HTTP-level wiring: response shape, refund integer,
//! 409 idempotency, and that the credits ledger reflects the refund.

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
    let pub_pem = pk
        .to_public_key()
        .to_public_key_pem(LineEnding::LF)
        .unwrap();
    Kp {
        enc: EncodingKey::from_rsa_pem(priv_pem.as_bytes()).unwrap(),
        dec: DecodingKey::from_rsa_pem(pub_pem.as_bytes()).unwrap(),
    }
}

fn now() -> usize {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs() as usize
}

fn mint(uid: &str, kp: &Kp) -> String {
    let claims = WireClaims {
        sub: uid.into(),
        email: format!("{uid}@example.test"),
        email_verified: true,
        name: Some("Test User".into()),
        iss: format!("https://securetoken.google.com/{TEST_PROJECT}"),
        aud: TEST_PROJECT.into(),
        exp: now() + 3600,
        iat: now() - 5,
        firebase: WireFirebase {
            sign_in_provider: "google.com".into(),
        },
    };
    let mut h = Header::new(Algorithm::RS256);
    h.kid = Some(TEST_KID.into());
    encode(&h, &claims, &kp.enc).unwrap()
}

async fn build_app() -> Option<(test_app::TestApp, Kp)> {
    let kp = gen_kp();
    let mut jwks = HashMap::new();
    jwks.insert(TEST_KID.into(), kp.dec.clone());
    let app = test_app::build_with_jwks(TEST_PROJECT, jwks).await?;
    Some((app, kp))
}

async fn signed_in_with_credits(
    app: &test_app::TestApp,
    kp: &Kp,
    uid: &str,
    credits: i32,
) -> String {
    let token = mint(uid, kp);
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

/// Submit a new paid job and return the job_id.
async fn submit_job(
    app: &test_app::TestApp,
    cookie: &str,
    credits_budget: i32,
    rush: bool,
) -> String {
    let (status, body) = post_json(
        app,
        "/api/research/jobs",
        cookie,
        &serde_json::json!({
            "hunch": "test conjecture",
            "credits_budget": credits_budget,
            "rush": rush,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::CREATED, "submit failed: {body}");
    body["job_id"].as_str().unwrap().to_string()
}

/// Force the row's `lake_slot_hours_consumed` to `consumed` so the
/// proportional refund formula has something to bite.
async fn force_consumed(app: &test_app::TestApp, job_id: &str, consumed: f32) {
    let job_uuid: uuid::Uuid = job_id.parse().unwrap();
    app.pg
        .execute_raw(Statement::from_sql_and_values(
            DatabaseBackend::Postgres,
            "UPDATE conjecture_jobs SET lake_slot_hours_consumed = $2 WHERE id = $1",
            [job_uuid.into(), (consumed as f64).into()],
        ))
        .await
        .unwrap();
}

async fn force_verified(app: &test_app::TestApp, job_id: &str, verified: i32) {
    let job_uuid: uuid::Uuid = job_id.parse().unwrap();
    app.pg
        .execute_raw(Statement::from_sql_and_values(
            DatabaseBackend::Postgres,
            "UPDATE conjecture_jobs SET candidates_verified = $2 WHERE id = $1",
            [job_uuid.into(), verified.into()],
        ))
        .await
        .unwrap();
}

#[tokio::test]
async fn cancel_zero_consumed_full_refund() {
    let Some((app, kp)) = build_app().await else {
        return;
    };
    let cookie = signed_in_with_credits(&app, &kp, "fb-cancel-full", 5).await;
    let job = submit_job(&app, &cookie, 5, false).await;
    // After submit: user has 0 credits, job has quota=480, consumed=0.

    let (status, body) = post_json(
        &app,
        &format!("/api/research/jobs/{job}/cancel"),
        &cookie,
        &serde_json::json!({}),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "body: {body}");
    assert_eq!(body["cancelled"], true);
    assert_eq!(
        body["refunded_credits"], 5,
        "0 consumed of 480 quota = full 5-credit refund"
    );
    assert_eq!(read_credits(&app, "fb-cancel-full").await, 5);
}

#[tokio::test]
async fn cancel_partial_consumed_proportional_refund() {
    let Some((app, kp)) = build_app().await else {
        return;
    };
    let cookie = signed_in_with_credits(&app, &kp, "fb-cancel-partial", 5).await;
    let job = submit_job(&app, &cookie, 5, false).await;
    // 5 credits → quota 480. Force 192 consumed (40%).
    force_consumed(&app, &job, 192.0).await;

    let (status, body) = post_json(
        &app,
        &format!("/api/research/jobs/{job}/cancel"),
        &cookie,
        &serde_json::json!({}),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "body: {body}");
    assert_eq!(
        body["refunded_credits"], 3,
        "floor(5 × (1 - 192/480)) = floor(3.0) = 3"
    );
    assert_eq!(read_credits(&app, "fb-cancel-partial").await, 3);
}

#[tokio::test]
async fn cancel_with_verified_no_refund() {
    let Some((app, kp)) = build_app().await else {
        return;
    };
    let cookie = signed_in_with_credits(&app, &kp, "fb-cancel-verified", 5).await;
    let job = submit_job(&app, &cookie, 5, false).await;
    force_verified(&app, &job, 1).await;

    let (status, body) = post_json(
        &app,
        &format!("/api/research/jobs/{job}/cancel"),
        &cookie,
        &serde_json::json!({}),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "body: {body}");
    assert_eq!(
        body["refunded_credits"], 0,
        "any verified theorem disables refund regardless of consumed"
    );
    assert_eq!(read_credits(&app, "fb-cancel-verified").await, 0);
}

#[tokio::test]
async fn cancel_already_terminal_returns_409() {
    let Some((app, kp)) = build_app().await else {
        return;
    };
    let cookie = signed_in_with_credits(&app, &kp, "fb-cancel-409", 5).await;
    let job = submit_job(&app, &cookie, 1, false).await;

    let (status_a, _) = post_json(
        &app,
        &format!("/api/research/jobs/{job}/cancel"),
        &cookie,
        &serde_json::json!({}),
    )
    .await;
    assert_eq!(status_a, StatusCode::OK);

    let (status_b, body) = post_json(
        &app,
        &format!("/api/research/jobs/{job}/cancel"),
        &cookie,
        &serde_json::json!({}),
    )
    .await;
    assert_eq!(status_b, StatusCode::CONFLICT, "body: {body}");
    assert_eq!(body["error"], "terminal_state");
}

#[tokio::test]
async fn cancel_double_call_refunds_exactly_once() {
    // Idempotency at HTTP level: even if two concurrent requests
    // arrive, only one transitions the row and only one refunds.
    let Some((app, kp)) = build_app().await else {
        return;
    };
    let cookie = signed_in_with_credits(&app, &kp, "fb-cancel-double", 5).await;
    let job = submit_job(&app, &cookie, 3, false).await;
    // user should now have 2 credits.
    assert_eq!(read_credits(&app, "fb-cancel-double").await, 2);

    let path = format!("/api/research/jobs/{job}/cancel");
    let empty = serde_json::json!({});
    let (a, b) = tokio::join!(
        post_json(&app, &path, &cookie, &empty),
        post_json(&app, &path, &cookie, &empty),
    );
    let oks = [&a, &b].iter().filter(|r| r.0 == StatusCode::OK).count();
    let conflicts = [&a, &b]
        .iter()
        .filter(|r| r.0 == StatusCode::CONFLICT)
        .count();
    assert_eq!(oks, 1, "exactly one OK across the two parallel cancels");
    assert_eq!(conflicts, 1, "the loser sees 409");

    // 5 - 3 (debit at submit) + 3 (refund) = 5 again.
    assert_eq!(read_credits(&app, "fb-cancel-double").await, 5);
}
