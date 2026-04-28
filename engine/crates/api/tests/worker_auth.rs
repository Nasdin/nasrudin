//! Phase 9 / Task 4.3 — `WorkerAuth` extractor focused unit tests.
//!
//! These tests assert the two pre-database rejection branches of the
//! extractor:
//!
//! 1. Missing `Authorization: Bearer …` header → `401 Unauthorized`.
//! 2. Bearer present but with a non-`nsk_worker_` prefix (e.g. a user/live
//!    api-key) → `403 Forbidden`.
//!
//! Both cases reject before any PostgreSQL lookup runs, so the tests do not
//! depend on a live database. The "happy path" + Argon2-verify branch is
//! exercised end-to-end by the ingest integration tests in
//! `tests/reverify_a_path.rs` (which require a live DB).

use axum::extract::FromRequestParts;
use axum::http::{HeaderValue, Request, StatusCode};
use physics_api::auth::WorkerAuth;

/// Build a `Parts` value with the supplied `Authorization` header (or none).
fn parts_with_auth(authorization: Option<&str>) -> axum::http::request::Parts {
    let mut builder = Request::builder().method("POST").uri("/api/ingest");
    if let Some(v) = authorization {
        builder = builder.header(axum::http::header::AUTHORIZATION, v);
    }
    let req = builder.body(()).unwrap();
    let (parts, _body) = req.into_parts();
    parts
}

#[tokio::test]
async fn missing_bearer_returns_401() {
    let mut parts = parts_with_auth(None);
    let result = WorkerAuth::from_request_parts(&mut parts, &()).await;
    let err = result.err().expect("missing bearer must reject");
    assert_eq!(err.0, StatusCode::UNAUTHORIZED);
    let body = err.1.0.to_string();
    assert!(
        body.contains("not authenticated"),
        "expected 'not authenticated' body, got {body}"
    );
}

#[tokio::test]
async fn non_worker_prefix_returns_403() {
    // `nsk_live_*` is a valid user/live api-key — but the ingest endpoint
    // requires a *worker* key, so the extractor must hard-fail with 403.
    let header = HeaderValue::from_static("Bearer nsk_live_abcdefghijklmnop");
    let mut parts = parts_with_auth(Some(header.to_str().unwrap()));
    let result = WorkerAuth::from_request_parts(&mut parts, &()).await;
    let err = result.err().expect("non-worker prefix must reject");
    assert_eq!(err.0, StatusCode::FORBIDDEN);
    let body = err.1.0.to_string();
    assert!(
        body.contains("non_worker_key"),
        "expected 'non_worker_key' body, got {body}"
    );
}
