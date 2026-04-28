//! Integration tests for the `/api/events/discoveries` and
//! `/api/events/stats` SSE streams (Phase 9 / Task 5.2).
//!
//! These tests verify the *response shape* — status code + content-type —
//! through the in-memory `tower::oneshot` plumbing. Reading event bytes off
//! the response body works in principle, but `tower::ServiceExt::oneshot`
//! resolves once the response head is written; reading the streaming body
//! while concurrently sending events through `state.reverify_event_tx`
//! requires a different harness shape (spawning a real listener and a
//! reqwest client). End-to-end SSE round-trip lives in the Phase 10 smoke
//! tests; this file's value is asserting that the route is wired up and the
//! handler hands back the right `text/event-stream` content-type.

mod test_app;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::util::ServiceExt;

#[tokio::test]
async fn discoveries_stream_returns_event_stream_content_type() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unreachable");
        return;
    };

    let req = Request::builder()
        .method("GET")
        .uri("/api/events/discoveries")
        .header("accept", "text/event-stream")
        .body(Body::empty())
        .unwrap();

    let resp = app.router.clone().oneshot(req).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);

    let ct = resp
        .headers()
        .get("content-type")
        .expect("content-type header required for SSE")
        .to_str()
        .unwrap();
    assert!(
        ct.starts_with("text/event-stream"),
        "expected text/event-stream content-type, got {ct}"
    );
}

#[tokio::test]
async fn stats_stream_returns_event_stream_content_type() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unreachable");
        return;
    };

    let req = Request::builder()
        .method("GET")
        .uri("/api/events/stats")
        .header("accept", "text/event-stream")
        .body(Body::empty())
        .unwrap();

    let resp = app.router.clone().oneshot(req).await.unwrap();
    assert_eq!(resp.status(), StatusCode::OK);

    let ct = resp
        .headers()
        .get("content-type")
        .expect("content-type header required for SSE")
        .to_str()
        .unwrap();
    assert!(
        ct.starts_with("text/event-stream"),
        "expected text/event-stream content-type, got {ct}"
    );
}

/// Sanity check that the broadcast channel exposed via the test harness
/// actually accepts the three reverify event variants. This is a unit-style
/// assertion (no HTTP) — it's the closest we get to round-trip coverage at
/// the in-memory test layer; full streaming round-trip is deferred to the
/// Phase 10 smoke tests against a real listener.
#[tokio::test]
async fn reverify_event_tx_accepts_all_three_variants() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unreachable");
        return;
    };

    use physics_api::reverify::DiscoveryEvent;

    // Subscribe BEFORE sending so the broadcast channel buffers the events.
    let mut rx = app.reverify_event_tx.subscribe();

    app.reverify_event_tx
        .send(DiscoveryEvent::TheoremPending {
            theorem_id: "deadbeefdeadbeef".into(),
            canonical: "True".into(),
            contributor_id: "w1".into(),
        })
        .unwrap();
    app.reverify_event_tx
        .send(DiscoveryEvent::TheoremVerified {
            theorem_id: "deadbeefdeadbeef".into(),
            verification_path: "B".into(),
            duration_ms: 42,
        })
        .unwrap();
    app.reverify_event_tx
        .send(DiscoveryEvent::TheoremRejected {
            theorem_id: "deadbeefdeadbeef".into(),
            reason: "lake_build_failed".into(),
        })
        .unwrap();

    let pending = rx.recv().await.unwrap();
    let verified = rx.recv().await.unwrap();
    let rejected = rx.recv().await.unwrap();
    assert!(matches!(pending, DiscoveryEvent::TheoremPending { .. }));
    assert!(matches!(verified, DiscoveryEvent::TheoremVerified { .. }));
    assert!(matches!(rejected, DiscoveryEvent::TheoremRejected { .. }));
}
