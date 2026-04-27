//! End-to-end test that AuthOrApiKey resolves both a cookie session
//! and a Bearer api-key to the same `AuthUser`.

#[tokio::test]
async fn placeholder_until_extractor_lands() {
    // We need a running test server harness to exercise this end-to-end.
    // For Phase 2 we only assert the type exists and is `Send + Sync`.
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<physics_api::auth::AuthOrApiKey>();
}
