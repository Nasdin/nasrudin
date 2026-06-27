//! Integration test for `GET /api/discoveries/novel` (M3).
//!
//! Verifies that the handler:
//!   * excludes rows with `verification_tactic = 'imported'`
//!   * excludes rows with `generation = 0` (or NULL)
//!   * excludes rows whose `canonical_hash` is in the boot-loaded
//!     catalog hash set
//!   * surfaces non-imported, gen > 0, off-catalog rows
//!
//! Skips gracefully when the test PostgreSQL isn't reachable.

mod test_app;

use axum::http::StatusCode;
use sea_orm::{ActiveModelTrait, Set};
use std::sync::Arc;

use nasrudin_pg::entity::theorems;
use nasrudin_pg::query::theorems as theorem_q;

/// Helper: insert a Verified theorem with full GA metadata. Uses the
/// pg entity ActiveModel directly so we can set both `generation` and
/// `verification_tactic` in one round-trip (the harness's
/// `seed_verified_theorems` always leaves generation NULL and tactic
/// = 'A' which isn't what M3 needs).
async fn seed_ga(
    app: &test_app::TestApp,
    canonical: &str,
    domain: &str,
    generation: i64,
    tactic: Option<&str>,
) -> Vec<u8> {
    let id = nasrudin_core::canonical_hash(canonical);

    let row = theorem_q::NewTheorem {
        id: id.clone(),
        canonical_hash: id.clone(),
        canonical_statement: canonical.into(),
        domain: domain.into(),
        lean_source: format!("theorem t : True := trivial -- {canonical}"),
        chain_json: serde_json::json!([]),
        engine_git_sha: "test".into(),
        lean_version: "4.27.0".into(),
        contributor_id: "test".into(),
        generation: Some(generation),
        axioms_used: vec!["axiom_a".into(), "axiom_b".into()],
        ..Default::default()
    };
    theorem_q::insert_pending(&app.pg, row).await.unwrap();

    // Flip to Verified with the requested tactic. mark_verified
    // requires a non-empty tactic string; for the "null tactic" case
    // (in-process GA chain) we manually patch the column back to NULL
    // afterwards via an ActiveModel update.
    let effective_tactic = tactic.unwrap_or("A");
    theorem_q::mark_verified(&app.pg, &id, "test_path", effective_tactic, 1)
        .await
        .unwrap();
    if tactic.is_none() {
        let am = theorems::ActiveModel {
            id: Set(id.clone()),
            verification_tactic: Set(None),
            ..Default::default()
        };
        am.update(&app.pg).await.unwrap();
    }
    id
}

#[tokio::test]
async fn novel_excludes_imports_and_catalog_hits() {
    let Some(mut app) = test_app::build().await else {
        return;
    };

    // Seed:
    //   1. an 'imported' theorem (must be excluded)
    //   2. a gen=0 GA-like row (must be excluded)
    //   3. a gen=5 GA row whose canonical_hash IS in the catalog set
    //      (must be excluded as a rediscovery)
    //   4. a gen=5 GA row whose canonical_hash is NOT in the catalog
    //      set (must be surfaced as a novel discovery)
    seed_ga(
        &app,
        "imported_catalog_thm",
        "Special relativity",
        0,
        Some("imported"),
    )
    .await;
    seed_ga(&app, "seed_axiom", "Special relativity", 0, None).await;
    let rediscovery_id = seed_ga(&app, "rediscovered_emc2", "Special relativity", 5, None).await;
    let novel_id = seed_ga(&app, "brand_new_lemma", "Special relativity", 5, None).await;

    // Catalog set defaults to empty in the harness. Mount a fresh
    // router on a state that differs only in `catalog_hashes` so
    // the rejection branch actually fires.
    let state_for_handler = override_catalog_set(&app, vec![rediscovery_id.clone()]);
    let route = axum::Router::new()
        .route(
            "/api/discoveries/novel",
            axum::routing::get(physics_api::handlers::discoveries::novel),
        )
        .with_state(state_for_handler);
    app.router = route;

    let resp = test_app::get(&app, "/api/discoveries/novel?limit=50").await;
    assert_eq!(
        resp.status,
        StatusCode::OK,
        "body: {:?}",
        String::from_utf8_lossy(&resp.body)
    );

    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    let discoveries = body["discoveries"].as_array().expect("discoveries array");

    // Catalog set should report exactly one entry — the rediscovery
    // hash we injected.
    assert_eq!(
        body["catalog_hashes_loaded"].as_u64().unwrap(),
        1,
        "catalog_hashes_loaded reflects the injected set size"
    );

    let returned_ids: Vec<String> = discoveries
        .iter()
        .map(|d| d["id"].as_str().unwrap().to_string())
        .collect();

    let novel_hex = hex::encode(&novel_id);
    let rediscovery_hex = hex::encode(&rediscovery_id);
    let imported_hex = hex::encode(nasrudin_core::canonical_hash("imported_catalog_thm"));
    let seed_hex = hex::encode(nasrudin_core::canonical_hash("seed_axiom"));

    assert!(
        returned_ids.contains(&novel_hex),
        "novel row must be surfaced; got ids = {returned_ids:?}"
    );
    assert!(
        !returned_ids.contains(&rediscovery_hex),
        "rediscovery hash is in catalog set ⇒ must be filtered out"
    );
    assert!(
        !returned_ids.contains(&imported_hex),
        "imported tactic ⇒ must be filtered out"
    );
    assert!(
        !returned_ids.contains(&seed_hex),
        "generation=0 ⇒ must be filtered out"
    );

    // Spot-check the row shape on the surviving novel row.
    let novel_row = discoveries
        .iter()
        .find(|d| d["id"].as_str().unwrap() == novel_hex)
        .expect("novel row present");
    assert_eq!(novel_row["canonical_statement"], "brand_new_lemma");
    assert_eq!(novel_row["domain"], "Special relativity");
    assert_eq!(novel_row["generation"].as_i64().unwrap(), 5);
    assert!(
        novel_row["verification_tactic"].is_null(),
        "in-process GA row carries NULL tactic"
    );
}

#[tokio::test]
async fn novel_empty_catalog_treats_everything_as_novel() {
    let Some(app) = test_app::build().await else {
        return;
    };

    // Empty catalog (the test harness default). A single non-imported
    // GA row should land in the response unconditionally.
    let id = seed_ga(&app, "free_pass_lemma", "Special relativity", 3, None).await;

    let resp = test_app::get(&app, "/api/discoveries/novel?limit=10").await;
    assert_eq!(resp.status, StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert_eq!(
        body["catalog_hashes_loaded"].as_u64().unwrap(),
        0,
        "empty catalog at boot ⇒ catalog_hashes_loaded = 0"
    );

    let ids: Vec<String> = body["discoveries"]
        .as_array()
        .unwrap()
        .iter()
        .map(|d| d["id"].as_str().unwrap().to_string())
        .collect();
    assert!(
        ids.contains(&hex::encode(&id)),
        "with empty catalog every non-imported GA row passes through"
    );
}

/// Re-build the test app's state with a custom catalog hash set.
/// Returns an `Arc<AppState>` ready to be plugged into a fresh router
/// via `.with_state()`. Mirrors `test_app::build()` field-for-field;
/// only `catalog_hashes` differs.
fn override_catalog_set(
    app: &test_app::TestApp,
    hashes: Vec<Vec<u8>>,
) -> Arc<physics_api::state::AppState> {
    use physics_api::state::AppState;
    // Pull every shared resource off the existing state so the
    // overridden state is observationally identical except for the
    // catalog hash set.
    let s = &app.state;
    Arc::new(AppState {
        db: Arc::clone(&s.db),
        pg: s.pg.clone(),
        axiom_store: s.axiom_store.clone(),
        discovery_tx: s.discovery_tx.clone(),
        ga_status: Arc::clone(&s.ga_status),
        lake: Arc::clone(&s.lake),
        reverify_event_tx: s.reverify_event_tx.clone(),
        reverify: s.reverify.clone(),
        worker_rate_limiter: Arc::clone(&s.worker_rate_limiter),
        admin_token: s.admin_token.clone(),
        cache_ctx: s.cache_ctx.clone(),
        embed: s.embed.clone(),
        embedder: s.embedder.clone(),
        embed_path: s.embed_path.clone(),
        llm_encrypt_key: s.llm_encrypt_key,
        conjecture_event_tx: s.conjecture_event_tx.clone(),
        lake_promotion: s.lake_promotion.clone(),
        billing: s.billing.clone(),
        seed_cache: Arc::clone(&s.seed_cache),
        steering: Arc::clone(&s.steering),
        cluster_config: Arc::clone(&s.cluster_config),
        directive_arms: Arc::clone(&s.directive_arms),
        compute_arms: Arc::clone(&s.compute_arms),
        capacity: Arc::clone(&s.capacity),
        job_events: Arc::clone(&s.job_events),
        landing_stats: Arc::clone(&s.landing_stats),
        workers_list_cache: Arc::clone(&s.workers_list_cache),
        contributors_list_cache: Arc::clone(&s.contributors_list_cache),
        theorems_recent_cache: Arc::clone(&s.theorems_recent_cache),
        firebase_project_id: s.firebase_project_id.clone(),
        firebase_jwks: Arc::clone(&s.firebase_jwks),
        stripe_http: s.stripe_http.clone(),
        stripe_base_url: s.stripe_base_url.clone(),
        stripe_secret: s.stripe_secret.clone(),
        impersonation_signing_key: s.impersonation_signing_key.clone(),
        bulk_run_progress_tx: s.bulk_run_progress_tx.clone(),
        trust_cache: s.trust_cache.clone(),
        trust_invalidation_tx: s.trust_invalidation_tx.clone(),
        trusted_spot_check_rate: s.trusted_spot_check_rate,
        catalog_hashes: physics_api::state::CatalogHashSet::from_vec(hashes),
        naming_client: s.naming_client.clone(),
        naming_semaphore: Arc::clone(&s.naming_semaphore),
    })
}
