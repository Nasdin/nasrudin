//! End-to-end LLM cluster steering test.
//!
//! Proves the full loop: a canned LLM response → cycle persists → state
//! Arc swaps → /api/seed includes new steering + cluster_config →
//! apply_steering_knobs reads mutation_priors → operator selection
//! distribution actually shifts. This is the load-bearing integration
//! test for the cluster steering work; if it passes, the LLM's
//! emissions reach mutation operator weights as designed.

mod test_app;

use async_trait::async_trait;
use rand::SeedableRng;
use rand::rngs::StdRng;
use serde_json::json;

use nasrudin_ga::chain_engine::DiscoveryConfig;
use nasrudin_ga::steering_knobs::apply_steering_knobs;
use physics_api::steerer::cycle::{CycleError, LlmCaller, run_one_cycle};

struct FakeLlmCaller {
    canned: String,
}

#[async_trait]
impl LlmCaller for FakeLlmCaller {
    async fn call(
        &self,
        _system: &str,
        _user: &str,
        _max_total_tokens: u32,
    ) -> Result<(String, Option<i32>, Option<i32>), CycleError> {
        Ok((self.canned.clone(), Some(100), Some(200)))
    }
}

#[tokio::test]
async fn llm_steering_changes_ga_behavior() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };

    let canned = json!({
        "version": 1,
        "scope": "C",
        "domain_weights": {
            "special_relativity": 0.25,
            "electromagnetism": 0.25,
            "classical_mechanics": 0.25,
            "thermodynamics": 0.25
        },
        "axiom_emphasis": {},
        "fitness_weights": {
            "novelty": 0.4,
            "dimensional_elegance": 0.3,
            "chain_length_penalty": 0.2,
            "target_proximity": 0.1
        },
        "soft_targets": [],
        "hard_targets": [],
        "mutation_knobs": {
            "rate": 0.25,
            "suffix_bias": 1.0,
            "population_size": 64,
            "elitism_fraction": 0.10
        },
        "mutation_priors": { "append_productive_suffix": 2.0 },
        "cluster_directives": [{
            "island_domain": "special_relativity",
            "centroid_skeleton_hash": 0u64,
            "action": "boost",
            "strength": 0.5
        }],
        "rationale": "test cycle"
    })
    .to_string();

    let fake = FakeLlmCaller { canned };

    // 1. Cycle runs end-to-end against the test PG.
    let cycle_id = run_one_cycle(
        // Reach into AppState via a re-borrow that matches run_one_cycle's signature.
        &app.state(),
        &app.pg,
        &fake,
        "test-model",
        true,
    )
    .await
    .expect("cycle ran");
    assert_ne!(cycle_id, uuid::Uuid::nil());

    // 2. Steering snapshot got swapped; cluster_config got populated.
    let snap = app.state().steering.load();
    assert_ne!(snap.etag, 0, "steering snapshot should be non-default");
    assert_eq!(snap.config["mutation_knobs"]["rate"], 0.25);
    assert_eq!(snap.config["cluster_directives"][0]["action"], "boost");
    let cc = app.state().cluster_config.load();
    assert!(
        !cc.k_per_island.is_empty(),
        "cluster_config should have all 6 islands populated by UCB1"
    );
    for domain in &[
        "special_relativity",
        "electromagnetism",
        "quantum_mechanics",
        "thermodynamics",
        "classical_mechanics",
        "general_relativity",
    ] {
        assert!(
            cc.k_per_island.contains_key(*domain),
            "missing K assignment for {domain}"
        );
    }

    // 3. /api/seed surfaces both steering + cluster_config.
    let resp = test_app::get(&app, "/api/seed").await;
    assert_eq!(resp.status, axum::http::StatusCode::OK);
    let v: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert_eq!(v["steering"]["config"]["mutation_knobs"]["rate"], 0.25);
    assert_eq!(
        v["steering"]["config"]["mutation_priors"]["append_productive_suffix"],
        2.0
    );
    assert!(v["cluster_config"]["k_per_island"].is_object());
    assert!(
        v["cluster_config"]["etag"]
            .as_str()
            .is_some_and(|s| !s.is_empty())
    );

    // 4. apply_steering_knobs picks up rate, suffix_bias, mutation_priors.
    let mut cfg = DiscoveryConfig::default();
    let baseline_rate = cfg.mutation_rate;
    let applied = apply_steering_knobs(&mut cfg, &v["steering"]);
    assert!(applied);
    assert_eq!(cfg.mutation_rate, 0.25);
    assert_ne!(cfg.mutation_rate, baseline_rate);
    let priors = cfg.mutation_priors.as_ref().expect("priors set");
    assert_eq!(priors.get("append_productive_suffix").copied(), Some(2.0));

    // 5. Operator distribution actually shifts. Sample 10k weighted picks
    //    against the LLM's priors + suffix_bias=1.0; the
    //    append_productive_suffix bucket should dominate (uniform would
    //    be ~16.7%; with prior=2.0 and suffix_bias=1.0 → weight = 2*5
    //    out of 5+2*5 = 15 → ~67% expected).
    let mut rng = StdRng::seed_from_u64(42);
    let weights = nasrudin_ga::chain_ga::resolve_weights_for_test(Some(priors), 1.0);
    let mut counts = [0u32; 6];
    for _ in 0..10_000 {
        let pick = nasrudin_ga::chain_ga::weighted_pick_for_test(&weights, &mut rng);
        counts[pick as usize] += 1;
    }
    let suffix_share = counts[5] as f32 / 10_000.0;
    let uniform_share = 1.0 / 6.0;
    assert!(
        suffix_share > uniform_share * 2.5,
        "expected ≥{:.3} suffix share (≥2.5× uniform), got {suffix_share}",
        uniform_share * 2.5
    );

    // 6. Bandit arms got materialised + at least the previous-K pull
    //    recorded for some island. Use special_relativity as a probe.
    let arms = physics_api::steerer::bandit::load_arms(&app.pg, "special_relativity")
        .await
        .expect("arm load");
    assert!(
        arms.len() == physics_api::steerer::bandit::K_VALUES.len(),
        "expected one arm per K_VALUES entry, got {}",
        arms.len()
    );
}

#[tokio::test]
async fn cluster_report_round_trips() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };

    // Register the cluster-report route on the test router. The
    // production router mounts it on the platform_worker layer (with
    // bearer auth + IP rate-limit); for this test we mount it bare.
    let router = app.router.clone().route(
        "/api/cluster-report",
        axum::routing::post(physics_api::handlers::cluster_report::handler).with_state(app.state()),
    );

    let body = json!({
        "worker_id": "11111111-1111-1111-1111-111111111111",
        "chunk_index": 7,
        "k_used": 4,
        "island_reports": [{
            "island_domain": "special_relativity",
            "summaries": [{
                "cluster_id": 0,
                "island_domain": "special_relativity",
                "size": 24,
                "mean_fitness": 0.42,
                "fitness_stddev": 0.08,
                "silhouette": 0.6,
                "dominant_axioms": [],
                "novelty_trend": 0.05,
                "stagnation_chunks": 2,
                "centroid_skeleton_hash": 1234567890u64
            }]
        }]
    });

    use axum::body::{Body, to_bytes};
    use axum::http::Request;
    use tower::util::ServiceExt;

    let req = Request::builder()
        .method("POST")
        .uri("/api/cluster-report")
        .header(axum::http::header::CONTENT_TYPE, "application/json")
        .body(Body::from(serde_json::to_vec(&body).unwrap()))
        .unwrap();
    let resp = router.oneshot(req).await.unwrap();
    assert_eq!(resp.status(), axum::http::StatusCode::OK);
    let body_bytes = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body_bytes).unwrap();
    assert_eq!(v["received"], true);
    assert_eq!(v["stored"], 1);

    // Verify the row landed in PG.
    let recent =
        nasrudin_pg::query::cluster_reports::recent_for_island(&app.pg, "special_relativity", 10)
            .await
            .unwrap();
    assert_eq!(recent.len(), 1);
    assert_eq!(recent[0].chunk_index, 7);
    assert_eq!(recent[0].k_used, 4);
}
