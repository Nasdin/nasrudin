//! End-to-end test for the per-cluster directive multiplier bandit.
//!
//! Seeds the directive_arms table with a deliberate skew so one
//! multiplier_choice wins UCB1 unambiguously. Then runs a steerer
//! cycle (with a FakeLlmCaller emitting one cluster_directive),
//! reads /api/seed, and asserts the snapshot carries the seeded skew.
//! Finally posts a directive_feedback batch and asserts record_pull
//! flipped the rows.

mod test_app;

use async_trait::async_trait;
use serde_json::json;

use physics_api::steerer::cycle::{run_one_cycle, CycleError, LlmCaller};

struct FakeLlmCaller {
    canned: String,
}

#[async_trait]
impl LlmCaller for FakeLlmCaller {
    async fn call(
        &self,
        _system: &str,
        _user: &str,
    ) -> Result<(String, Option<i32>, Option<i32>), CycleError> {
        Ok((self.canned.clone(), Some(50), Some(80)))
    }
}

#[tokio::test]
async fn directive_arms_snapshot_carries_seeded_skew() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };

    // Seed a single arm with high mean reward so UCB1 must pick it.
    physics_api::steerer::directive_bandit::ensure_all_arms(&app.pg)
        .await
        .expect("ensure arms");
    for choice in 0..5 {
        let reward = if choice == 3 { 0.9 } else { 0.1 };
        for _ in 0..10 {
            nasrudin_pg::query::cluster_directive_arms::record_pull(
                &app.pg,
                "special_relativity",
                "boost",
                2,
                choice,
                reward,
            )
            .await
            .unwrap();
        }
    }

    // Run a cycle to publish the snapshot to ArcSwap and seed cache.
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
            "rate": 0.20,
            "suffix_bias": 0.5,
            "population_size": 64,
            "elitism_fraction": 0.05
        },
        "mutation_priors": {},
        "cluster_directives": [{
            "island_domain": "special_relativity",
            "centroid_skeleton_hash": 0u64,
            "action": "boost",
            "strength": 0.5
        }],
        "rationale": "directive bandit e2e"
    })
    .to_string();
    let fake = FakeLlmCaller { canned };
    run_one_cycle(&app.state(), &app.pg, &fake, "test-model")
        .await
        .expect("cycle ran");

    // Read /api/seed and assert the directive_arms slot has the seeded skew.
    let resp = test_app::get(&app, "/api/seed").await;
    assert_eq!(resp.status, axum::http::StatusCode::OK);
    let v: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    let snapshot = v["directive_arms"]["snapshot"]
        .as_array()
        .expect("directive_arms.snapshot is an array");
    let slot = snapshot
        .iter()
        .find(|s| {
            s["island_domain"] == "special_relativity"
                && s["action"] == "boost"
                && s["strength_bucket"] == 2
        })
        .expect("seeded slot present");
    let arm_3 = slot["arms"]
        .as_array()
        .unwrap()
        .iter()
        .find(|a| a["multiplier_choice"] == 3)
        .unwrap();
    assert_eq!(arm_3["pulls"], 10);
    assert!((arm_3["mean_reward"].as_f64().unwrap() - 0.9).abs() < 1e-6);

    // Locally exercise the worker's UCB1: arm 3 should win.
    let arms_local: Vec<(u8, i64, f64)> = slot["arms"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| {
            let c = a["multiplier_choice"].as_u64().unwrap() as u8;
            let p = a["pulls"].as_i64().unwrap();
            let mean = a["mean_reward"].as_f64().unwrap();
            (c, p, mean * p as f64)
        })
        .collect();
    let pick = ucb1_pick(&arms_local);
    assert_eq!(pick, 3, "UCB1 should pick the seeded high-reward arm");
}

/// Mirror of the worker's `pick_multiplier_choice` for the e2e check.
/// Lives in the test file so the test doesn't pull in the worker binary.
fn ucb1_pick(arms: &[(u8, i64, f64)]) -> u8 {
    let total: i64 = arms.iter().map(|(_, p, _)| *p).sum();
    if total < 15 {
        return 0;
    }
    if let Some((c, _, _)) = arms.iter().find(|(_, p, _)| *p == 0) {
        return *c;
    }
    let ln_n = (total as f64).ln();
    let mut best = arms[0].0;
    let mut best_score = f64::NEG_INFINITY;
    for &(c, p, t) in arms {
        let mean = if p > 0 { t / p as f64 } else { 0.0 };
        let exploration = (2.0 * ln_n / p as f64).sqrt();
        let score = mean + exploration;
        if score > best_score {
            best_score = score;
            best = c;
        }
    }
    best
}

#[tokio::test]
async fn directive_feedback_records_pulls() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };
    physics_api::steerer::directive_bandit::ensure_all_arms(&app.pg)
        .await
        .expect("ensure arms");

    // Mount the endpoint locally on the existing test router.
    let router = app.router.clone().route(
        "/api/directive-feedback",
        axum::routing::post(physics_api::handlers::directive_feedback::handler)
            .with_state(app.state()),
    );

    use axum::body::{to_bytes, Body};
    use axum::http::Request;
    use tower::util::ServiceExt;

    let body = json!({
        "feedback": [
            {
                "island_domain": "special_relativity",
                "action": "boost",
                "strength_bucket": 1,
                "multiplier_choice": 2,
                "reward": 0.7
            },
            {
                "island_domain": "thermodynamics",
                "action": "exploit",
                "strength_bucket": 4,
                "multiplier_choice": 0,
                "reward": 0.3
            }
        ]
    });
    let req = Request::builder()
        .method("POST")
        .uri("/api/directive-feedback")
        .header(axum::http::header::CONTENT_TYPE, "application/json")
        .body(Body::from(serde_json::to_vec(&body).unwrap()))
        .unwrap();
    let resp = router.oneshot(req).await.unwrap();
    assert_eq!(resp.status(), axum::http::StatusCode::OK);
    let body_bytes = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body_bytes).unwrap();
    assert_eq!(v["received"], true);
    assert_eq!(v["applied"], 2);

    // Verify the rows actually moved.
    let arms = nasrudin_pg::query::cluster_directive_arms::list_for_slot(
        &app.pg,
        "special_relativity",
        "boost",
        1,
    )
    .await
    .unwrap();
    let chosen = arms
        .iter()
        .find(|a| a.multiplier_choice == 2)
        .expect("seeded slot exists");
    assert_eq!(chosen.pulls, 1);
    assert!((chosen.last_reward - 0.7).abs() < 1e-6);
}

#[tokio::test]
async fn directive_feedback_rejects_bad_action_and_buckets() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };
    physics_api::steerer::directive_bandit::ensure_all_arms(&app.pg)
        .await
        .expect("ensure arms");
    let router = app.router.clone().route(
        "/api/directive-feedback",
        axum::routing::post(physics_api::handlers::directive_feedback::handler)
            .with_state(app.state()),
    );
    use axum::body::{to_bytes, Body};
    use axum::http::Request;
    use tower::util::ServiceExt;

    // Two malformed entries should be silently dropped (handler logs
    // and continues), so applied should be 0.
    let body = json!({
        "feedback": [
            { "island_domain": "x", "action": "explode", "strength_bucket": 0,
              "multiplier_choice": 0, "reward": 0.5 },
            { "island_domain": "x", "action": "boost", "strength_bucket": 99,
              "multiplier_choice": 0, "reward": 0.5 }
        ]
    });
    let req = Request::builder()
        .method("POST")
        .uri("/api/directive-feedback")
        .header(axum::http::header::CONTENT_TYPE, "application/json")
        .body(Body::from(serde_json::to_vec(&body).unwrap()))
        .unwrap();
    let resp = router.oneshot(req).await.unwrap();
    assert_eq!(resp.status(), axum::http::StatusCode::OK);
    let body_bytes = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body_bytes).unwrap();
    assert_eq!(v["received"], true);
    assert_eq!(v["applied"], 0);
}
