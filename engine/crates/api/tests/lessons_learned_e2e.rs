//! End-to-end test for the rolling `lessons_learned` indefinite-
//! horizon LLM memory.
//!
//! Runs two cycles back-to-back with a stateful `FakeLlmCaller`:
//!
//!   Cycle 1: LLM emits SteeringConfig with lessons_learned =
//!            "Boost@SR worked. Diversify@QM hurt."
//!            Row lands in cluster_steering with that lessons string.
//!
//!   Cycle 2: build_prompt loads the cycle-1 lessons via
//!            last_known_good and surfaces them as
//!            previous_lessons_learned. The fake caller captures the
//!            received prompt; we assert cycle-1's lessons appear
//!            verbatim. Then the LLM emits a REPLACEMENT (rolling,
//!            not appending) lessons string. Row lands; we assert
//!            the cycle-2 row has the new lessons, NOT the cycle-1
//!            ones.
//!
//! Proves: persistence → load → prompt-surface → rewrite → persist.
//! The full round-trip the rolling-memory feature depends on.

mod test_app;

use async_trait::async_trait;
use serde_json::json;
use std::sync::{Arc, Mutex};

use physics_api::steerer::cycle::{CycleError, LlmCaller, run_one_cycle};

/// Stateful caller: returns a queue of canned responses in order,
/// and captures every prompt it receives so the test can inspect
/// what the cycle actually sent. Single-threaded by construction
/// (only one cycle runs at a time in this test).
struct ScriptedLlmCaller {
    responses: Mutex<std::collections::VecDeque<String>>,
    captured_prompts: Arc<Mutex<Vec<String>>>,
}

#[async_trait]
impl LlmCaller for ScriptedLlmCaller {
    async fn call(
        &self,
        _system: &str,
        user: &str,
    ) -> Result<(String, Option<i32>, Option<i32>), CycleError> {
        self.captured_prompts.lock().unwrap().push(user.to_string());
        let next = self
            .responses
            .lock()
            .unwrap()
            .pop_front()
            .expect("ScriptedLlmCaller: no canned response left");
        Ok((next, Some(50), Some(80)))
    }
}

fn canned(lessons: &str) -> String {
    json!({
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
        "cluster_directives": [],
        "compute_directives": [],
        "target_status_updates": [],
        "extension": null,
        "lessons_learned": lessons,
        "rationale": "lessons round-trip e2e"
    })
    .to_string()
}

#[tokio::test]
async fn lessons_round_trip_across_two_cycles() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };

    let cycle_1_lessons =
        "Boost@SR strength=0.5 → 1.5× worked. Diversify@QM strength=0.7 hurt yields.";
    let cycle_2_lessons = "(updated) SR boost still working — extending to 2.0× this cycle. \
         QM remains noisy; trying Exploit@QM instead. Compute scaling 1.5× sweet spot.";

    let mut queue = std::collections::VecDeque::new();
    queue.push_back(canned(cycle_1_lessons));
    queue.push_back(canned(cycle_2_lessons));
    let captured = Arc::new(Mutex::new(Vec::<String>::new()));
    let fake = ScriptedLlmCaller {
        responses: Mutex::new(queue),
        captured_prompts: Arc::clone(&captured),
    };

    eprintln!("\n========================================");
    eprintln!("  ROLLING LESSONS_LEARNED — END-TO-END TRACE");
    eprintln!("========================================\n");

    // ── Cycle 1 ─────────────────────────────────────────────
    eprintln!("┌─ CYCLE 1 ──────────────────────────────");
    run_one_cycle(&app.state(), &app.pg, &fake, "test-model", true)
        .await
        .expect("cycle 1 ran");

    // The first prompt should have an EMPTY previous_lessons_learned
    // (cold boot — no prior cycle to load from).
    {
        let prompts = captured.lock().unwrap();
        assert_eq!(prompts.len(), 1);
        assert!(
            prompts[0].contains("previous_lessons_learned"),
            "cycle 1 prompt missing previous_lessons_learned key"
        );
        // The empty-string surface looks like  "previous_lessons_learned": "",
        assert!(
            prompts[0].contains("\"previous_lessons_learned\": \"\""),
            "cycle 1 should see empty lessons (cold boot); got prompt:\n{}",
            &prompts[0]
                .split("previous_lessons_learned")
                .nth(1)
                .map(|s| &s[..120.min(s.len())])
                .unwrap_or("(not found)")
        );
        eprintln!("│  Prompt seen by LLM:  previous_lessons_learned = \"\"  (cold boot, no LKG)");
    }
    eprintln!("│  LLM emitted lessons: {:?}", cycle_1_lessons);

    // After cycle 1, PG holds a row whose config_json.lessons_learned
    // is exactly what the LLM emitted.
    let after_1 = nasrudin_pg::query::cluster_steering::most_recent(&app.pg)
        .await
        .unwrap()
        .expect("cycle 1 row persisted");
    let lessons_1 = after_1
        .config_json
        .get("lessons_learned")
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert_eq!(lessons_1, cycle_1_lessons, "cycle 1 lessons must persist");
    eprintln!(
        "│  PG row id={}: config_json.lessons_learned = {:?}",
        after_1.id, lessons_1
    );
    eprintln!("└──────────────────────────────────────────\n");

    // ── Cycle 2 ─────────────────────────────────────────────
    eprintln!("┌─ CYCLE 2 ──────────────────────────────");
    run_one_cycle(&app.state(), &app.pg, &fake, "test-model", true)
        .await
        .expect("cycle 2 ran");

    // Cycle 2's prompt MUST contain cycle 1's lessons verbatim. This
    // is the load-from-LKG → surface-in-prompt half of the loop.
    {
        let prompts = captured.lock().unwrap();
        assert_eq!(prompts.len(), 2);
        let p2 = &prompts[1];
        assert!(
            p2.contains("previous_lessons_learned"),
            "cycle 2 prompt missing previous_lessons_learned key"
        );
        assert!(
            p2.contains("Boost@SR strength=0.5") && p2.contains("Diversify@QM"),
            "cycle 2 must see cycle 1's lessons; got:\n{}",
            p2.split("previous_lessons_learned")
                .nth(1)
                .map(|s| &s[..400.min(s.len())])
                .unwrap_or("(not found)")
        );
        // And cycle 2's prompt MUST NOT see cycle 2's lessons yet —
        // those are emitted IN this cycle's response.
        assert!(
            !p2.contains("(updated) SR boost still working"),
            "cycle 2's own emitted lessons must not pre-leak into its prompt"
        );
        // Pull the actual previous_lessons_learned snippet out of the
        // prompt JSON so we can show what the LLM literally received.
        let snippet = p2
            .split("\"previous_lessons_learned\": \"")
            .nth(1)
            .and_then(|s| s.split("\",").next())
            .unwrap_or("(not found)");
        eprintln!("│  Prompt seen by LLM:");
        eprintln!("│    previous_lessons_learned = {:?}", snippet);
    }
    eprintln!("│  LLM emitted (replacement, NOT append):");
    eprintln!("│    {:?}", cycle_2_lessons);

    // After cycle 2, the latest row's lessons_learned must be the
    // REPLACEMENT (cycle 2), not an append-of-both.
    let after_2 = nasrudin_pg::query::cluster_steering::most_recent(&app.pg)
        .await
        .unwrap()
        .expect("cycle 2 row persisted");
    let lessons_2 = after_2
        .config_json
        .get("lessons_learned")
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert_eq!(
        lessons_2, cycle_2_lessons,
        "cycle 2 lessons must REPLACE cycle 1's, not append"
    );
    // Confirm cycle 1's lessons are NOT inside cycle 2's lessons —
    // that would mean append, which violates the rolling contract.
    assert!(
        !lessons_2.contains("Diversify@QM strength=0.7"),
        "cycle 2 lessons must not contain cycle 1's text (rolling, not appending)"
    );
    eprintln!(
        "│  PG row id={}: config_json.lessons_learned = {:?}",
        after_2.id, lessons_2
    );
    eprintln!("└──────────────────────────────────────────\n");
    eprintln!("✓ ROUND-TRIP VERIFIED:");
    eprintln!("  · Cycle 1 → PG (cold-boot lessons persisted)");
    eprintln!("  · PG → Cycle 2 prompt (LKG-loaded into previous_lessons_learned)");
    eprintln!("  · Cycle 2 LLM emits replacement → PG (rolling, not appending)");
    eprintln!();
}

#[tokio::test]
async fn cold_boot_surfaces_empty_lessons_then_first_emission_persists() {
    // Sanity: the first ever cycle on a fresh DB should see empty
    // previous_lessons_learned (no LKG row), then the freshly
    // emitted lessons should land — independent of the round-trip
    // assertions above. Smaller, complementary check.
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };

    let lessons = "First emission. Nothing learned yet — populating from scratch.";
    let mut queue = std::collections::VecDeque::new();
    queue.push_back(canned(lessons));
    let captured = Arc::new(Mutex::new(Vec::<String>::new()));
    let fake = ScriptedLlmCaller {
        responses: Mutex::new(queue),
        captured_prompts: Arc::clone(&captured),
    };

    run_one_cycle(&app.state(), &app.pg, &fake, "test-model", true)
        .await
        .expect("cold-boot cycle ran");

    let prompts = captured.lock().unwrap();
    assert!(prompts[0].contains("\"previous_lessons_learned\": \"\""));

    let row = nasrudin_pg::query::cluster_steering::most_recent(&app.pg)
        .await
        .unwrap()
        .expect("row persisted");
    let stored = row
        .config_json
        .get("lessons_learned")
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert_eq!(stored, lessons);
}
