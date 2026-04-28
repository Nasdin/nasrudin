//! Phase 9 / Task 10.1 — end-to-end ingest round-trip test.
//!
//! Hand-coded `RestEnergyUpstream.lean` -> `/api/ingest` -> Verified.
//!
//! Gated behind `#[ignore]` because it requires:
//!   - A running API server at `$NASRUDIN_API_URL` (or `http://localhost:3001`).
//!   - A valid worker bearer key in `$NASRUDIN_INTERNAL_WORKER_KEY`.
//!   - The `prover/` tree on disk so the API container can lake-build it
//!     (override location with `$PROVER_ROOT`; default is `../../../prover`
//!     relative to the api crate root).
//!   - Up to 180s of patience for cold-cache lake builds.
//!
//! Operators run this nightly via:
//!   cargo test -p physics-api --test e2e_spontaneous_emc2_ingest -- --ignored

use std::time::Duration;

#[tokio::test]
#[ignore]
async fn rest_energy_upstream_round_trips_through_ingest() -> anyhow::Result<()> {
    let api = std::env::var("NASRUDIN_API_URL").unwrap_or_else(|_| "http://localhost:3001".into());
    let key = std::env::var("NASRUDIN_INTERNAL_WORKER_KEY")
        .map_err(|_| anyhow::anyhow!("NASRUDIN_INTERNAL_WORKER_KEY required"))?;

    // Read the canonical hand-proof from the committed prover tree.
    let lean_path = std::env::var("PROVER_ROOT").unwrap_or_else(|_| "../../../prover".into());
    let lean_file = format!("{lean_path}/PhysicsGenerator/Derived/RestEnergyUpstream.lean");
    let lean_source = std::fs::read_to_string(&lean_file)
        .map_err(|e| anyhow::anyhow!("failed to read {lean_file}: {e}"))?;

    // Use a unique canonical_statement so we don't dedupe-collide with prior runs.
    let canonical = format!("E_eq_mc2_e2e_{}", chrono::Utc::now().timestamp());

    let payload = serde_json::json!({
        "worker_id": "in-proc-worker-1",
        "engine_git_sha": "e2e",
        "lean_version": "4.27.0",
        "theorems": [{
            "canonical_statement": canonical,
            "domain": "SpecialRelativity",
            "lean_source": lean_source,
            "chain": [],
            "axioms_used": [
                "four_momentum_time_component",
                "minkowski_invariant_def",
                "invariant_mass_postulate",
                "rest_frame_psq_zero",
                "c_positive",
                "mass_nonneg",
                "energy_nonneg",
            ],
        }]
    });

    let client = reqwest::Client::new();
    let resp = client
        .post(format!("{api}/api/ingest"))
        .bearer_auth(&key)
        .json(&payload)
        .send()
        .await?;
    let status = resp.status();
    let body: serde_json::Value = resp.json().await?;
    if !status.is_success() {
        anyhow::bail!("ingest failed status={status} body={body}");
    }

    let theorem_id = body["results"][0]["theorem_id"]
        .as_str()
        .ok_or_else(|| anyhow::anyhow!("response missing theorem_id: {body}"))?
        .to_string();
    let result_kind = body["results"][0]["status"]["kind"].as_str().unwrap_or("?");
    eprintln!("ingest accepted: theorem_id={theorem_id} kind={result_kind}");

    // Poll until Verified (or 180s timeout).
    let deadline = std::time::Instant::now() + Duration::from_secs(180);
    while std::time::Instant::now() < deadline {
        tokio::time::sleep(Duration::from_secs(5)).await;
        let r = client
            .get(format!("{api}/api/theorems/{theorem_id}"))
            .send()
            .await?;
        if !r.status().is_success() {
            continue;
        }
        let row: serde_json::Value = r.json().await?;
        let st = row["status"].as_str().unwrap_or("?");
        eprintln!("poll status={st}");
        match st {
            "Verified" => {
                eprintln!(
                    "verified: verification_path={} duration_ms={}",
                    row["verification_path"], row["verification_duration_ms"]
                );
                // Sanity-check the row is the one we just ingested.
                assert_eq!(
                    row["status"].as_str(),
                    Some("Verified"),
                    "status must be Verified"
                );
                let returned_source = row["lean_source"].as_str().unwrap_or("");
                assert_eq!(
                    returned_source, lean_source,
                    "lean_source from /api/theorems/<hash> must match ingested source"
                );
                return Ok(());
            }
            "Rejected" => anyhow::bail!("rejected: {}", row["rejected_reason"]),
            _ => {} // Pending — keep polling
        }
    }
    anyhow::bail!("did not reach Verified within 180s");
}
