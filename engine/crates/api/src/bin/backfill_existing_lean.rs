//! `backfill_existing_lean` — one-shot binary to seed a fresh deployment with
//! the committed reference proofs from `prover/PhysicsGenerator/Derived/*.lean`.
//!
//! Walks the `Derived/` directory, extracts the canonical theorem statement
//! from each `.lean` file via a heuristic regex, and POSTs each one through
//! the production `/api/ingest` endpoint so the corpus has the historical
//! reference proofs (`RestEnergyUpstream.lean`,  `AutoRestEnergyUpstream.lean`,
//! `PhotonEnergyMomentum.lean`, plus prior `Discover*.lean` discoveries) on
//! day 1 of a fresh-droplet bootstrap.
//!
//! Phase 9 Task 7.2.

use anyhow::Result;
use std::path::Path;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::try_init().ok();

    let prover = std::env::var("PROVER_ROOT").unwrap_or_else(|_| "../prover".into());
    let derived = Path::new(&prover).join("PhysicsGenerator/Derived");
    let api_url =
        std::env::var("NASRUDIN_API_URL").unwrap_or_else(|_| "http://localhost:3001".into());
    let key = std::env::var("NASRUDIN_BACKFILL_KEY")
        .map_err(|_| anyhow::anyhow!("NASRUDIN_BACKFILL_KEY env var required"))?;

    if !derived.exists() {
        anyhow::bail!("Derived/ directory not found: {}", derived.display());
    }

    let client = reqwest::Client::new();
    let mut submitted = 0;
    let mut skipped = 0;
    let mut errors = 0;

    for entry in walkdir::WalkDir::new(&derived).max_depth(1) {
        let entry = entry?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        if path.extension().and_then(|s| s.to_str()) != Some("lean") {
            continue;
        }

        let lean_source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                tracing::warn!(file = %path.display(), err = %e, "backfill: read failed");
                errors += 1;
                continue;
            }
        };

        let canonical = extract_canonical(&lean_source).unwrap_or_else(|| {
            // Fallback: use the file stem as the canonical identifier so the row
            // is at least dedup-stable.
            path.file_stem()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_default()
        });

        if canonical.is_empty() {
            tracing::warn!(file = %path.display(), "backfill: could not extract canonical, skipping");
            skipped += 1;
            continue;
        }

        let domain = infer_domain(path);

        let payload = serde_json::json!({
            "worker_id": "backfill",
            "engine_git_sha": "backfill",
            "lean_version": "4.27.0",
            "theorems": [{
                "canonical_statement": canonical,
                "domain": domain,
                "lean_source": lean_source,
                "chain": [],
                "axioms_used": [],
                "origin": {
                    "type": "Imported",
                    "source": format!(
                        "backfill:{}",
                        path.file_name().unwrap_or_default().to_string_lossy()
                    ),
                },
            }]
        });

        match client
            .post(format!("{api_url}/api/ingest"))
            .bearer_auth(&key)
            .json(&payload)
            .send()
            .await
        {
            Ok(resp) => {
                let status = resp.status();
                let body: serde_json::Value = resp.json().await.unwrap_or_default();
                let result_kind = body
                    .get("results")
                    .and_then(|r| r.as_array())
                    .and_then(|arr| arr.first())
                    .and_then(|first| first.get("status"))
                    .and_then(|s| s.get("kind"))
                    .and_then(|k| k.as_str())
                    .unwrap_or("?");
                tracing::info!(
                    file = %path.display(),
                    status = %status,
                    result = %result_kind,
                    "backfill: submitted"
                );
                if status.is_success() && (result_kind == "Pending" || result_kind == "Duplicate") {
                    submitted += 1;
                } else {
                    errors += 1;
                }
            }
            Err(e) => {
                tracing::error!(file = %path.display(), err = %e, "backfill: HTTP error");
                errors += 1;
            }
        }
    }

    println!("Backfill complete: submitted={submitted} skipped={skipped} errors={errors}");
    if errors > 0 {
        anyhow::bail!("{errors} files failed to ingest");
    }
    Ok(())
}

/// Extract the canonical theorem statement from a Lean source file.
/// Looks for `theorem <name> [args] : <statement> := ...` and returns `<statement>`.
/// Falls back to None if the regex doesn't match.
fn extract_canonical(src: &str) -> Option<String> {
    let re = regex::Regex::new(r"(?s)theorem\s+\w+(?:\s*\([^)]*\))*\s*:\s*([^:]*?)\s*:=").ok()?;
    let caps = re.captures(src)?;
    let m = caps.get(1)?;
    let s = m.as_str().trim();
    if s.is_empty() {
        None
    } else {
        Some(s.to_string())
    }
}

/// Heuristically infer the physics domain from the Lean file path / contents.
/// For Phase 9 this is best-effort; the resulting Domain just affects
/// `/browse` filtering.
fn infer_domain(path: &Path) -> &'static str {
    let name = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
    if name.contains("RestEnergy") || name.contains("Photon") {
        "SpecialRelativity"
    } else if name.contains("Disc") {
        // GA-discovered theorems
        "PureMath"
    } else {
        "PureMath"
    }
}
