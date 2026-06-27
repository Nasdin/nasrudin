//! Goal-directed beam search for E=mc². Parallel to `discover_emc2`
//! (random GA), trades breadth for depth: maintains a small frontier
//! of best-scoring chains, expands each by one rule per step, prunes
//! by ladder distance to a configured `TargetSpec`.
//!
//! Usage:
//!
//!     beam_emc2 --target sr_rest_energy [--width 32] [--depth 12]
//!         [--accept 0.95] [--verify ./prover]
//!
//! Submits the same way `discover_emc2` does: HTTP POST to
//! `/api/ingest` with `Authorization: Bearer $NASRUDIN_WORKER_KEY`.
//! The chain firewall replays + lake-builds independently — the beam
//! binary's job is just to *find* the chain.

use std::path::PathBuf;
use std::time::Instant;

use nasrudin_derive::AxiomStore;
use nasrudin_ga::{
    beam::{BeamConfig, beam_search},
    target::TargetSpec,
};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let argv: Vec<String> = std::env::args().collect();
    let get_arg = |key: &str| -> Option<String> {
        argv.windows(2).find(|w| w[0] == key).map(|w| w[1].clone())
    };
    let has_flag = |key: &str| -> bool { argv.iter().any(|a| a == key) };

    let target_name = get_arg("--target")
        .or_else(|| std::env::var("NASRUDIN_TARGET").ok())
        .unwrap_or_else(|| "sr_rest_energy".into());
    let target = TargetSpec::lookup(&target_name).ok_or_else(|| {
        anyhow::anyhow!("unknown target spec `{target_name}` (available: sr_rest_energy)")
    })?;

    let width = get_arg("--width")
        .and_then(|s| s.parse().ok())
        .unwrap_or(32);
    let depth = get_arg("--depth")
        .and_then(|s| s.parse().ok())
        .unwrap_or(12);
    let accept = get_arg("--accept")
        .and_then(|s| s.parse().ok())
        .unwrap_or(0.95);
    let prover_root: Option<PathBuf> = get_arg("--verify").map(PathBuf::from);

    let domain = get_arg("--domain").unwrap_or_else(|| "sr".into());

    println!("═══════════════════════════════════════════════════════");
    println!("  Nasrudin Goal-Directed Beam Search");
    println!("  target = {}, domain = {domain}", target.name);
    println!("  width = {width}, depth = {depth}, accept ≥ {accept}");
    println!("═══════════════════════════════════════════════════════\n");

    // Build the AxiomStore: upstream postulates + (optionally) seed-sync.
    let mut store = AxiomStore::new();
    // Newtonian postulates first; SR/EM upstream layered on top. The
    // server's AxiomStore loads the same set so chain replay matches.
    store.load_classical_mechanics_postulates();
    match domain.as_str() {
        "sr" => store.load_special_relativity_upstream(),
        "em" => store.load_electromagnetism_upstream(),
        other => anyhow::bail!("unknown domain `{other}` (try `sr` or `em`)"),
    }

    println!("▶ AxiomStore: {} upstream axioms", store.len());

    // No-cheat audit BEFORE seed-sync. (Seed-sync may legitimately add
    // peer-verified theorems that contain the headline once any worker
    // has already discovered it; this is the compounding behaviour we
    // want, not cheating. The audit on PRE-seed-sync state catches a
    // bad upstream loader.)
    nasrudin_derive::no_cheat_audit::audit_or_panic(&store, "beam pre-seed-sync");
    println!("  ✓ no-cheat audit on upstream store passed");

    if !has_flag("--no-seed-sync")
        && let Ok(api_url) = std::env::var("NASRUDIN_API_URL")
    {
        match seed_sync(&api_url, &domain, &mut store).await {
            Ok((axioms, theorems)) => {
                println!("▶ Seed-sync: +{axioms} axioms, +{theorems} peer theorems");
            }
            Err(e) => eprintln!("  ! seed-sync skipped: {e}"),
        }
    }
    println!("  store size: {} entries\n", store.len());

    let cfg = BeamConfig {
        beam_width: width,
        max_depth: depth,
        accept_threshold: accept,
        stagnation_window: 5,
    };

    let t0 = Instant::now();
    let report = beam_search(&store, &target, &cfg);
    println!(
        "▶ Beam search complete in {:.1}s ({} iterations)",
        t0.elapsed().as_secs_f64(),
        report.iterations
    );
    println!("  frontier final: {} states", report.frontier_final.len());
    println!("  candidates ≥ {}: {}", accept, report.candidates.len());
    println!();

    // Top of the final frontier — for the operator to see how close we got.
    println!("▶ Top frontier (best 5 by score):");
    for (i, s) in report.frontier_final.iter().take(5).enumerate() {
        println!(
            "  {}. ladder={:.3}  shape={:.3}  coverage={:.3}  steps={}",
            i + 1,
            s.ladder,
            s.shape,
            s.coverage,
            s.chain.0.len()
        );
        println!("     final: {}", s.expr.to_canonical());
    }
    println!();

    if report.candidates.is_empty() {
        println!("▶ No candidate cleared the {accept} threshold this run.");
        println!("  Try a longer run (--depth 16 --width 64) or a wider corpus.");
        return Ok(());
    }

    // Lake builds are slow (~30s/candidate). Pick the top-K by
    // (shape DESC, IntroduceAxiom-count DESC) — RearrangeEquation
    // discharges via nlinarith over the accumulated facts, so the more
    // IntroduceAxioms in the chain prefix, the more hypotheses Lean has
    // in scope. Then dedup by `(canonical, intro_count)` keeping the
    // version with the most hypotheses for each canonical. Override
    // with --max-verify N.
    let max_verify: usize = get_arg("--max-verify")
        .and_then(|s| s.parse().ok())
        .unwrap_or(8);
    // Count *distinct* IntroduceAxiom names in the chain. Repeated
    // introductions of the same axiom add no new fact, so they don't
    // help nlinarith — and bias the dedup picker toward chains with
    // more *unique* hypotheses.
    let intro_count = |s: &nasrudin_ga::beam::BeamState| -> usize {
        use nasrudin_derive::RuleStep;
        let mut names = std::collections::HashSet::new();
        for step in &s.chain.0 {
            if let RuleStep::IntroduceAxiom { axiom_name } = step {
                names.insert(axiom_name.clone());
            }
        }
        names.len()
    };
    let mut by_canonical: std::collections::HashMap<String, nasrudin_ga::beam::BeamState> =
        std::collections::HashMap::new();
    for cand in &report.candidates {
        let canon = cand.expr.to_canonical();
        match by_canonical.get(&canon) {
            None => {
                by_canonical.insert(canon, cand.clone());
            }
            Some(existing) if intro_count(cand) > intro_count(existing) => {
                by_canonical.insert(canon, cand.clone());
            }
            _ => {}
        }
    }
    // Score for the picker: prefer chains that end with the canonical
    // pattern `RearrangeEquation(...) → TakePositiveRoot`. That's the
    // shape Lean's `Real.sqrt_sq` discharges directly; a bare
    // `RearrangeEquation` to the final target asks nlinarith to invent
    // the square root, which it almost never does for non-trivial
    // polynomials. Boost +0.5 to the score so a 5-step chain ending
    // in `Rearrange(rung_2) + TakePositiveRoot` outranks a 4-step
    // chain ending in `Rearrange(final)` even at equal shape.
    let canonical_pattern_bonus = |s: &nasrudin_ga::beam::BeamState| -> f64 {
        use nasrudin_derive::RuleStep;
        let n = s.chain.0.len();
        if n < 2 {
            return 0.0;
        }
        match (&s.chain.0[n - 2], &s.chain.0[n - 1]) {
            (RuleStep::RearrangeEquation { .. }, RuleStep::TakePositiveRoot) => 0.5,
            _ => 0.0,
        }
    };
    let pick_score = |s: &nasrudin_ga::beam::BeamState| -> f64 {
        s.shape + canonical_pattern_bonus(s) + 0.05 * (intro_count(s) as f64)
    };
    let mut sorted: Vec<_> = by_canonical.into_values().collect();
    sorted.sort_by(|a, b| {
        pick_score(b)
            .partial_cmp(&pick_score(a))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    let pick: Vec<_> = sorted.into_iter().take(max_verify).collect();
    println!(
        "▶ Verifying top {} of {} unique candidates (use --max-verify N to change)",
        pick.len(),
        report.candidates.len()
    );

    // Verify and submit each candidate that cleared the threshold.
    let prover_root = match &prover_root {
        Some(p) => p,
        None => {
            println!(
                "▶ {} candidate(s) above threshold but --verify <prover_root> not given.",
                report.candidates.len()
            );
            println!("  Re-run with `--verify ./prover` to lake-build and submit.");
            return Ok(());
        }
    };

    let api_url = std::env::var("NASRUDIN_API_URL").ok();
    let worker_key = std::env::var("NASRUDIN_WORKER_KEY").ok();
    let worker_id = std::env::var("NASRUDIN_WORKER_ID")
        .ok()
        .unwrap_or_else(|| "beam-emc2".into());

    for (i, cand) in pick.iter().enumerate() {
        let mod_name = format!("Beam_{}", i);
        let theorem_name = format!("beam_{}", i);
        println!("▶ Verifying candidate {} (shape={:.3}):", i, cand.shape);
        println!("    {}", cand.expr.to_canonical());
        match nasrudin_ga::chain_ga::verify_chain(
            &cand.chain,
            &store,
            prover_root,
            &mod_name,
            &theorem_name,
        ) {
            nasrudin_ga::chain_ga::ChainVerifyOutcome::Verified {
                lean_source,
                module_path,
            } => {
                println!("    ✓ lake-verified");
                if let (Some(api), Some(key)) = (api_url.as_ref(), worker_key.as_ref()) {
                    if let Err(e) = submit(api, key, &worker_id, cand, &lean_source).await {
                        eprintln!("    ! submit failed: {e}");
                    } else {
                        println!("    ✓ submitted to {api}");
                    }
                }
                let _ = module_path;
            }
            nasrudin_ga::chain_ga::ChainVerifyOutcome::LeanRejected { stderr, .. } => {
                println!(
                    "    ✗ lean rejected: {}",
                    stderr.lines().next().unwrap_or("(no stderr)")
                );
            }
            nasrudin_ga::chain_ga::ChainVerifyOutcome::PreFilterFailed { reason } => {
                println!("    ✗ pre-filter failed: {reason}");
            }
            nasrudin_ga::chain_ga::ChainVerifyOutcome::ToolchainError { message } => {
                println!("    ! toolchain error: {message} (will not retry)");
            }
        }
    }

    Ok(())
}

async fn seed_sync(
    api_url: &str,
    domain: &str,
    store: &mut AxiomStore,
) -> anyhow::Result<(usize, usize)> {
    use nasrudin_core::Expr;
    use nasrudin_derive::{
        Axiom, Chain, DerivationContext, RuleStep, strategies::DerivationStrategy,
    };
    let domain_param = match domain {
        "sr" => "SpecialRelativity",
        "em" => "Electromagnetism",
        _ => "",
    };
    let url = if domain_param.is_empty() {
        format!("{api_url}/api/seed?top=200")
    } else {
        format!("{api_url}/api/seed?domain={domain_param}&top=200")
    };
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(15))
        .build()?;
    let resp = client.get(&url).send().await?;
    if !resp.status().is_success() {
        anyhow::bail!("seed http {}", resp.status());
    }
    let body: serde_json::Value = resp.json().await?;
    let mut axioms_added = 0;
    if let Some(arr) = body.get("axioms").and_then(|v| v.as_array()) {
        for entry in arr {
            let Some(name) = entry.get("name").and_then(|v| v.as_str()) else {
                continue;
            };
            if store.get(name).is_some() {
                continue;
            }
            let Some(stmt_str) = entry.get("statement").and_then(|v| v.as_str()) else {
                continue;
            };
            let Ok(stmt) = serde_json::from_str::<Expr>(stmt_str) else {
                continue;
            };
            store.register(Axiom {
                name: name.to_string(),
                domain: nasrudin_core::Domain::PureMath,
                statement: stmt,
                description: format!("seed-sync from {api_url}"),
            });
            axioms_added += 1;
        }
    }
    let mut theorems_added = 0;
    if let Some(arr) = body.get("seed_theorems").and_then(|v| v.as_array()) {
        for t in arr {
            let chain_val = match t.get("chain_json") {
                Some(c) => c,
                None => continue,
            };
            if chain_val.is_null() {
                continue;
            }
            let Ok(steps): Result<Vec<RuleStep>, _> = serde_json::from_value(chain_val.clone())
            else {
                continue;
            };
            if steps.is_empty() {
                continue;
            }
            let chain = Chain(steps);
            let mut ctx = DerivationContext::new();
            let Ok(final_expr) = chain.execute(store, &mut ctx) else {
                continue;
            };
            let canon = t
                .get("canonical_statement")
                .and_then(|v| v.as_str())
                .unwrap_or_default();
            if canon.is_empty() {
                continue;
            }
            let name = format!(
                "peer_{:016x}",
                xxhash_rust::xxh64::xxh64(canon.as_bytes(), 0)
            );
            if store.get(&name).is_some() {
                continue;
            }
            store.register(Axiom {
                name,
                domain: nasrudin_core::Domain::PureMath,
                statement: final_expr,
                description: "peer-verified theorem (seed-sync)".to_string(),
            });
            theorems_added += 1;
        }
    }
    Ok((axioms_added, theorems_added))
}

async fn submit(
    api_url: &str,
    worker_key: &str,
    worker_id: &str,
    cand: &nasrudin_ga::beam::BeamState,
    lean_source: &str,
) -> anyhow::Result<()> {
    use nasrudin_derive::RuleStep;
    let chain_json = serde_json::to_value(&cand.chain.0)?;
    let axioms_used: Vec<String> = cand
        .chain
        .0
        .iter()
        .filter_map(|s| match s {
            RuleStep::IntroduceAxiom { axiom_name } => Some(axiom_name.clone()),
            RuleStep::IntroduceTheorem { theorem_name } => Some(theorem_name.clone()),
            _ => None,
        })
        .collect();
    let payload = serde_json::json!({
        "worker_id": worker_id,
        "engine_git_sha": "beam",
        "lean_version": "4.27.0",
        "theorems": [{
            "canonical_statement": cand.expr.to_canonical(),
            "domain": "SpecialRelativity",
            "lean_source": lean_source,
            "chain": chain_json,
            "axioms_used": axioms_used,
            "depth": cand.chain.0.len() as u32,
            "generation": 0,
        }],
    });
    let client = reqwest::Client::new();
    let resp = client
        .post(format!("{api_url}/api/ingest"))
        .bearer_auth(worker_key)
        .json(&payload)
        .send()
        .await?;
    if !resp.status().is_success() {
        anyhow::bail!(
            "ingest http {}: {}",
            resp.status(),
            resp.text().await.unwrap_or_default()
        );
    }
    Ok(())
}
