//! Apply LLM-emitted mutation knobs from a `SteeringConfig` to a
//! `DiscoveryConfig` in place.
//!
//! The schema is defined in `physics_api::steerer::schema::MutationKnobs`
//! but the GA crate doesn't depend on the API crate, so this module
//! reads the JSON shape directly. Bounds match the API-side validator
//! (rate ∈ [0.05, 0.30], population_size ∈ [32, 512], etc.) — values
//! outside the bounds are clamped, never used to shrink/expand wildly.
//!
//! When `mutation_knobs` is absent or null (mode B / first cycle /
//! no LLM running), the function is a no-op and the GA keeps its
//! existing config. This is the safety property the steerer relies
//! on: a missing or malformed steering payload never destabilises a
//! running worker.

use crate::chain_engine::DiscoveryConfig;
use serde_json::Value;

/// Read the `mutation_knobs` object from a `steering` JSON value (the
/// same shape `/api/seed` folds in) and patch the GA config.
///
/// Returns `true` if any field was applied — useful for logging the
/// effective config at chunk boundaries.
///
/// `domain_key` (e.g. `"special_relativity"`, `"electromagnetism"`)
/// scopes the per-domain LLM levers — currently the `atom_pool`. Pass
/// the empty string to skip the per-domain extraction (legacy callers
/// without a domain context).
pub fn apply_steering_knobs(cfg: &mut DiscoveryConfig, steering: &Value) -> bool {
    apply_steering_knobs_for_domain(cfg, steering, "")
}

/// Domain-aware variant of [`apply_steering_knobs`]. Threads through
/// the LLM-curated `atom_pool[domain]` so the GA's
/// `append_productive_suffix` mutation operator gets the right
/// physics-shape compounds for the island it's running on (SR atoms
/// for SR work, EM atoms for EM work, etc.).
///
/// `domain_key` must match the key the LLM emits under
/// `config.atom_pool` — typically the steerer's snake-case domain
/// name (e.g. `"special_relativity"`). Unknown keys silently
/// resolve to `None`, falling the GA back to its hardcoded baseline.
pub fn apply_steering_knobs_for_domain(
    cfg: &mut DiscoveryConfig,
    steering: &Value,
    domain_key: &str,
) -> bool {
    apply_steering_knobs_for_domain_with_strategy_weight(cfg, steering, domain_key, 1.0)
}

/// Domain-aware variant that lets the worker's local evaluator amplify
/// or dampen an LLM-emitted `strategy_genome_v1` policy without another
/// LLM call. A weight of 1.0 preserves the literal policy, <1.0 moves
/// macro-policy effects toward neutral, and >1.0 strengthens them.
pub fn apply_steering_knobs_for_domain_with_strategy_weight(
    cfg: &mut DiscoveryConfig,
    steering: &Value,
    domain_key: &str,
    strategy_weight: f64,
) -> bool {
    let mut applied = false;

    // mutation_knobs (population-level): nested object. Missing/null
    // is fine — leave cfg as-is. mutation_priors lives at config-level
    // and is handled separately below.
    let knobs = steering
        .get("config")
        .and_then(|c| c.get("mutation_knobs"))
        .filter(|v| !v.is_null());
    if let Some(knobs) = knobs {
        if let Some(rate) = knobs.get("rate").and_then(Value::as_f64) {
            cfg.mutation_rate = rate.clamp(0.05, 0.30);
            applied = true;
        }
        if let Some(pop) = knobs.get("population_size").and_then(Value::as_u64) {
            cfg.population_size = pop.clamp(32, 512) as usize;
            applied = true;
        }
        if let Some(bias) = knobs.get("suffix_bias").and_then(Value::as_f64) {
            cfg.suffix_bias = bias.clamp(0.0, 1.0) as f32;
            applied = true;
        }
        if let Some(elite) = knobs.get("elitism_fraction").and_then(Value::as_f64) {
            cfg.elitism_fraction = elite.clamp(0.0, 0.2) as f32;
            applied = true;
        }
    }

    // mutation_priors is a sibling of mutation_knobs (NOT nested) and
    // is read independently — the LLM may emit priors without knobs
    // (e.g. in scope=B where knobs are locked but per-operator bias
    // still helps). Each value clamped to [0.0, 2.0]; empty map →
    // leave cfg.mutation_priors as None so the GA's uniform fallback
    // kicks in.
    let priors = steering
        .get("config")
        .and_then(|c| c.get("mutation_priors"))
        .and_then(|p| p.as_object());
    if let Some(map) = priors {
        let mut h = std::collections::HashMap::new();
        for (k, v) in map {
            if let Some(f) = v.as_f64() {
                h.insert(k.clone(), f.clamp(0.0, 2.0) as f32);
            }
        }
        if !h.is_empty() {
            cfg.mutation_priors = Some(h);
            applied = true;
        }
    }

    // atom_pool is per-domain. The LLM emits a top-level
    // `{ "<domain>": [{name, weight}, ...] }` map and the worker
    // extracts only the slice for the island it's running on. Empty
    // / missing → leave cfg.atom_pool as None so the GA falls back
    // to its hardcoded baseline. Unknown atom names survive the
    // extraction (no validation here) — chain_ga drops them at the
    // sampler so forward-compat is preserved.
    if !domain_key.is_empty() {
        let pool_for_domain = steering
            .get("config")
            .and_then(|c| c.get("atom_pool"))
            .and_then(|p| p.as_object())
            .and_then(|m| m.get(domain_key))
            .and_then(|v| v.as_array());
        if let Some(arr) = pool_for_domain {
            let mut pool: Vec<(String, f32)> = Vec::with_capacity(arr.len());
            for entry in arr {
                let Some(name) = entry.get("name").and_then(Value::as_str) else {
                    continue;
                };
                let Some(w) = entry.get("weight").and_then(Value::as_f64) else {
                    continue;
                };
                if !w.is_finite() {
                    continue;
                }
                let w_c = w.clamp(0.0, 4.0) as f32;
                if w_c > 0.0 {
                    pool.push((name.to_string(), w_c));
                }
            }
            if !pool.is_empty() {
                cfg.atom_pool = Some(pool);
                applied = true;
            }
        }
    }

    // AlphaEvolve-style compact strategy genome. The LLM can spend a
    // few tokens on a domain policy that makes large worker-side moves;
    // the GA/RL evaluator then determines whether those moves survive.
    //
    // Shape:
    // {
    //   "config": {
    //     "extension": {
    //       "strategy_genome_v1": {
    //         "domain_policies": {
    //           "special_relativity": {
    //             "compute_scale": 1.5,
    //             "mutation_rate_mult": 1.1,
    //             "suffix_bias_delta": 0.2,
    //             "elitism_delta": 0.05,
    //             "operator_bias": {"append_productive_suffix": 1.6}
    //           }
    //         }
    //       }
    //     }
    //   }
    // }
    //
    // Scope B deliberately skips this block: paid-job runs require
    // stable compute accounting, so macro policies must wait for scope C.
    let scope = steering
        .get("config")
        .and_then(|c| c.get("scope"))
        .and_then(Value::as_str)
        .unwrap_or("C");
    if scope != "B" && !domain_key.is_empty() {
        let weight = strategy_weight.clamp(0.25, 1.75);
        if let Some(policy) = strategy_genome_policy(steering, domain_key) {
            if let Some(scale) = policy.get("compute_scale").and_then(Value::as_f64) {
                if scale.is_finite() {
                    let s = (1.0 + (scale.clamp(0.25, 4.0) - 1.0) * weight).clamp(0.25, 4.0);
                    cfg.population_size =
                        ((cfg.population_size as f64 * s).round()).clamp(32.0, 512.0) as usize;
                    cfg.generations =
                        ((cfg.generations as f64 * s).round()).clamp(1.0, 2000.0) as usize;
                    applied = true;
                }
            }
            if let Some(mult) = policy.get("mutation_rate_mult").and_then(Value::as_f64) {
                if mult.is_finite() {
                    let m = (1.0 + (mult.clamp(0.25, 4.0) - 1.0) * weight).clamp(0.25, 4.0);
                    cfg.mutation_rate = (cfg.mutation_rate * m).clamp(0.05, 0.30);
                    applied = true;
                }
            }
            if let Some(delta) = policy.get("suffix_bias_delta").and_then(Value::as_f64) {
                if delta.is_finite() {
                    cfg.suffix_bias = (cfg.suffix_bias + (delta.clamp(-1.0, 1.0) * weight) as f32)
                        .clamp(0.0, 1.0);
                    applied = true;
                }
            }
            if let Some(delta) = policy.get("elitism_delta").and_then(Value::as_f64) {
                if delta.is_finite() {
                    cfg.elitism_fraction = (cfg.elitism_fraction
                        + (delta.clamp(-0.2, 0.2) * weight) as f32)
                        .clamp(0.0, 0.2);
                    applied = true;
                }
            }
            if let Some(map) = policy.get("operator_bias").and_then(Value::as_object) {
                let priors = cfg
                    .mutation_priors
                    .get_or_insert_with(std::collections::HashMap::new);
                for (k, v) in map {
                    if let Some(f) = v.as_f64()
                        && f.is_finite()
                    {
                        let current = priors.get(k).copied().unwrap_or(1.0);
                        let bias = (1.0 + (f.clamp(0.0, 4.0) - 1.0) * weight).clamp(0.0, 4.0);
                        priors.insert(k.clone(), (current * bias as f32).clamp(0.0, 2.0));
                        applied = true;
                    }
                }
            }
        }
    }

    applied
}

fn strategy_genome_policy<'a>(steering: &'a Value, domain_key: &str) -> Option<&'a Value> {
    steering
        .get("config")
        .and_then(|c| c.get("extension"))
        .and_then(|e| e.get("strategy_genome_v1"))
        .and_then(|g| g.get("domain_policies"))
        .and_then(|p| p.as_object())
        .and_then(|m| m.get(domain_key))
}

/// Stable compact identifier for the active strategy genome policy in
/// this domain. Workers use this to attach local reward history to LLM
/// macro-policies without persisting the full prompt/response payload.
pub fn strategy_genome_fingerprint(steering: &Value, domain_key: &str) -> Option<String> {
    if domain_key.is_empty() {
        return None;
    }
    let scope = steering
        .get("config")
        .and_then(|c| c.get("scope"))
        .and_then(Value::as_str)
        .unwrap_or("C");
    if scope == "B" {
        return None;
    }
    let policy = strategy_genome_policy(steering, domain_key)?;
    let bytes = serde_json::to_vec(policy).ok()?;
    Some(format!("{:016x}", xxhash_rust::xxh64::xxh64(&bytes, 0)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain_engine::DiscoveryConfig;

    fn base() -> DiscoveryConfig {
        DiscoveryConfig::default()
    }

    #[test]
    fn no_mutation_knobs_is_noop() {
        let mut cfg = base();
        let original_rate = cfg.mutation_rate;
        let s = serde_json::json!({"config": {"scope": "C"}});
        assert!(!apply_steering_knobs(&mut cfg, &s));
        assert_eq!(cfg.mutation_rate, original_rate);
    }

    #[test]
    fn null_mutation_knobs_is_noop() {
        let mut cfg = base();
        let s = serde_json::json!({"config": {"scope": "B", "mutation_knobs": null}});
        assert!(!apply_steering_knobs(&mut cfg, &s));
    }

    #[test]
    fn applies_rate_and_pop_in_bounds() {
        let mut cfg = base();
        let s = serde_json::json!({
            "config": {
                "scope": "C",
                "mutation_knobs": {
                    "rate": 0.20,
                    "suffix_bias": 0.5,
                    "population_size": 128,
                    "elitism_fraction": 0.05
                }
            }
        });
        assert!(apply_steering_knobs(&mut cfg, &s));
        assert!((cfg.mutation_rate - 0.20).abs() < 1e-9);
        assert_eq!(cfg.population_size, 128);
    }

    #[test]
    fn clamps_out_of_range_rate() {
        let mut cfg = base();
        let s = serde_json::json!({
            "config": {
                "scope": "C",
                "mutation_knobs": { "rate": 0.99, "population_size": 9999 }
            }
        });
        apply_steering_knobs(&mut cfg, &s);
        assert!((cfg.mutation_rate - 0.30).abs() < 1e-9);
        assert_eq!(cfg.population_size, 512);
    }

    #[test]
    fn clamps_under_range_rate() {
        let mut cfg = base();
        let s = serde_json::json!({
            "config": {
                "mutation_knobs": { "rate": 0.001, "population_size": 1 }
            }
        });
        apply_steering_knobs(&mut cfg, &s);
        assert!((cfg.mutation_rate - 0.05).abs() < 1e-9);
        assert_eq!(cfg.population_size, 32);
    }

    #[test]
    fn applies_mutation_priors() {
        let mut cfg = base();
        let s = serde_json::json!({
            "config": {
                "scope": "C",
                "mutation_knobs": {
                    "rate": 0.10,
                    "suffix_bias": 0.0,
                    "population_size": 64,
                    "elitism_fraction": 0.05
                },
                "mutation_priors": {
                    "append_productive_suffix": 2.0,
                    "insert_random": 0.5
                }
            }
        });
        apply_steering_knobs(&mut cfg, &s);
        let priors = cfg.mutation_priors.as_ref().expect("priors should be set");
        assert!(
            (priors
                .get("append_productive_suffix")
                .copied()
                .unwrap_or(0.0)
                - 2.0)
                .abs()
                < 1e-6
        );
        assert!((priors.get("insert_random").copied().unwrap_or(0.0) - 0.5).abs() < 1e-6);
    }

    #[test]
    fn missing_mutation_priors_leaves_field_none() {
        let mut cfg = base();
        let s = serde_json::json!({"config": {"scope": "C", "mutation_knobs": null}});
        apply_steering_knobs(&mut cfg, &s);
        assert!(cfg.mutation_priors.is_none());
    }

    #[test]
    fn clamps_mutation_prior_above_two() {
        let mut cfg = base();
        let s = serde_json::json!({
            "config": {
                "mutation_priors": { "insert_random": 5.0 }
            }
        });
        apply_steering_knobs(&mut cfg, &s);
        let priors = cfg.mutation_priors.as_ref().unwrap();
        assert!((priors.get("insert_random").copied().unwrap_or(0.0) - 2.0).abs() < 1e-6);
    }

    #[test]
    fn atom_pool_extracted_for_matching_domain() {
        let mut cfg = base();
        let s = serde_json::json!({
            "config": {
                "atom_pool": {
                    "special_relativity": [
                        { "name": "m_c_sq", "weight": 2.0 },
                        { "name": "e_sq", "weight": 1.5 }
                    ],
                    "electromagnetism": [
                        { "name": "future_em_atom", "weight": 1.0 }
                    ]
                }
            }
        });
        assert!(apply_steering_knobs_for_domain(
            &mut cfg,
            &s,
            "special_relativity"
        ));
        let pool = cfg.atom_pool.as_ref().expect("pool should be set");
        assert_eq!(pool.len(), 2);
        assert_eq!(pool[0].0, "m_c_sq");
        assert!((pool[0].1 - 2.0).abs() < 1e-6);
    }

    #[test]
    fn atom_pool_no_matching_domain_leaves_field_unchanged() {
        let mut cfg = base();
        cfg.atom_pool = None;
        let s = serde_json::json!({
            "config": {
                "atom_pool": {
                    "special_relativity": [ { "name": "m_c_sq", "weight": 1.0 } ]
                }
            }
        });
        apply_steering_knobs_for_domain(&mut cfg, &s, "thermodynamics");
        assert!(cfg.atom_pool.is_none());
    }

    #[test]
    fn atom_pool_legacy_caller_skips_extraction() {
        let mut cfg = base();
        let s = serde_json::json!({
            "config": {
                "atom_pool": {
                    "special_relativity": [ { "name": "m_c_sq", "weight": 1.0 } ]
                }
            }
        });
        // Empty domain key → atom_pool extraction skipped. Existing
        // call sites that don't pass a domain continue to work
        // unchanged (no atom_pool overrides applied).
        apply_steering_knobs(&mut cfg, &s);
        assert!(cfg.atom_pool.is_none());
    }

    #[test]
    fn atom_pool_clamps_out_of_range_weight() {
        let mut cfg = base();
        let s = serde_json::json!({
            "config": {
                "atom_pool": {
                    "sr": [
                        { "name": "x", "weight": 99.0 },
                        { "name": "y", "weight": -1.0 }
                    ]
                }
            }
        });
        apply_steering_knobs_for_domain(&mut cfg, &s, "sr");
        let pool = cfg.atom_pool.as_ref().expect("clamped to 4.0; included");
        // weight=99 → clamps to 4.0 (kept); weight=-1 → clamps to 0 (dropped).
        assert_eq!(pool.len(), 1);
        assert_eq!(pool[0].0, "x");
        assert!((pool[0].1 - 4.0).abs() < 1e-6);
    }

    #[test]
    fn strategy_genome_applies_matching_domain_macro_policy() {
        let mut cfg = base();
        cfg.population_size = 64;
        cfg.generations = 10;
        cfg.mutation_rate = 0.10;
        let s = serde_json::json!({
            "config": {
                "scope": "C",
                "extension": {
                    "strategy_genome_v1": {
                        "domain_policies": {
                            "special_relativity": {
                                "compute_scale": 2.0,
                                "mutation_rate_mult": 2.0,
                                "suffix_bias_delta": 0.25,
                                "elitism_delta": 0.05,
                                "operator_bias": {
                                    "append_productive_suffix": 1.8
                                }
                            }
                        }
                    }
                }
            }
        });

        assert!(apply_steering_knobs_for_domain(
            &mut cfg,
            &s,
            "special_relativity"
        ));

        assert_eq!(cfg.population_size, 128);
        assert_eq!(cfg.generations, 20);
        assert!((cfg.mutation_rate - 0.20).abs() < 1e-9);
        assert!((cfg.suffix_bias - 0.25).abs() < 1e-6);
        assert!((cfg.elitism_fraction - 0.05).abs() < 1e-6);
        assert_eq!(
            cfg.mutation_priors
                .as_ref()
                .unwrap()
                .get("append_productive_suffix")
                .copied(),
            Some(1.8)
        );
    }

    #[test]
    fn strategy_genome_ignores_non_matching_domain() {
        let mut cfg = base();
        let original_pop = cfg.population_size;
        let s = serde_json::json!({
            "config": {
                "scope": "C",
                "extension": {
                    "strategy_genome_v1": {
                        "domain_policies": {
                            "quantum_mechanics": {"compute_scale": 3.0}
                        }
                    }
                }
            }
        });

        assert!(!apply_steering_knobs_for_domain(
            &mut cfg,
            &s,
            "special_relativity"
        ));
        assert_eq!(cfg.population_size, original_pop);
    }

    #[test]
    fn strategy_genome_skipped_in_scope_b() {
        let mut cfg = base();
        let original_pop = cfg.population_size;
        let s = serde_json::json!({
            "config": {
                "scope": "B",
                "extension": {
                    "strategy_genome_v1": {
                        "domain_policies": {
                            "special_relativity": {"compute_scale": 3.0}
                        }
                    }
                }
            }
        });

        assert!(!apply_steering_knobs_for_domain(
            &mut cfg,
            &s,
            "special_relativity"
        ));
        assert_eq!(cfg.population_size, original_pop);
    }

    #[test]
    fn strategy_genome_weight_dampens_macro_policy_toward_neutral() {
        let mut cfg = base();
        cfg.population_size = 64;
        cfg.generations = 10;
        cfg.mutation_rate = 0.10;
        let s = serde_json::json!({
            "config": {
                "scope": "C",
                "extension": {
                    "strategy_genome_v1": {
                        "domain_policies": {
                            "special_relativity": {
                                "compute_scale": 2.0,
                                "mutation_rate_mult": 2.0,
                                "operator_bias": {
                                    "append_productive_suffix": 1.8
                                }
                            }
                        }
                    }
                }
            }
        });

        assert!(apply_steering_knobs_for_domain_with_strategy_weight(
            &mut cfg,
            &s,
            "special_relativity",
            0.5
        ));

        assert_eq!(cfg.population_size, 96);
        assert_eq!(cfg.generations, 15);
        assert!((cfg.mutation_rate - 0.15).abs() < 1e-9);
        assert_eq!(
            cfg.mutation_priors
                .as_ref()
                .unwrap()
                .get("append_productive_suffix")
                .copied(),
            Some(1.4)
        );
    }

    #[test]
    fn strategy_genome_fingerprint_is_stable_and_domain_scoped() {
        let s = serde_json::json!({
            "config": {
                "scope": "C",
                "extension": {
                    "strategy_genome_v1": {
                        "domain_policies": {
                            "special_relativity": {"compute_scale": 2.0},
                            "quantum_mechanics": {"compute_scale": 1.5}
                        }
                    }
                }
            }
        });

        let sr1 = strategy_genome_fingerprint(&s, "special_relativity").unwrap();
        let sr2 = strategy_genome_fingerprint(&s, "special_relativity").unwrap();
        let qm = strategy_genome_fingerprint(&s, "quantum_mechanics").unwrap();

        assert_eq!(sr1, sr2);
        assert_ne!(sr1, qm);
        assert_eq!(strategy_genome_fingerprint(&s, "thermodynamics"), None);
    }

    #[test]
    fn strategy_genome_fingerprint_skips_scope_b() {
        let s = serde_json::json!({
            "config": {
                "scope": "B",
                "extension": {
                    "strategy_genome_v1": {
                        "domain_policies": {
                            "special_relativity": {"compute_scale": 2.0}
                        }
                    }
                }
            }
        });

        assert_eq!(strategy_genome_fingerprint(&s, "special_relativity"), None);
    }
}
