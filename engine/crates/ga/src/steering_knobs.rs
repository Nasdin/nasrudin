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
pub fn apply_steering_knobs(cfg: &mut DiscoveryConfig, steering: &Value) -> bool {
    let knobs = steering
        .get("config")
        .and_then(|c| c.get("mutation_knobs"));
    let Some(knobs) = knobs else { return false };
    if knobs.is_null() {
        return false;
    }

    let mut applied = false;
    if let Some(rate) = knobs.get("rate").and_then(Value::as_f64) {
        let clamped = rate.clamp(0.05, 0.30);
        cfg.mutation_rate = clamped;
        applied = true;
    }
    if let Some(pop) = knobs.get("population_size").and_then(Value::as_u64) {
        let clamped = pop.clamp(32, 512) as usize;
        cfg.population_size = clamped;
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

    applied
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
}
