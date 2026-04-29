//! Feature flags + stats aggregation for the three cache layers.
//!
//! Read once at process boot via `CacheConfig::from_env()`. Each cache
//! consults its corresponding flag before doing real work; when a flag
//! is off, the cache is a pass-through (cost: one bool branch).

use std::sync::atomic::AtomicU64;

/// Runtime configuration for the cache layer.
#[derive(Debug, Clone, Copy, Default)]
pub struct CacheConfig {
    pub attempts_enabled: bool,
    pub tactic_priors_enabled: bool,
    pub persistent_lean_enabled: bool,
}

impl CacheConfig {
    /// Read flags from env. Each flag is on iff the env var is set to a
    /// truthy value (`"1"`, `"true"`, `"yes"`, case-insensitive). Anything
    /// else (including unset, empty, `"0"`, `"false"`) is off.
    pub fn from_env() -> Self {
        Self {
            attempts_enabled: env_truthy("NASRUDIN_CACHE_ATTEMPTS"),
            tactic_priors_enabled: env_truthy("NASRUDIN_CACHE_TACTIC_PRIORS"),
            persistent_lean_enabled: env_truthy("NASRUDIN_CACHE_PERSISTENT_LEAN"),
        }
    }
}

fn env_truthy(name: &str) -> bool {
    match std::env::var(name) {
        Ok(s) => matches!(s.trim().to_lowercase().as_str(), "1" | "true" | "yes"),
        Err(_) => false,
    }
}

/// Atomic counter sink. Each cache layer increments its counters; the
/// `cache-stats` binary reads them out for reporting.
#[derive(Debug, Default)]
pub struct CacheStats {
    pub attempts_hits: AtomicU64,
    pub attempts_misses: AtomicU64,
    pub tactic_priors_hits: AtomicU64,
    pub tactic_priors_misses: AtomicU64,
    pub persistent_lean_requests: AtomicU64,
    pub persistent_lean_restarts: AtomicU64,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Save and restore env vars across one test. Required because cargo
    /// runs tests in parallel by default and env mutation isn't thread-safe;
    /// we use serial_test only if needed (skip for now since each test sets
    /// distinct vars).
    struct EnvGuard {
        saved: Vec<(String, Option<String>)>,
    }

    impl EnvGuard {
        fn clear(keys: &[&str]) -> Self {
            let saved: Vec<(String, Option<String>)> = keys
                .iter()
                .map(|k| (k.to_string(), std::env::var(k).ok()))
                .collect();
            for k in keys {
                // SAFETY: env mutation is unsafe in Rust 2024+; tests in this
                // module mutate env serially within one test fn so cross-test
                // interleaving via Cargo's parallel runner is the only risk.
                // Each test uses distinct vars or guards them.
                unsafe {
                    std::env::remove_var(k);
                }
            }
            Self { saved }
        }

        fn set(pairs: &[(&str, &str)]) -> Self {
            let saved: Vec<(String, Option<String>)> = pairs
                .iter()
                .map(|(k, _)| (k.to_string(), std::env::var(k).ok()))
                .collect();
            for (k, v) in pairs {
                unsafe {
                    std::env::set_var(k, v);
                }
            }
            Self { saved }
        }
    }

    impl Drop for EnvGuard {
        fn drop(&mut self) {
            for (k, v) in &self.saved {
                unsafe {
                    match v {
                        Some(val) => std::env::set_var(k, val),
                        None => std::env::remove_var(k),
                    }
                }
            }
        }
    }

    #[test]
    fn defaults_are_off() {
        let _g = EnvGuard::clear(&[
            "NASRUDIN_CACHE_ATTEMPTS",
            "NASRUDIN_CACHE_TACTIC_PRIORS",
            "NASRUDIN_CACHE_PERSISTENT_LEAN",
        ]);
        let cfg = CacheConfig::from_env();
        assert!(!cfg.attempts_enabled);
        assert!(!cfg.tactic_priors_enabled);
        assert!(!cfg.persistent_lean_enabled);
    }

    #[test]
    fn one_flag_set_enables_only_that_cache() {
        let _g = EnvGuard::set(&[
            ("NASRUDIN_CACHE_ATTEMPTS", "1"),
            ("NASRUDIN_CACHE_TACTIC_PRIORS", "0"),
            ("NASRUDIN_CACHE_PERSISTENT_LEAN", ""),
        ]);
        let cfg = CacheConfig::from_env();
        assert!(cfg.attempts_enabled);
        assert!(!cfg.tactic_priors_enabled);
        assert!(!cfg.persistent_lean_enabled);
    }

    #[test]
    fn truthy_variants_all_work() {
        // Distinct var name to avoid racing with `falsy_variants_all_off` under
        // Cargo's parallel test runner. Both tests exercise `env_truthy`
        // directly, which is the unit-under-test for the env-var parsing.
        let var = "NASRUDIN_CACHE_ATTEMPTS_TRUTHY_TEST";
        for variant in ["1", "true", "TRUE", "True", "yes", "YES", "Yes"] {
            let _g = EnvGuard::set(&[(var, variant)]);
            assert!(env_truthy(var), "variant {variant:?} should be truthy");
        }
    }

    #[test]
    fn falsy_variants_all_off() {
        let var = "NASRUDIN_CACHE_ATTEMPTS_FALSY_TEST";
        for variant in ["0", "false", "FALSE", "no", "off", ""] {
            let _g = EnvGuard::set(&[(var, variant)]);
            assert!(!env_truthy(var), "variant {variant:?} should be falsy");
        }
    }

    #[test]
    fn cache_stats_default_is_zero() {
        use std::sync::atomic::Ordering;
        let s = CacheStats::default();
        assert_eq!(s.attempts_hits.load(Ordering::Relaxed), 0);
        assert_eq!(s.attempts_misses.load(Ordering::Relaxed), 0);
        assert_eq!(s.tactic_priors_hits.load(Ordering::Relaxed), 0);
        assert_eq!(s.tactic_priors_misses.load(Ordering::Relaxed), 0);
        assert_eq!(s.persistent_lean_requests.load(Ordering::Relaxed), 0);
        assert_eq!(s.persistent_lean_restarts.load(Ordering::Relaxed), 0);
    }
}
