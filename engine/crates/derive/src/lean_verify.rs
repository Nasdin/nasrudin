//! Process-based Lean4 verification.
//!
//! Writes a `.lean` file and runs `lake build` to verify the proof.
//! Upgradeable to FFI-based verification later.

use chrono::Duration;
use nasrudin_rocks::attempts_cache::{AttemptOutcome, AttemptRecord, AttemptsCache};
use std::path::PathBuf;
use std::process::Command;

/// Result of a Lean4 verification attempt.
#[derive(Debug, Clone)]
pub enum LeanVerifyResult {
    /// Lean4 accepted the proof.
    Success,
    /// Lean4 rejected the proof.
    Failed {
        stderr: String,
    },
    /// `lake build` could not be executed.
    ProcessError {
        message: String,
    },
}

/// Lean4 verifier that runs proofs through `lake build`.
#[derive(Debug, Clone)]
pub struct LeanVerifier {
    /// Path to the Lean4 prover project root (where `lakefile.lean` lives).
    pub prover_root: PathBuf,
}

impl LeanVerifier {
    pub fn new(prover_root: impl Into<PathBuf>) -> Self {
        Self {
            prover_root: prover_root.into(),
        }
    }

    /// Write a `.lean` file and verify it via `lake build`.
    pub fn verify_file(&self, lean_content: &str, module_path: &str) -> LeanVerifyResult {
        // Convert module path to file path (e.g., "PhysicsGenerator.Derived.RestEnergy"
        // → "PhysicsGenerator/Derived/RestEnergy.lean")
        let relative_path = module_path.replace('.', "/") + ".lean";
        let file_path = self.prover_root.join(&relative_path);

        // Ensure parent directory exists
        if let Some(parent) = file_path.parent() {
            if let Err(e) = std::fs::create_dir_all(parent) {
                return LeanVerifyResult::ProcessError {
                    message: format!("failed to create directory: {e}"),
                };
            }
        }

        // Write the Lean file
        if let Err(e) = std::fs::write(&file_path, lean_content) {
            return LeanVerifyResult::ProcessError {
                message: format!("failed to write file: {e}"),
            };
        }

        // Run `lake build <module>`
        self.run_lake_build(module_path)
    }

    /// Run `lake build` for a specific module.
    fn run_lake_build(&self, module_path: &str) -> LeanVerifyResult {
        // Resolve lake binary: prefer ~/.elan/bin/lake, fall back to PATH
        let lake_bin = std::env::var("HOME")
            .ok()
            .map(|home| {
                let elan_lake = PathBuf::from(&home).join(".elan/bin/lake");
                if elan_lake.exists() {
                    elan_lake
                } else {
                    PathBuf::from("lake")
                }
            })
            .unwrap_or_else(|| PathBuf::from("lake"));

        // Ensure elan bin is on PATH for child processes (lean, leanc, etc.)
        let path_env = {
            let current = std::env::var("PATH").unwrap_or_default();
            if let Some(home) = std::env::var("HOME").ok() {
                let elan_bin = format!("{home}/.elan/bin");
                if !current.contains(&elan_bin) {
                    format!("{elan_bin}:{current}")
                } else {
                    current
                }
            } else {
                current
            }
        };

        let result = Command::new(&lake_bin)
            .arg("build")
            .arg(module_path)
            .current_dir(&self.prover_root)
            .env("PATH", &path_env)
            .output();

        match result {
            Ok(output) => {
                if output.status.success() {
                    LeanVerifyResult::Success
                } else {
                    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
                    LeanVerifyResult::Failed { stderr }
                }
            }
            Err(e) => LeanVerifyResult::ProcessError {
                message: format!("failed to run `lake build`: {e}"),
            },
        }
    }
}

/// Cache-backed wrapper around [`LeanVerifier::verify_file`].
///
/// On cache hit (within TTL), returns the cached outcome translated back
/// to a [`LeanVerifyResult`]. On miss, calls the underlying verifier,
/// caches the outcome, and returns the verifier's original result.
///
/// `cache_key` should be `AttemptsCache::make_key(canonical_hash, axiom_set_hash)`
/// computed by the caller — the verifier doesn't know what axioms are in scope.
///
/// `ttl_days` controls how long a cached outcome is considered fresh. Records
/// older than this are treated as cache misses (the underlying verifier runs
/// again and overwrites the row).
///
/// **Note**: when a cached `Verified` outcome is returned, the underlying
/// `theorem_id` field is filled with zeros (we don't know it at this layer).
/// Callers that need the canonical hash of the verified theorem must
/// recompute it from the source.
pub fn verify_with_cache(
    verifier: &LeanVerifier,
    cache: &AttemptsCache,
    cache_key: &[u8; 16],
    lean_version: &str,
    worker_id: &str,
    lean_content: &str,
    module_path: &str,
    ttl_days: i64,
) -> LeanVerifyResult {
    let max_age = Duration::days(ttl_days);

    // Cache hit fast-path: if there's a fresh record, translate it back.
    match cache.get_with_ttl(cache_key, max_age) {
        Ok(Some(record)) => {
            return match record.outcome {
                AttemptOutcome::Verified { .. } => LeanVerifyResult::Success,
                AttemptOutcome::RejectedTypeError { msg } => {
                    LeanVerifyResult::Failed { stderr: msg }
                }
                AttemptOutcome::RejectedTimeout => LeanVerifyResult::Failed {
                    stderr: "timeout".into(),
                },
                AttemptOutcome::RejectedTrivial { reason } => {
                    LeanVerifyResult::Failed { stderr: reason }
                }
                AttemptOutcome::Pending => {
                    // Pending records are written by other code paths (lease-TTL
                    // mid-attempt). Treat as a cache miss and re-run the verifier
                    // without persisting (Phase A.5 will own the lease semantics).
                    verifier.verify_file(lean_content, module_path)
                }
            };
        }
        Ok(None) => {} // miss — fall through and run the verifier
        Err(e) => {
            // Cache read failure is not a verification result; log and run
            // the verifier directly without trying to persist.
            tracing::warn!("attempts cache get failed: {e}");
            return verifier.verify_file(lean_content, module_path);
        }
    }

    // Miss: run the verifier.
    let started = std::time::Instant::now();
    let raw = verifier.verify_file(lean_content, module_path);
    let elapsed_ms = u32::try_from(started.elapsed().as_millis()).unwrap_or(u32::MAX);

    // Map the result to a cacheable outcome — but ONLY if it's a stable
    // signal. Process errors are transient (different machine might
    // succeed) so we skip the cache write and return the raw result.
    let outcome = match &raw {
        LeanVerifyResult::Success => AttemptOutcome::Verified {
            theorem_id: [0u8; 8],
            tactic: String::new(),
        },
        LeanVerifyResult::Failed { stderr } => AttemptOutcome::RejectedTypeError {
            msg: truncate(stderr, 256),
        },
        LeanVerifyResult::ProcessError { .. } => {
            // Transient — do not persist.
            return raw;
        }
    };

    let record = AttemptRecord {
        outcome,
        lean_version: lean_version.to_string(),
        timestamp: chrono::Utc::now(),
        attempted_by: worker_id.to_string(),
        elapsed_ms,
    };
    if let Err(e) = cache.put(cache_key, &record) {
        tracing::warn!("attempts cache put failed: {e}");
    }
    raw
}

fn truncate(s: &str, n: usize) -> String {
    if n == 0 {
        return String::new();
    }
    if s.len() <= n {
        s.to_string()
    } else {
        // Truncate at character boundary — find the last char boundary at-or-before `n`.
        let mut idx = n;
        while idx > 0 && !s.is_char_boundary(idx) {
            idx -= 1;
        }
        format!("{}…", &s[..idx])
    }
}
