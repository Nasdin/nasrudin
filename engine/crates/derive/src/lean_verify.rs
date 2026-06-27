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
    Failed { stderr: String },
    /// `lake build` could not be executed.
    ProcessError { message: String },
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
        self.run_lake_build(module_path, lean_content)
    }

    /// Run `lake build` for a specific module.
    fn run_lake_build(&self, module_path: &str, lean_content: &str) -> LeanVerifyResult {
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
                    let stderr = combined_output(&output);
                    if stderr.contains("ProofWidgets not up-to-date")
                        || stderr.contains("no such file or directory")
                    {
                        return self.run_direct_lean(module_path, Some(lean_content));
                    }
                    LeanVerifyResult::Failed { stderr }
                }
            }
            Err(e) => LeanVerifyResult::ProcessError {
                message: format!("failed to run `lake build`: {e}"),
            },
        }
    }

    /// Elaborate the generated module directly with Lean. This avoids
    /// Lake package targets that are unrelated to kernel-checking the
    /// generated proof, notably ProofWidgets' JS bundle.
    fn run_direct_lean(&self, module_path: &str, lean_content: Option<&str>) -> LeanVerifyResult {
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

        let relative_path = module_path.replace('.', "/") + ".lean";
        if let Some(content) = lean_content {
            let file_path = self.prover_root.join(&relative_path);
            if let Some(parent) = file_path.parent()
                && let Err(e) = std::fs::create_dir_all(parent)
            {
                return LeanVerifyResult::ProcessError {
                    message: format!("failed to create direct-lean source dir: {e}"),
                };
            }
            if let Err(e) = std::fs::write(&file_path, content) {
                return LeanVerifyResult::ProcessError {
                    message: format!("failed to rewrite direct-lean source: {e}"),
                };
            }
        }
        let foundation_modules = [
            (
                "PhysicsGenerator/LeafImports.lean",
                "PhysicsGenerator/LeafImports.olean",
            ),
            (
                "PhysicsGenerator/Basic.lean",
                "PhysicsGenerator/Basic.olean",
            ),
        ];
        for (src, out) in foundation_modules {
            let out_path = self.prover_root.join(".lake/build/lib/lean").join(out);
            if let Some(parent) = out_path.parent()
                && let Err(e) = std::fs::create_dir_all(parent)
            {
                return LeanVerifyResult::ProcessError {
                    message: format!("failed to create direct-lean output dir: {e}"),
                };
            }
            let output = Command::new(&lake_bin)
                .arg("env")
                .arg("lean")
                .arg("-R")
                .arg(".")
                .arg("-o")
                .arg(&out_path)
                .arg(src)
                .current_dir(&self.prover_root)
                .output();
            match output {
                Ok(o) if o.status.success() => {}
                Ok(o) => {
                    return LeanVerifyResult::Failed {
                        stderr: combined_output(&o),
                    };
                }
                Err(e) => {
                    return LeanVerifyResult::ProcessError {
                        message: format!("failed to run direct lean for {src}: {e}"),
                    };
                }
            }
        }

        let output = Command::new(&lake_bin)
            .arg("env")
            .arg("lean")
            .arg("-R")
            .arg(".")
            .arg(relative_path)
            .current_dir(&self.prover_root)
            .output();
        match output {
            Ok(o) if o.status.success() => LeanVerifyResult::Success,
            Ok(o) => LeanVerifyResult::Failed {
                stderr: combined_output(&o),
            },
            Err(e) => LeanVerifyResult::ProcessError {
                message: format!("failed to run direct lean: {e}"),
            },
        }
    }
}

fn combined_output(output: &std::process::Output) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    if stdout.is_empty() {
        stderr.to_string()
    } else if stderr.is_empty() {
        stdout.to_string()
    } else {
        format!("{stdout}\n{stderr}")
    }
}

/// Borrowed bundle of identity + caches passed to [`verify_with_cache`].
///
/// Holding all of these on one struct keeps the call site tidy at every
/// production verification path. All fields are borrowed for the
/// duration of the call — caller owns the [`AttemptsCache`] and
/// [`LeanVerifier`].
pub struct VerifyWithCacheCtx<'a> {
    pub verifier: &'a LeanVerifier,
    pub cache: &'a AttemptsCache,
    pub cache_key: &'a [u8; 16],
    pub lean_version: &'a str,
    pub worker_id: &'a str,
    /// How many days a cached outcome is considered fresh. Records older
    /// than this are treated as cache misses.
    pub ttl_days: i64,
}

/// Cache-backed wrapper around [`LeanVerifier::verify_file`].
///
/// On cache hit (within `ttl_days`), returns the cached outcome
/// translated back to a [`LeanVerifyResult`]. On miss, calls the
/// underlying verifier, caches the outcome (skipping `ProcessError` —
/// transient), and returns the verifier's original result.
///
/// `ctx.cache_key` should be `AttemptsCache::make_key(canonical_hash, axiom_set_hash)`
/// computed by the caller — the verifier doesn't know what axioms are
/// in scope.
///
/// **Note**: when a cached `Verified` outcome is returned, the
/// underlying `theorem_id` field is filled with zeros (we don't know
/// it at this layer). Callers that need the canonical hash of the
/// verified theorem must recompute it from the source.
pub fn verify_with_cache(
    ctx: &VerifyWithCacheCtx<'_>,
    lean_content: &str,
    module_path: &str,
) -> LeanVerifyResult {
    let max_age = Duration::days(ctx.ttl_days);

    // Cache hit fast-path: if there's a fresh record, translate it back.
    match ctx.cache.get_with_ttl(ctx.cache_key, max_age) {
        Ok(Some(record)) => {
            return match record.outcome {
                AttemptOutcome::Verified { .. } => LeanVerifyResult::Success,
                AttemptOutcome::RejectedTypeError { msg } => {
                    if is_transient_verifier_failure(&msg) {
                        ctx.verifier.verify_file(lean_content, module_path)
                    } else {
                        LeanVerifyResult::Failed { stderr: msg }
                    }
                }
                AttemptOutcome::RejectedTimeout => LeanVerifyResult::Failed {
                    stderr: "timeout".into(),
                },
                AttemptOutcome::RejectedTrivial { reason } => {
                    LeanVerifyResult::Failed { stderr: reason }
                }
                AttemptOutcome::Pending => {
                    // Pending records are written by other code paths
                    // (lease-TTL mid-attempt). Treat as a cache miss and
                    // re-run the verifier without persisting.
                    ctx.verifier.verify_file(lean_content, module_path)
                }
            };
        }
        Ok(None) => {}
        Err(e) => {
            tracing::warn!("attempts cache get failed: {e}");
            return ctx.verifier.verify_file(lean_content, module_path);
        }
    }

    let started = std::time::Instant::now();
    let raw = ctx.verifier.verify_file(lean_content, module_path);
    let elapsed_ms = u32::try_from(started.elapsed().as_millis()).unwrap_or(u32::MAX);

    let outcome = match &raw {
        LeanVerifyResult::Success => AttemptOutcome::Verified {
            theorem_id: [0u8; 8],
            tactic: String::new(),
        },
        LeanVerifyResult::Failed { stderr } if is_transient_verifier_failure(stderr) => {
            return raw;
        }
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
        lean_version: ctx.lean_version.to_string(),
        timestamp: chrono::Utc::now(),
        attempted_by: ctx.worker_id.to_string(),
        elapsed_ms,
    };
    if let Err(e) = ctx.cache.put(ctx.cache_key, &record) {
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

fn is_transient_verifier_failure(stderr: &str) -> bool {
    stderr.contains("ProofWidgets not up-to-date") || stderr.contains("no such file or directory")
}

#[cfg(test)]
mod ctx_tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn verify_with_cache_ctx_constructs_with_borrowed_fields() {
        let dir = tempdir().unwrap();
        let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
        let key = [0u8; 16];
        let verifier = LeanVerifier::new("/nonexistent");
        let ctx = VerifyWithCacheCtx {
            verifier: &verifier,
            cache: &cache,
            cache_key: &key,
            lean_version: "4.27.0",
            worker_id: "ctx-test",
            ttl_days: 30,
        };
        assert_eq!(ctx.lean_version, "4.27.0");
        assert_eq!(ctx.ttl_days, 30);
    }

    #[test]
    fn process_error_is_not_cached() {
        // Verifier pointing at /nonexistent → ProcessError. Cache must
        // stay empty after the call (transient errors don't persist).
        let dir = tempdir().unwrap();
        let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
        let key = [0xef; 16];
        let verifier = LeanVerifier::new("/nonexistent");
        let ctx = VerifyWithCacheCtx {
            verifier: &verifier,
            cache: &cache,
            cache_key: &key,
            lean_version: "4.27.0",
            worker_id: "test",
            ttl_days: 30,
        };
        let _ = verify_with_cache(&ctx, "stub source", "Stub.Module");
        assert!(
            cache.get(&key).unwrap().is_none(),
            "ProcessError must not be cached"
        );
    }
}
