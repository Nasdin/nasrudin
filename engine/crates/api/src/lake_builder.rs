//! Lake builder + axiom/sorry pre-flight.
//!
//! Provides the `LakeBuilder` task pool that runs `lake build` in tmpdir copies
//! of the `prover/` template, plus a free function `preflight_axiom_or_sorry`
//! which is the firewall against hostile-worker submissions: it rejects any
//! Lean source that declares a fresh `axiom` or contains a `sorry` placeholder.
//!
//! Pre-flight runs *before* `lake build`. Together they constitute the B-path
//! "double verification": pre-flight strips fake-via-axiom proofs, then
//! `lake build` checks the real Lean kernel succeeds on the trusted prover
//! template.
use std::path::PathBuf;
use std::process::Stdio;
use std::sync::{Arc, LazyLock};
use std::time::Duration;

use anyhow::{Context, Result};
use chrono::Duration as ChronoDuration;
use nasrudin_rocks::{AttemptOutcome, AttemptRecord, AttemptsCache};
use tokio::process::Command;
use tokio::sync::Semaphore;

const VERIFY_TIMEOUT: Duration = Duration::from_secs(300);

static AXIOM_RE: LazyLock<regex::Regex> =
    LazyLock::new(|| regex::Regex::new(r"(?m)^\s*axiom\s+\w+").expect("static regex compiles"));

static SORRY_RE: LazyLock<regex::Regex> =
    LazyLock::new(|| regex::Regex::new(r"\bsorry\b").expect("static regex compiles"));

/// Outcome of a single verification attempt.
#[derive(Debug, Clone)]
pub enum VerifyOutcome {
    Verified { tactic: String, duration_ms: u32 },
    Rejected { reason: String, stderr_tail: String },
}

/// Tokio task pool that runs `lake build` against the trusted `prover/`
/// directory directly, sharing the persistent `.lake/build/` cache across
/// every verification. Each verification writes a uniquely-named submission
/// file (`PhysicsGenerator/Derived/Submission_<theorem_id_hex>.lean`),
/// runs `lake build` (which only re-elaborates the new submission against
/// the already-cached PhysicsGenerator + Mathlib oleans), and cleans up
/// the source + olean afterwards.
///
/// The previous design copied the entire prover tree into a tmpdir per
/// verification, which forced lake to re-load 7,500+ Mathlib oleans into
/// elaborator scope each time. Direct-mode reuses the warm cache, cutting
/// per-verification cost from ~60s to ~5s (and far less with the
/// `LeafImports` module — Task 2).
///
/// `workspace_root` is preserved as a field for backwards compat with
/// callers that pass it; it's no longer used.
pub struct LakeBuilder {
    /// Prover root directory — the actual `prover/` tree, not a copy.
    prover_template: PathBuf,
    #[allow(dead_code)]
    workspace_root: PathBuf,
    semaphore: Arc<Semaphore>,
}

impl LakeBuilder {
    pub fn new(prover_template: PathBuf, workspace_root: PathBuf, slots: usize) -> Self {
        Self {
            prover_template,
            workspace_root,
            semaphore: Arc::new(Semaphore::new(slots.max(1))),
        }
    }

    /// One-shot warmup: run `lake build PhysicsGenerator` against the
    /// prover tree at API boot to ensure all base oleans (PhysicsGenerator
    /// + LeafImports + transitive Mathlib) are populated before workers
    /// start hitting verify(). Idempotent — if the cache is already warm,
    /// lake exits in seconds.
    ///
    /// Errors are logged but non-fatal: if `lake` isn't on PATH the API
    /// boots anyway and individual verifications fall back to per-call
    /// build. Callers should `tokio::spawn` this so it doesn't block boot.
    pub async fn warmup(&self) -> Result<()> {
        let prover_root = self.prover_template.clone();
        let join = tokio::task::spawn_blocking(move || -> Result<std::process::Output> {
            std::process::Command::new("lake")
                .arg("build")
                .arg("PhysicsGenerator")
                .current_dir(&prover_root)
                .output()
                .context("lake warmup spawn")
        })
        .await
        .context("spawn_blocking join error")??;

        if !join.status.success() {
            tracing::warn!(
                "lake warmup non-zero exit ({}): {}",
                join.status,
                String::from_utf8_lossy(&join.stderr)
            );
        } else {
            tracing::info!("lake warmup complete (PhysicsGenerator oleans cached)");
        }
        Ok(())
    }

    /// Pre-flight checks (`axiom` / `sorry`), then runs `lake build` against
    /// the prover tree with the submission written directly to
    /// `prover/PhysicsGenerator/Derived/Submission_<theorem_id_hex>.lean`.
    /// The submission file is removed after verification regardless of
    /// outcome (the `.olean` artifact lingers in `.lake/build/` — cheap
    /// disk, helpful if the same chain ever re-verifies).
    pub async fn verify(&self, lean_source: &str, theorem_id_hex: &str) -> Result<VerifyOutcome> {
        // 1. Pre-flight first — reject before we even allocate a slot.
        if let Err(reason) = preflight_axiom_or_sorry(lean_source) {
            return Ok(VerifyOutcome::Rejected {
                reason: reason.to_string(),
                stderr_tail: String::new(),
            });
        }

        // 2. Acquire a permit (caps concurrent lake-build invocations).
        // Lake serialises internally on `.lake/lock` for cross-process
        // builds against the same project, so concurrent verify() calls
        // are safe but may queue at the lake-manifest level. Permit count
        // is the user-tunable parallelism.
        let _permit = self
            .semaphore
            .acquire()
            .await
            .context("lake-builder semaphore closed")?;

        // 3. Write the submission file directly into the prover tree. The
        // submission filename is namespaced by theorem_id_hex so concurrent
        // verifications don't collide. We delete the .lean source after
        // the build completes (success or failure) so the prover tree
        // doesn't accumulate stale Submission_*.lean files.
        let prover_root = self.prover_template.clone();
        let lean_source = lean_source.to_string();
        let theorem_id_hex = theorem_id_hex.to_string();
        let submission_relative =
            format!("PhysicsGenerator/Derived/Submission_{theorem_id_hex}.lean");
        let submission_path = prover_root.join(&submission_relative);

        let write_result = {
            let submission_path = submission_path.clone();
            tokio::task::spawn_blocking(move || -> Result<()> {
                if let Some(parent) = submission_path.parent() {
                    std::fs::create_dir_all(parent).ok();
                }
                std::fs::write(&submission_path, lean_source.as_bytes())
                    .context("write submission lean source")
            })
            .await
            .context("spawn_blocking join error")?
        };

        if let Err(e) = write_result {
            return Ok(VerifyOutcome::Rejected {
                reason: "toolchain_error".into(),
                stderr_tail: e.to_string(),
            });
        }

        // 4. RAII guard: ensure the submission .lean file is removed even
        // on early return / panic.
        let _cleanup = SubmissionCleanup {
            path: submission_path.clone(),
            theorem_id_hex: theorem_id_hex.clone(),
            prover_root: prover_root.clone(),
        };

        // 5. Run `lake build <Module>` with a 300s wall-clock timeout.
        // Targeting the specific module (not bare `lake build`) tells lake
        // to only build this one submission + its transitive deps; the
        // prebuilt PhysicsGenerator.LeafImports oleans satisfy the deps.
        let module_target = format!("PhysicsGenerator.Derived.Submission_{theorem_id_hex}");
        let start = std::time::Instant::now();
        let mut cmd = Command::new("lake");
        cmd.arg("build")
            .arg(&module_target)
            .current_dir(&prover_root)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let mut child = match cmd.spawn() {
            Ok(c) => c,
            Err(e) => {
                return Ok(VerifyOutcome::Rejected {
                    reason: "toolchain_error".into(),
                    stderr_tail: e.to_string(),
                });
            }
        };

        let wait_result = tokio::time::timeout(VERIFY_TIMEOUT, child.wait()).await;
        let duration_ms = start.elapsed().as_millis().min(u32::MAX as u128) as u32;

        match wait_result {
            Err(_) => {
                // Timed out — kill the subprocess so it doesn't leak RAM/CPU.
                let _ = child.start_kill();
                // Reap so we don't leave a zombie. Bound the wait at 5s.
                let _ = tokio::time::timeout(Duration::from_secs(5), child.wait()).await;
                Ok(VerifyOutcome::Rejected {
                    reason: "verify_timeout".into(),
                    stderr_tail: String::new(),
                })
            }
            Ok(Err(e)) => Ok(VerifyOutcome::Rejected {
                reason: "toolchain_error".into(),
                stderr_tail: e.to_string(),
            }),
            Ok(Ok(status)) => {
                // Read stderr after process exit (for tail / failure path).
                let mut stderr_buf = Vec::new();
                if let Some(mut stderr) = child.stderr.take() {
                    use tokio::io::AsyncReadExt;
                    let _ = stderr.read_to_end(&mut stderr_buf).await;
                }
                if status.success() {
                    Ok(VerifyOutcome::Verified {
                        tactic: "lake_build".to_string(),
                        duration_ms,
                    })
                } else {
                    let stderr_str = String::from_utf8_lossy(&stderr_buf);
                    Ok(VerifyOutcome::Rejected {
                        reason: "lake_build_failed".into(),
                        stderr_tail: tail_lines(&stderr_str, 20),
                    })
                }
            }
        }
    }

    /// Cache-backed wrapper around [`Self::verify`]. On hit (within
    /// `ttl_days`), returns the cached outcome without invoking
    /// `lake build`. On miss, runs `verify` and writes the outcome.
    /// Errors from `verify` (transient process failures) bubble up
    /// without persistence.
    pub async fn verify_cached(
        &self,
        cache: &AttemptsCache,
        cache_key: &[u8; 16],
        lean_version: &str,
        worker_id: &str,
        ttl_days: i64,
        lean_source: &str,
        theorem_id_hex: &str,
    ) -> Result<VerifyOutcome> {
        let max_age = ChronoDuration::days(ttl_days);
        if let Ok(Some(rec)) = cache.get_with_ttl(cache_key, max_age) {
            return Ok(match rec.outcome {
                AttemptOutcome::Verified { tactic, .. } => VerifyOutcome::Verified {
                    tactic: if tactic.is_empty() {
                        "cached".into()
                    } else {
                        tactic
                    },
                    duration_ms: 0,
                },
                AttemptOutcome::RejectedTypeError { msg } => VerifyOutcome::Rejected {
                    reason: "cached_rejected".into(),
                    stderr_tail: msg,
                },
                AttemptOutcome::RejectedTimeout => VerifyOutcome::Rejected {
                    reason: "cached_timeout".into(),
                    stderr_tail: String::new(),
                },
                AttemptOutcome::RejectedTrivial { reason } => VerifyOutcome::Rejected {
                    reason,
                    stderr_tail: String::new(),
                },
                AttemptOutcome::Pending => self.verify(lean_source, theorem_id_hex).await?,
            });
        }

        let raw = self.verify(lean_source, theorem_id_hex).await?;
        let outcome = match &raw {
            VerifyOutcome::Verified { tactic, .. } => AttemptOutcome::Verified {
                theorem_id: [0u8; 8],
                tactic: tactic.clone(),
            },
            VerifyOutcome::Rejected {
                reason,
                stderr_tail,
            } => AttemptOutcome::RejectedTypeError {
                msg: format!("{reason}: {stderr_tail}"),
            },
        };
        let record = AttemptRecord {
            outcome,
            lean_version: lean_version.to_string(),
            timestamp: chrono::Utc::now(),
            attempted_by: worker_id.to_string(),
            elapsed_ms: 0,
        };
        if let Err(e) = cache.put(cache_key, &record) {
            tracing::warn!("attempts cache put failed: {e}");
        }
        Ok(raw)
    }
}

/// Pre-flight firewall: scan `src` for any top-level `axiom` declaration or any
/// `sorry` token. Comments (line + nesting block) are stripped first so an
/// `axiom`-mention in a docstring passes.
///
/// Patterns:
/// - top-level `axiom`: `^\s*axiom\s+\w+` (multiline)
/// - `sorry` token: `\bsorry\b` (word boundaries — `sorrylike` does NOT match)
pub fn preflight_axiom_or_sorry(src: &str) -> Result<(), &'static str> {
    let (stripped, unterminated) = strip_comments(src);
    if unterminated {
        return Err("preflight_unterminated_comment");
    }

    if AXIOM_RE.is_match(&stripped) {
        return Err("preflight_axiom_declared");
    }

    if SORRY_RE.is_match(&stripped) {
        return Err("preflight_sorry_present");
    }

    Ok(())
}

/// Strip Lean 4 comments: `--` line comments and `/- ... -/` block comments
/// (which nest in Lean 4). Whitespace structure is preserved enough for the
/// multiline axiom regex (newlines from line comments are kept).
///
/// Returns `(stripped, unterminated_block)` where `unterminated_block` is true
/// if a `/-` opener was never matched by a closing `-/` (which the preflight
/// uses to reject the source rather than silently accept the truncated tail).
fn strip_comments(src: &str) -> (String, bool) {
    let mut out = String::with_capacity(src.len());
    let mut chars = src.chars().peekable();
    let mut unterminated = false;
    while let Some(c) = chars.next() {
        if c == '-' && chars.peek() == Some(&'-') {
            chars.next(); // consume second '-'
            for c2 in chars.by_ref() {
                if c2 == '\n' {
                    out.push('\n');
                    break;
                }
            }
        } else if c == '/' && chars.peek() == Some(&'-') {
            chars.next(); // consume '-'
            let mut depth = 1usize;
            let mut closed = false;
            while let Some(c2) = chars.next() {
                if c2 == '-' && chars.peek() == Some(&'/') {
                    chars.next();
                    depth -= 1;
                    if depth == 0 {
                        closed = true;
                        break;
                    }
                } else if c2 == '/' && chars.peek() == Some(&'-') {
                    chars.next();
                    depth += 1;
                }
            }
            if !closed {
                unterminated = true;
                break;
            }
        } else {
            out.push(c);
        }
    }
    (out, unterminated)
}

/// RAII guard that deletes a submission `.lean` file (and its `.olean` if
/// present) when dropped. The `.lean` is removed unconditionally so the
/// prover tree never accumulates stale per-verification submissions; the
/// `.olean` is best-effort cleanup since lake might already have written
/// it to `.lake/build/lib/lean/PhysicsGenerator/Derived/`.
struct SubmissionCleanup {
    path: PathBuf,
    theorem_id_hex: String,
    prover_root: PathBuf,
}

impl Drop for SubmissionCleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
        let olean_rel = format!(
            ".lake/build/lib/lean/PhysicsGenerator/Derived/Submission_{}.olean",
            self.theorem_id_hex
        );
        let _ = std::fs::remove_file(self.prover_root.join(&olean_rel));
        // Other build artifacts (.ilean, .c) co-located alongside .olean —
        // ignore failures, they're cheap to leave.
        let ilean_rel = format!(
            ".lake/build/lib/lean/PhysicsGenerator/Derived/Submission_{}.ilean",
            self.theorem_id_hex
        );
        let _ = std::fs::remove_file(self.prover_root.join(&ilean_rel));
    }
}

/// Return the last `n` lines of `s` joined with '\n'.
fn tail_lines(s: &str, n: usize) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let start = lines.len().saturating_sub(n);
    lines[start..].join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip_handles_nested_block_comments() {
        let src = "/- outer /- inner -/ still outer -/ visible";
        let (stripped, unterminated) = strip_comments(src);
        assert_eq!(stripped.trim(), "visible");
        assert!(!unterminated);
    }

    #[test]
    fn strip_flags_unterminated_block_comment() {
        let src = "/- never closes\nstuff";
        let (_stripped, unterminated) = strip_comments(src);
        assert!(unterminated);
    }

    #[test]
    fn tail_lines_caps_count() {
        let s = "a\nb\nc\nd\ne";
        assert_eq!(tail_lines(s, 2), "d\ne");
        assert_eq!(tail_lines(s, 10), "a\nb\nc\nd\ne");
    }

    #[tokio::test]
    async fn verify_cached_returns_hit_without_invoking_lake() {
        use chrono::Utc;
        use tempfile::tempdir;

        let dir = tempdir().unwrap();
        let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
        let key = [9u8; 16];
        cache
            .put(
                &key,
                &AttemptRecord {
                    outcome: AttemptOutcome::Verified {
                        theorem_id: [0; 8],
                        tactic: "ring".into(),
                    },
                    lean_version: "4.27.0".into(),
                    timestamp: Utc::now(),
                    attempted_by: "test".into(),
                    elapsed_ms: 1,
                },
            )
            .unwrap();

        // LakeBuilder pointing at /nonexistent — a real lake call would
        // error. Cache hit must short-circuit before that.
        let lake = LakeBuilder::new(
            std::path::PathBuf::from("/nonexistent"),
            std::path::PathBuf::from("/tmp"),
            1,
        );
        let result = lake
            .verify_cached(&cache, &key, "4.27.0", "test", 30, "lean source", "abc123")
            .await
            .expect("cache hit must return Ok");
        assert!(matches!(result, VerifyOutcome::Verified { .. }));
    }
}
