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
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::{Arc, LazyLock};
use std::time::Duration;

use anyhow::{Context, Result};
use tokio::process::Command;
use tokio::sync::Semaphore;

const VERIFY_TIMEOUT: Duration = Duration::from_secs(300);

static AXIOM_RE: LazyLock<regex::Regex> = LazyLock::new(|| {
    regex::Regex::new(r"(?m)^\s*axiom\s+\w+").expect("static regex compiles")
});

static SORRY_RE: LazyLock<regex::Regex> = LazyLock::new(|| {
    regex::Regex::new(r"\bsorry\b").expect("static regex compiles")
});

/// Outcome of a single verification attempt.
#[derive(Debug, Clone)]
pub enum VerifyOutcome {
    Verified {
        tactic: String,
        duration_ms: u32,
    },
    Rejected {
        reason: String,
        stderr_tail: String,
    },
}

/// Tokio task pool that spawns `lake build` in throwaway tmpdir copies of the
/// trusted `prover/` template. Concurrency is capped by a semaphore.
pub struct LakeBuilder {
    prover_template: PathBuf,
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

    /// Pre-flight checks (`axiom` / `sorry`), then runs `lake build` on a
    /// tmpdir copy of `prover_template` with the submission written to
    /// `PhysicsGenerator/Derived/Submission_<theorem_id_hex>.lean`.
    pub async fn verify(
        &self,
        lean_source: &str,
        theorem_id_hex: &str,
    ) -> Result<VerifyOutcome> {
        // 1. Pre-flight first — reject before we even allocate a slot.
        if let Err(reason) = preflight_axiom_or_sorry(lean_source) {
            return Ok(VerifyOutcome::Rejected {
                reason: reason.to_string(),
                stderr_tail: String::new(),
            });
        }

        // 2. Acquire a permit (caps concurrent lake-build invocations).
        let _permit = self
            .semaphore
            .acquire()
            .await
            .context("lake-builder semaphore closed")?;

        // 3. Allocate an isolated tmpdir under `workspace_root`.
        let workspace_root = self.workspace_root.clone();
        let prover_template = self.prover_template.clone();
        let lean_source = lean_source.to_string();
        let theorem_id_hex = theorem_id_hex.to_string();

        let join = tokio::task::spawn_blocking(move || -> Result<tempfile::TempDir> {
            std::fs::create_dir_all(&workspace_root).ok();
            let tmp = tempfile::tempdir_in(&workspace_root)
                .context("create lake-builder tmpdir")?;
            mirror_tree(&prover_template, tmp.path())
                .context("mirror prover template into tmpdir")?;
            // Write submission.
            let submission_dir = tmp.path().join("PhysicsGenerator").join("Derived");
            std::fs::create_dir_all(&submission_dir)
                .context("create Derived submission dir")?;
            let submission_path =
                submission_dir.join(format!("Submission_{theorem_id_hex}.lean"));
            std::fs::write(&submission_path, lean_source.as_bytes())
                .context("write submission lean source")?;
            Ok(tmp)
        })
        .await
        .context("spawn_blocking join error")?;

        let tmp = match join {
            Ok(t) => t,
            Err(e) => {
                return Ok(VerifyOutcome::Rejected {
                    reason: "toolchain_error".into(),
                    stderr_tail: e.to_string(),
                });
            }
        };

        // 4. Run `lake build` with a 300s wall-clock timeout.
        let start = std::time::Instant::now();
        let mut cmd = Command::new("lake");
        cmd.arg("build")
            .current_dir(tmp.path())
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
                let _ = tokio::time::timeout(
                    Duration::from_secs(5),
                    child.wait(),
                )
                .await;
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

/// Mirror `src` into `dst` using hardlinks where possible, falling back to copy.
fn mirror_tree(src: &Path, dst: &Path) -> Result<()> {
    for entry in walkdir::WalkDir::new(src).follow_links(true) {
        let entry = entry.with_context(|| format!("walkdir {}", src.display()))?;
        let rel = entry
            .path()
            .strip_prefix(src)
            .context("strip_prefix in mirror_tree")?;
        let target = dst.join(rel);
        if entry.file_type().is_dir() {
            std::fs::create_dir_all(&target)
                .with_context(|| format!("mkdir {}", target.display()))?;
        } else if entry.file_type().is_file() {
            if let Some(parent) = target.parent() {
                std::fs::create_dir_all(parent).ok();
            }
            // Try hardlink first, fall back to copy on any error (cross-device,
            // permission, etc.).
            if std::fs::hard_link(entry.path(), &target).is_err() {
                std::fs::copy(entry.path(), &target).with_context(|| {
                    format!(
                        "copy {} -> {}",
                        entry.path().display(),
                        target.display()
                    )
                })?;
            }
        }
        // Symlinks: followed (target contents are copied/hardlinked).
    }
    Ok(())
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
}
