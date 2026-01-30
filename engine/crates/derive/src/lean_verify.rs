//! Process-based Lean4 verification.
//!
//! Writes a `.lean` file and runs `lake build` to verify the proof.
//! Upgradeable to FFI-based verification later.

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
