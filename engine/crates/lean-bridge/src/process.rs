//! Process-based Lean4 verification via `lake build`.
//!
//! This is the primary verification path until the C FFI bridge is wired.
//! For each candidate theorem:
//!
//! 1. Generate a standalone `.lean` file with the theorem statement
//! 2. Write it to `prover/PhysicsGenerator/Derived/`
//! 3. Run `lake build PhysicsGenerator.Derived.<name>`
//! 4. Parse the exit code: 0 = verified, nonzero = rejected
//!
//! The generated `.lean` file uses the tactic cascade to attempt
//! automated proof.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use anyhow::{Context, Result};
use nasrudin_core::{Domain, Expr, Theorem};

use crate::VerifyResult;
use crate::lean_syntax::{
    collect_free_vars, expr_to_lean4, resolve_imports,
};
use crate::tactic::render_cascade_tactic;

/// Configuration for process-based verification.
#[derive(Debug, Clone)]
pub struct ProcessVerifyConfig {
    /// Root path of the Lean4 prover project (contains `lakefile.lean`).
    pub prover_root: PathBuf,
    /// Subdirectory within the prover for generated files.
    pub output_subdir: String,
    /// Lean4 namespace for generated theorems.
    pub namespace: String,
    /// Maximum wall-clock time for `lake build` per theorem.
    pub timeout: Duration,
}

impl Default for ProcessVerifyConfig {
    fn default() -> Self {
        Self {
            prover_root: PathBuf::from("../prover"),
            output_subdir: "PhysicsGenerator/Derived".into(),
            namespace: "PhysicsGenerator.Derived".into(),
            timeout: Duration::from_secs(60),
        }
    }
}

impl ProcessVerifyConfig {
    /// Create a config from an environment variable or default.
    pub fn from_env() -> Self {
        let prover_root = std::env::var("PROVER_ROOT")
            .map(PathBuf::from)
            .unwrap_or_else(|_| PathBuf::from("../prover"));
        Self {
            prover_root,
            ..Default::default()
        }
    }

    /// The directory where generated `.lean` files are written.
    pub fn output_dir(&self) -> PathBuf {
        self.prover_root.join(&self.output_subdir)
    }
}

/// Process-based verifier that shells out to `lake build`.
pub struct ProcessVerifier {
    config: ProcessVerifyConfig,
}

impl ProcessVerifier {
    /// Create a new process verifier.
    pub fn new(config: ProcessVerifyConfig) -> Self {
        Self { config }
    }

    /// Create a verifier from environment defaults.
    pub fn from_env() -> Self {
        Self::new(ProcessVerifyConfig::from_env())
    }

    /// Verify a theorem by generating a `.lean` file and running `lake build`.
    pub fn verify_theorem(&self, theorem: &Theorem) -> Result<VerifyResult> {
        let safe_name = sanitize_theorem_name(&hex::encode(theorem.id));
        let module_name = format!("Auto_{safe_name}");

        // Generate the .lean file content
        let lean_content = generate_lean_file(
            &module_name,
            &theorem.statement,
            &theorem.domain,
            &theorem.proof,
        );

        // Write to the prover directory
        let output_dir = self.config.output_dir();
        std::fs::create_dir_all(&output_dir)
            .context("Failed to create output directory")?;

        let file_path = output_dir.join(format!("{module_name}.lean"));
        std::fs::write(&file_path, &lean_content)
            .context("Failed to write .lean file")?;

        tracing::debug!("Wrote verification file: {}", file_path.display());

        // Run lake build
        let module_path = format!(
            "{}.{module_name}",
            self.config.namespace
        );
        let result = run_lake_build(
            &self.config.prover_root,
            &module_path,
            self.config.timeout,
        )?;

        // Clean up the generated file (optional, keep for debugging)
        // std::fs::remove_file(&file_path).ok();

        Ok(result)
    }

    /// Verify a raw canonical expression string.
    pub fn verify_canonical(
        &self,
        canonical: &str,
        statement: &Expr,
        domain: &Domain,
    ) -> Result<VerifyResult> {
        let hash = nasrudin_core::compute_theorem_id(canonical);
        let safe_name = sanitize_theorem_name(&hex::encode(hash));
        let module_name = format!("Auto_{safe_name}");

        let lean_content = generate_lean_file(
            &module_name,
            statement,
            domain,
            &nasrudin_core::ProofTree::Axiom([0; 8]),
        );

        let output_dir = self.config.output_dir();
        std::fs::create_dir_all(&output_dir)?;

        let file_path = output_dir.join(format!("{module_name}.lean"));
        std::fs::write(&file_path, &lean_content)?;

        let module_path = format!("{}.{module_name}", self.config.namespace);
        run_lake_build(&self.config.prover_root, &module_path, self.config.timeout)
    }

    /// Check if the prover project exists and `lake` is available.
    pub fn check_available(&self) -> Result<bool> {
        let lakefile = self.config.prover_root.join("lakefile.lean");
        if !lakefile.exists() {
            tracing::warn!(
                "Prover project not found at {}",
                self.config.prover_root.display()
            );
            return Ok(false);
        }

        // Check if lake is on PATH
        match Command::new("lake").arg("--version").output() {
            Ok(output) if output.status.success() => {
                let version = String::from_utf8_lossy(&output.stdout);
                tracing::info!("Lake available: {}", version.trim());
                Ok(true)
            }
            _ => {
                tracing::warn!("lake command not found on PATH");
                Ok(false)
            }
        }
    }
}

/// Generate a standalone `.lean` file for a theorem.
///
/// The generated file:
/// 1. Imports the necessary axiom modules
/// 2. Opens the PhysicsGenerator namespace
/// 3. States the theorem with free variables as `ℝ` parameters
/// 4. Attempts proof via the full tactic cascade
fn generate_lean_file(
    name: &str,
    statement: &Expr,
    domain: &Domain,
    proof: &nasrudin_core::ProofTree,
) -> String {
    let mut out = String::new();

    // Imports
    let imports = resolve_imports(domain, proof);
    for imp in &imports {
        out.push_str(&format!("import {imp}\n"));
    }
    out.push('\n');

    // Header comment
    out.push_str(&format!(
        "/-!\n# Auto-generated by Nasrudin GA engine\n\
         \nDomain: {domain:?}\n\
         Theorem: {name}\n\
         \nVerify: `lake build {namespace}.{name}`\n-/\n\n",
        namespace = "PhysicsGenerator.Derived"
    ));

    // Namespace
    out.push_str("namespace PhysicsGenerator.Derived\n\n");
    out.push_str("open PhysicsGenerator\n");

    // Open domain-specific namespaces
    match domain {
        Domain::SpecialRelativity => {
            out.push_str("open PhysicsGenerator.SpecialRelativity\n");
        }
        Domain::Electromagnetism => {
            out.push_str("open PhysicsGenerator.Electromagnetism\n");
        }
        Domain::QuantumMechanics => {
            out.push_str("open PhysicsGenerator.QuantumMechanics\n");
        }
        Domain::Thermodynamics => {
            out.push_str("open PhysicsGenerator.Thermodynamics\n");
        }
        Domain::ClassicalMechanics => {
            out.push_str("open PhysicsGenerator.Mechanics\n");
        }
        _ => {}
    }
    out.push('\n');

    // Theorem statement with free variables as parameters
    let free_vars = collect_free_vars(statement);
    let params: Vec<String> = free_vars
        .iter()
        .filter(|v| !is_constant_var(v))
        .map(|v| v.clone())
        .collect();

    let param_str = if params.is_empty() {
        String::new()
    } else {
        let vars = params.join(" ");
        format!(" ({vars} : ℝ)")
    };

    let lean_statement = expr_to_lean4(statement);

    out.push_str(&format!(
        "/-- Auto-generated theorem -/\ntheorem {name}{param_str} :\n    {lean_statement} := "
    ));

    // Proof: use tactic cascade
    out.push_str(&render_cascade_tactic());
    out.push('\n');

    // Close namespace
    out.push_str("end PhysicsGenerator.Derived\n");

    out
}

/// Run `lake build` on a module and return the verification result.
fn run_lake_build(
    prover_root: &Path,
    module_path: &str,
    timeout: Duration,
) -> Result<VerifyResult> {
    tracing::debug!("Running: lake build {module_path} in {}", prover_root.display());

    let child = Command::new("lake")
        .arg("build")
        .arg(module_path)
        .current_dir(prover_root)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn();

    let mut child = match child {
        Ok(c) => c,
        Err(e) => {
            return Ok(VerifyResult::FfiError {
                message: format!("Failed to spawn lake: {e}"),
            });
        }
    };

    // Wait with timeout
    let result = match wait_with_timeout(&mut child, timeout) {
        Ok(status) => {
            if status.success() {
                tracing::info!("lake build {module_path}: VERIFIED");
                VerifyResult::Verified {
                    proof_term: vec![],
                }
            } else {
                let stderr = child
                    .stderr
                    .take()
                    .map(|mut s| {
                        let mut buf = String::new();
                        use std::io::Read;
                        s.read_to_string(&mut buf).ok();
                        buf
                    })
                    .unwrap_or_default();

                tracing::debug!("lake build {module_path}: REJECTED\n{stderr}");
                VerifyResult::Rejected {
                    reason: if stderr.is_empty() {
                        "lake build failed".to_string()
                    } else {
                        // Truncate long error messages
                        let truncated: String = stderr.chars().take(500).collect();
                        truncated
                    },
                }
            }
        }
        Err(_) => {
            // Timeout: kill the process
            child.kill().ok();
            tracing::warn!("lake build {module_path}: TIMEOUT after {}s", timeout.as_secs());
            VerifyResult::Timeout
        }
    };

    Ok(result)
}

/// Wait for a child process with a timeout.
fn wait_with_timeout(
    child: &mut std::process::Child,
    timeout: Duration,
) -> Result<std::process::ExitStatus, ()> {
    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return Ok(status),
            Ok(None) => {
                if start.elapsed() > timeout {
                    return Err(());
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(_) => return Err(()),
        }
    }
}

/// Sanitize a hex string into a valid Lean4 identifier.
fn sanitize_theorem_name(hex_id: &str) -> String {
    // Lean4 identifiers can't start with a digit
    format!("t{hex_id}")
}

/// Check if a variable name is actually a physics constant.
fn is_constant_var(name: &str) -> bool {
    matches!(
        name,
        "c" | "G"
            | "h_planck"
            | "hbar"
            | "k_B"
            | "e_charge"
            | "m_e"
            | "m_p"
            | "eps0"
            | "mu0"
            | "N_A"
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_core::{BinOp, PhysConst, ProofTree};

    #[test]
    fn generate_lean_file_emc2() {
        let stmt = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("E".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Var("m".into())),
                Box::new(Expr::BinOp(
                    BinOp::Pow,
                    Box::new(Expr::Const(PhysConst::SpeedOfLight)),
                    Box::new(Expr::Lit(2, 1)),
                )),
            )),
        );

        let content = generate_lean_file(
            "test_emc2",
            &stmt,
            &Domain::SpecialRelativity,
            &ProofTree::Axiom([0; 8]),
        );

        assert!(content.contains("import PhysicsGenerator.Basic"));
        assert!(content.contains("import PhysicsGenerator.Generated.SpecialRelativity"));
        assert!(content.contains("theorem test_emc2"));
        assert!(content.contains("E m : ℝ"));
        assert!(content.contains("E = (m * (c ^ (2 : ℝ)))"));
        assert!(content.contains("first"));
        assert!(content.contains("grind"));
    }

    #[test]
    fn sanitize_name() {
        assert_eq!(sanitize_theorem_name("abcd1234"), "tabcd1234");
    }
}
