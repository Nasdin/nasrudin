//! Tactic cascade configuration for Lean4 verification.
//!
//! Defines the ordered list of tactics to try when verifying a candidate
//! theorem, each with a timeout. Tactics are tried in order of speed;
//! the first to succeed produces the proof.
//!
//! See LEAN4-BRIDGE.md §4 for the full tactic strategy.

use std::time::Duration;

/// A single tactic in the verification cascade.
#[derive(Debug, Clone)]
pub struct TacticEntry {
    /// Lean4 tactic name (e.g., `"omega"`, `"grind"`).
    pub name: &'static str,
    /// Maximum time allowed for this tactic.
    pub timeout: Duration,
    /// Human-readable description of what this tactic is good at.
    pub description: &'static str,
}

/// The default tactic cascade, ordered from fastest to most powerful.
///
/// | Priority | Tactic     | Timeout | Best For                          |
/// |----------|------------|---------|-----------------------------------|
/// | 1        | omega      | 500ms   | Integer/natural number goals      |
/// | 2        | norm_num   | 500ms   | Numeric computations              |
/// | 3        | ring       | 1s      | Polynomial ring equalities        |
/// | 4        | simp       | 2s      | Rewriting with Mathlib lemma DB   |
/// | 5        | linarith   | 2s      | Linear arithmetic inequalities    |
/// | 6        | field_simp | 2s      | Field fraction simplification     |
/// | 7        | polyrith   | 5s      | Polynomial arithmetic (external)  |
/// | 8        | grind      | 10s     | SMT-style reasoning (most powerful)|
pub fn default_cascade() -> Vec<TacticEntry> {
    vec![
        TacticEntry {
            name: "omega",
            timeout: Duration::from_millis(500),
            description: "Integer/natural number goals",
        },
        TacticEntry {
            name: "norm_num",
            timeout: Duration::from_millis(500),
            description: "Numeric computations",
        },
        TacticEntry {
            name: "ring",
            timeout: Duration::from_secs(1),
            description: "Polynomial ring equalities",
        },
        TacticEntry {
            name: "simp",
            timeout: Duration::from_secs(2),
            description: "Rewriting with Mathlib lemma DB",
        },
        TacticEntry {
            name: "linarith",
            timeout: Duration::from_secs(2),
            description: "Linear arithmetic inequalities",
        },
        TacticEntry {
            name: "field_simp",
            timeout: Duration::from_secs(2),
            description: "Field fraction simplification",
        },
        TacticEntry {
            name: "polyrith",
            timeout: Duration::from_secs(5),
            description: "Polynomial arithmetic (calls external oracle)",
        },
        TacticEntry {
            name: "grind",
            timeout: Duration::from_secs(10),
            description: "SMT-style reasoning (most powerful)",
        },
    ]
}

/// Total maximum verification time if all tactics are attempted.
pub fn total_cascade_timeout() -> Duration {
    default_cascade().iter().map(|t| t.timeout).sum()
}

/// Render a Lean4 `by` block that tries the full cascade.
///
/// Produces:
/// ```lean
/// by
///   first
///   | omega
///   | norm_num
///   | ring
///   | simp
///   | linarith
///   | field_simp
///   | polyrith
///   | grind
/// ```
pub fn render_cascade_tactic() -> String {
    let mut out = String::from("by\n  first\n");
    for entry in default_cascade() {
        out.push_str(&format!("  | {}\n", entry.name));
    }
    out
}

/// Render a single tactic `by` block.
pub fn render_single_tactic(tactic_name: &str) -> String {
    format!("by\n  {tactic_name}\n")
}

/// Render a tactic `by` block with a specific lemma list.
///
/// Produces: `by grind [lemma1, lemma2, ...]`
pub fn render_tactic_with_lemmas(tactic_name: &str, lemmas: &[&str]) -> String {
    if lemmas.is_empty() {
        return render_single_tactic(tactic_name);
    }
    let lemma_list = lemmas.join(", ");
    format!("by\n  {tactic_name} [{lemma_list}]\n")
}
