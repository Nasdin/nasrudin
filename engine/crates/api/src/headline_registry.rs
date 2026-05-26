//! Curated registry of headline physics theorems and how to recognise
//! them in the corpus.
//!
//! When the GA derives a chain whose final statement is, say,
//! `(= v:E (* v:m (^ c:SpeedOfLight n:2)))`, the canonical form is
//! correct but unreadable to a human. This module is the
//! single-source-of-truth that maps canonical-form fragments back to
//! a curated human identity:
//!
//!   * `name`         — short headline ("Mass-energy equivalence")
//!   * `description`  — one-sentence prose for the cite block / OG card
//!   * `display_latex`— canonical LaTeX ("E = m c^2")
//!   * `domain`       — UI-facing domain string
//!
//! Two consumers:
//!
//!   * `handlers::featured` — checks whether each headline has been
//!     proved yet, drives the landing-page Featured cards.
//!   * `handlers::theorems::by_id` — wraps the raw `Theorem` row with
//!     `display_name` + `description` when the canonical statement
//!     matches a headline, so the corpus page stops showing
//!     `gen 0` / `lake_build` for a row that is the platform's first
//!     E=mc² proof.
//!
//! Researcher-submitted conjectures get the same treatment via a
//! separate lookup (theorem id → conjecture_jobs.hunch), not handled
//! here. This file is for the curated headline set only.

/// One curated headline.
pub struct Headline {
    pub name: &'static str,
    pub description: &'static str,
    pub display_latex: &'static str,
    pub domain: &'static str,
    /// Canonical-form substrings that must ALL appear in a theorem's
    /// `canonical_statement` for us to consider it this headline.
    /// Patterns target the worker-emitted form (e.g. `v:E`,
    /// `c:SpeedOfLight`), NOT English words. See the deploy-v7
    /// post-mortem in featured.rs for why pattern lists must be
    /// canonical-form tokens.
    pub canonical_patterns: &'static [&'static str],
}

/// The curated set. Order is the landing-page display order.
pub const HEADLINES: &[Headline] = &[
    Headline {
        name: "Mass-energy equivalence",
        description: "Rest energy of a body equals its mass times the square of the speed of light.",
        display_latex: "E = m c^{2}",
        domain: "Special relativity",
        // `(= v:E (* v:m (^ c:SpeedOfLight n:2)))`
        canonical_patterns: &["v:E", "(* v:m (^ c:SpeedOfLight n:2)"],
    },
    Headline {
        name: "Newton's second law",
        description: "Force equals mass times acceleration.",
        display_latex: "F = m a",
        domain: "Classical mechanics",
        canonical_patterns: &["v:F", "(* v:m v:a)"],
    },
    Headline {
        name: "Boltzmann entropy",
        description: "Entropy of an isolated system is proportional to the natural logarithm of its microstate count.",
        display_latex: "S = k_B \\ln \\Omega",
        domain: "Statistical mechanics",
        canonical_patterns: &["v:S", "v:k_B"],
    },
    Headline {
        name: "Schrödinger equation",
        description: "Time evolution of a quantum state is governed by the Hamiltonian operator.",
        display_latex: "i\\hbar\\dot\\psi = \\hat H \\psi",
        domain: "Quantum mechanics",
        canonical_patterns: &["v:psi", "v:H"],
    },
    Headline {
        name: "Einstein field equations",
        description: "Spacetime curvature is sourced by the stress-energy tensor.",
        display_latex: "R_{\\mu\\nu} - \\tfrac12 g_{\\mu\\nu} R = 8\\pi T_{\\mu\\nu}",
        domain: "General relativity",
        canonical_patterns: &["v:R_uv", "v:T_uv"],
    },
    Headline {
        name: "Gauss's law",
        description: "Electric flux through a closed surface is proportional to the enclosed charge.",
        display_latex: "\\nabla\\cdot E = \\rho/\\varepsilon_0",
        domain: "Electromagnetism",
        canonical_patterns: &["v:div_E", "v:rho"],
    },
];

/// Match a canonical statement against the curated headline set.
/// Returns the first matching entry — ALL patterns must appear so a
/// stray `v:E` in an unrelated theorem won't false-positive. Returns
/// `None` for theorems that don't correspond to a curated headline
/// (which is most of them — the GA finds many side lemmas).
pub fn match_canonical(canonical: &str) -> Option<&'static Headline> {
    HEADLINES
        .iter()
        .find(|h| h.canonical_patterns.iter().all(|p| canonical.contains(*p)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_emc2_canonical() {
        let h = match_canonical("(= v:E (* v:m (^ c:SpeedOfLight n:2)))")
            .expect("E=mc^2 canonical should match");
        assert_eq!(h.name, "Mass-energy equivalence");
        assert_eq!(h.display_latex, "E = m c^{2}");
    }

    #[test]
    fn matches_newton_canonical() {
        let h = match_canonical("(= v:F (* v:m v:a))").expect("F=ma should match");
        assert_eq!(h.name, "Newton's second law");
    }

    /// Stray `v:E` in an unrelated theorem must NOT false-positive as
    /// E=mc². The all-patterns rule guards against this.
    #[test]
    fn stray_var_does_not_false_positive() {
        assert!(match_canonical("(= v:E (* v:lambda v:phi))").is_none());
    }

    /// Theorems with no headline match (the common case for emergent
    /// side lemmas) return None cleanly.
    #[test]
    fn unrelated_theorem_returns_none() {
        assert!(match_canonical("(= (+ n:1 n:1) n:2)").is_none());
        assert!(match_canonical("").is_none());
    }
}
