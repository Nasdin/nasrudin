//! Builds the LLM prompt from a hunch + nearest-neighbour theorems +
//! axiom catalog. Pure string assembly — no I/O.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeighbourTheorem {
    pub id: String,
    pub statement: String,
    pub domain: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AxiomEntry {
    pub name: String,
    pub domain: String,
    pub description: String,
}

pub const SYSTEM_PROMPT: &str = "You are an assistant for a formal-theorem-discovery system. \
Given a researcher's informal conjecture and a set of related verified theorems from the existing \
corpus, produce a JSON object with a `suggestions` array of derivation seeds the system can \
search from.\n\n\
Each seed includes:\n\
- axiom_set: which axioms to enable (subset of the provided catalog, by name)\n\
- initial_population: 5-10 expression sketches the GA should mutate (Lean-style strings)\n\
- mutation_priors: per-operator weights biasing the GA's mutation choices, in [0, 1]\n\
- target_shape: optional human-readable description of the target form\n\
- rationale: why these seeds, in 1-2 sentences\n\n\
You DO NOT prove anything. You suggest where to search. \
Aim for 3 distinct suggestions per call.";

pub fn build_user_prompt(
    hunch: &str,
    domain_hint: Option<&str>,
    neighbours: &[NeighbourTheorem],
    axioms: &[AxiomEntry],
) -> String {
    let mut out = String::new();
    out.push_str("# Researcher's hunch\n\n");
    out.push_str(hunch.trim());
    if let Some(d) = domain_hint {
        out.push_str(&format!("\n\nDomain hint: {d}"));
    }

    out.push_str("\n\n# Nearest verified theorems in the corpus\n\n");
    if neighbours.is_empty() {
        out.push_str("(none found)\n");
    } else {
        for n in neighbours {
            out.push_str(&format!("- [{}, {}] {}\n", n.id, n.domain, n.statement));
        }
    }

    out.push_str("\n# Axiom catalog\n\n");
    if axioms.is_empty() {
        out.push_str("(catalog unavailable)\n");
    } else {
        for a in axioms {
            out.push_str(&format!("- {} ({}): {}\n", a.name, a.domain, a.description));
        }
    }

    out.push_str(
        "\n# Output format\n\n\
        Reply with strictly valid JSON: \
        {\"suggestions\": [{\"axiom_set\": [...], \"initial_population\": [...], \
        \"mutation_priors\": {...}, \"target_shape\": \"...\", \"rationale\": \"...\"}]}\n",
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn neighbour(id: &str, statement: &str, domain: &str) -> NeighbourTheorem {
        NeighbourTheorem {
            id: id.into(),
            statement: statement.into(),
            domain: domain.into(),
        }
    }

    fn axiom(name: &str, domain: &str, desc: &str) -> AxiomEntry {
        AxiomEntry {
            name: name.into(),
            domain: domain.into(),
            description: desc.into(),
        }
    }

    #[test]
    fn builds_prompt_with_all_sections() {
        let p = build_user_prompt(
            "Energy and mass relate by c squared",
            Some("SpecialRelativity"),
            &[neighbour("deadbeef", "(c·p)² + m²c⁴ = E²", "SpecialRelativity")],
            &[axiom(
                "sr_invariant_interval",
                "SpecialRelativity",
                "ds² = c²dt² - dx²",
            )],
        );
        assert!(p.contains("Energy and mass"));
        assert!(p.contains("Domain hint: SpecialRelativity"));
        assert!(p.contains("deadbeef"));
        assert!(p.contains("sr_invariant_interval"));
        assert!(p.contains("# Output format"));
        assert!(p.contains("\"suggestions\""));
    }

    #[test]
    fn handles_empty_neighbours_and_no_domain_hint() {
        let p = build_user_prompt("a hunch", None, &[], &[]);
        assert!(p.contains("(none found)"));
        assert!(p.contains("(catalog unavailable)"));
        assert!(!p.contains("Domain hint"));
    }

    #[test]
    fn system_prompt_locks_json_contract() {
        assert!(SYSTEM_PROMPT.contains("JSON"));
        assert!(SYSTEM_PROMPT.contains("axiom_set"));
        assert!(SYSTEM_PROMPT.contains("mutation_priors"));
        assert!(SYSTEM_PROMPT.contains("DO NOT prove"));
    }
}
