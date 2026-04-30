//! Named axiom — a `(name, domain, statement, description)` quadruple
//! that the GA's chain engine can introduce by name.
//!
//! Lives in `nasrudin-core` (and not `nasrudin-derive`) so the rocks
//! crate can encode/decode `Axiom` values for the cold-tier corpus
//! without forming a `rocks → derive` dependency cycle. The
//! [`AxiomStore`](../../../derive/src/axiom_store.rs) keeps a hot
//! `HashMap<String, Axiom>` plus a `Box<dyn CorpusBackend>` cold tier.
//!
//! Wire format: `bincode` over the `serde::{Serialize, Deserialize}`
//! derives. The Mathlib math-corpus extract has Lean dependent-type
//! `Expr` trees up to ~200 levels deep — the JSON loader disables
//! `serde_json`'s recursion limit, but bincode has no such limit so
//! this works out of the box for `Expr` round-tripping.
//!
//! See `engine/crates/derive/src/axiom_store.rs` and
//! `engine/crates/rocks/src/lib.rs` for the cold-tier wiring.

use crate::{Domain, Expr};
use serde::{Deserialize, Serialize};

/// A named axiom with its domain and expression.
///
/// `name` is the chain engine's `IntroduceAxiom { axiom_name }`
/// lookup key; `statement` is the propositional `Expr` the chain
/// engine substitutes into the proof state. `description` is an
/// operator-facing free-form blurb (typically the first line of the
/// Lean docstring).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Axiom {
    /// Human-readable name (e.g., `"energy_momentum_relation"`,
    /// `"Real.add_comm"`).
    pub name: String,
    /// The physics or math domain this axiom belongs to. Drives
    /// `AxiomStore::by_domain` and is the secondary-index key in the
    /// cold-tier RocksDB store.
    pub domain: Domain,
    /// The axiom's mathematical statement as a structured `Expr`. May
    /// be `Expr::Var(name)` placeholder if the upstream catalog
    /// emitted a non-`expr_ast` entry (decorative-only).
    pub statement: Expr,
    /// Brief description (Lean docstring first line, or a hand-coded
    /// blurb from the postulate loaders).
    pub description: String,
}
