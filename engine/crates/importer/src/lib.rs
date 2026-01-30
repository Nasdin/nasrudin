//! Theorem importer for the Physics Generator.
//!
//! This crate handles importing known physics theorems and identities from
//! external sources to seed the genetic algorithm's initial population:
//!
//! - Classical mechanics axioms (Newton's laws, conservation laws)
//! - Electromagnetism (Maxwell's equations)
//! - Special relativity (Lorentz transformations, E=mc^2)
//! - Quantum mechanics (Schrodinger equation, commutation relations)
//! - Thermodynamics (laws of thermodynamics)
//! - Mathematical identities (trig, calculus, algebra)
//!
//! Each imported theorem is converted to the `Expr` AST, assigned a canonical form,
//! hashed for deduplication, and stored as an axiom-origin theorem.
