//! User-facing parsers feeding the search layer.
//!
//! Three input formats reduce to the same `Expr`:
//!   * [`sexpr`] — the canonical form `Expr::to_canonical()` emits
//!     (round-trippable, lossless, machine-friendly).
//!   * [`simple`] — a small math syntax with infix operators, function
//!     calls, subscripts, greek aliases, and commutator brackets.
//!   * [`latex`] — a curated subset of LaTeX covering what physicists
//!     actually type when stating a conjecture.
//!
//! All three return [`Expr`] on success. AC-equivalent expressions
//! ultimately collide via [`crate::canonical_ac::canonical_ac_hash`].

pub mod sexpr;
pub mod simple;
pub mod latex;

pub use sexpr::{parse_sexpr, SexprError};
pub use simple::{parse_simple, SimpleError};
pub use latex::{parse_latex, LatexError};
