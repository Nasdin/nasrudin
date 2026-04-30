# Quantum Physics Derivation — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans / TDD per item.

**Goal:** Make the system structurally capable of spontaneously deriving quantum-physics theorems by adding QM postulates, QM targets, store-aware mutation, QM-aware fitness, expanded math corpus, populated PhysLean AST, and QM headline guards.

**Architecture:** Seven self-contained edits, each compiles & tests independently, layered:
1. Postulates (foundation) → 2. Targets (gradient) → 7. Audit (guardrail) → 3. Mutation (reach) → 4. Fitness (signal) → 5/6. Corpus (substrate).

**Tech Stack:** Rust 2024 edition, Cargo workspace, Lean4 (PhysLean extractor), RocksDB, Axum.

---

## Item 1 — `load_quantum_mechanics_postulates()`

**Files:**
- Create: `engine/crates/derive/src/postulates_quantum.rs`
- Modify: `engine/crates/derive/src/lib.rs:32` — add `pub mod postulates_quantum;`
- Modify: `engine/crates/api/src/main.rs:110` — call `axiom_store.load_quantum_mechanics_postulates();`

**Postulates:**
- `qm_position_op` — `x̂ψ = x·ψ` (position acts multiplicatively)
- `qm_momentum_op` — `p̂ψ = -iℏ ∂ψ/∂x`
- `qm_canonical_commutator` — `[x̂,p̂] = iℏ`  i.e. `xp - px = i·ℏ`
- `qm_schrodinger_time_evolution` — `iℏ ∂ψ/∂t = Ĥψ`
- `qm_hamiltonian_free_particle` — `Ĥ_free = p̂²/(2m)`
- `qm_eigenvalue_equation` — `Âψ = aψ` (general operator-eigenvalue form)
- `qm_born_rule` — `P(a) = |⟨φ_a|ψ⟩|²` represented as `P = |c|²` with `c = ⟨φ|ψ⟩`
- `qm_normalization` — `∫ |ψ|² dx = 1`
- `qm_hbar_positive` — `ℏ > 0`

Use the existing AST primitives `PartialDeriv`, `Integral`, `UnOp::Conjugate`, `BinOp::Sub` (for commutator), `App` (for operator application), `Var("psi")`, `Var("i_unit")` for imaginary unit.

## Item 2 — QM TargetSpec(s)

**Files:**
- Modify: `engine/crates/ga/src/target.rs:65-70` — extend `TargetSpec::lookup`
- Add: `qm_free_particle_energy()` — Eₙ-equivalent target; ladder: Schrödinger free particle → -iℏ∂ψ/∂x = pψ → E = p²/2m.
- Add: `qm_harmonic_oscillator_levels()` — Eₙ = ℏω(n+½).

## Item 3a — AxiomInjection samples AxiomStore

**Files:**
- Modify: `engine/crates/ga/src/mutation.rs` — add `mutate_with_store(expr, &AxiomStore, domain, rng)`. Keep `mutate()` calling `mutate_with_store(expr, &empty_store, None, rng)` for back-compat.
- Modify: `engine/crates/ga/src/island.rs:155+` — `step()` takes `&AxiomStore`, threads to mutate.
- Modify: `engine/crates/ga/src/engine.rs` — pass `self.axiom_store` into island.step.

## Item 3b — Chain-engine QM target wiring

**Files:**
- Modify: `engine/crates/ga/src/bin/worker.rs:288` — already supports any TargetSpec name via env var; document the new QM target names.
- Add an end-to-end test: chain_engine seeded with QM postulates + qm_free_particle_energy target → discovery report has at least one chain with positive ladder_progress.

## Item 4 — QM-aware `nasrudin_relevance` + dimension domain awareness

**Files:**
- Modify: `engine/crates/ga/src/fitness.rs:85-91` — `dimensional_score` takes `theorem.domain`, calls `domain_variable_dimensions`.
- Modify: `engine/crates/ga/src/fitness.rs:134-159` — add quantum_signal helper:
  - +0.25 if expression contains `PartialDeriv(_, "t")` AND `PhysConst::ReducedPlanck`
  - +0.20 if contains `UnOp::Conjugate` OR `Var("i_unit")`
  - +0.20 if contains `BinOp::TensorProduct` OR `BinOp::Dot` (state inner products)
  - +0.15 if contains `Integral { var: "x", .. }` over abs/conjugate (normalization shape)
- Domain-gate: only apply quantum_signal when `theorem.domain == Domain::QuantumMechanics`.

## Item 5 — Mathlib QM whitelist in DomainTagger

**Files:**
- Modify: `physlean-extract/PhysLeanExtract/DomainTagger.lean:99-100` — branch Mathlib namespaces:
  - `Mathlib.Analysis.InnerProductSpace.*` → QuantumMechanics
  - `Mathlib.LinearAlgebra.SelfAdjoint.*` → QuantumMechanics
  - `Mathlib.Analysis.NormedSpace.Spectrum.*` → QuantumMechanics
  - `Mathlib.Topology.ContinuousFunction.Algebra.*` → QuantumMechanics
  - `Mathlib.MeasureTheory.*` → PureMath
  - `Mathlib.LinearAlgebra.TensorProduct.*` → QuantumMechanics
- Modify: `justfile` — add `extract-mathlib-qm` recipe wrapping `lake exe extract --whitelist=…`

## Item 6 — Backfill PhysLean catalog expr_ast

The catalog.json checked-in has 0/1907 expr_ast because it was generated before the universal translator. Walker.lean's universal translator is total. Ensure:
- Re-run instructions documented (justfile `extract-physlean` recipe).
- Add a startup assertion in `axiom_store.rs::load_from_catalog` that warns when 0% of entries have AST.

## Item 7 — QM headlines in no_cheat_audit

**Files:**
- Modify: `engine/crates/derive/src/no_cheat_audit.rs:25-74` — append to `forbidden_canonical_statements()`:
  - "schrodinger_time_evolution"
  - "canonical_commutator"
  - "born_rule_amplitude_squared"
  - "harmonic_oscillator_levels"
  - "free_particle_energy"

## Verification

- `cargo build -p nasrudin-derive -p nasrudin-ga -p nasrudin-core -p physics-api` — clean.
- `cargo test -p nasrudin-derive -p nasrudin-ga` — all green.
- The new postulates pass `audit()`.
- Boot of physics-api with QM postulates registered does not panic the no-cheat audit (postulates ≠ headlines).

