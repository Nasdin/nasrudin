# Physics Axioms Formalization

The system sources its axioms from **PhysLean**, a formally verified physics library
for Lean 4. Hand-coded axioms have been replaced by a catalog extraction pipeline.

## Architecture

```
physlean-extract/ (Lean 4.16.0)        prover/ (Lean 4.27.0)
  imports PhysLean                        imports Mathlib
  walks environment                       PhysicsGenerator/
  outputs catalog.json ──────────────────> Generated/*.lean (re-axiomatized)
         │                                 Derived/ (E=mc² etc.)
         │                                 Bridge/ (FFI)
         v
  engine/crates/importer/
    reads catalog.json
    populates AxiomStore
    drives lean-bridge imports
```

**Why re-axiomatize?** Lean 4.16 and 4.27 `.olean` files are not cross-compatible.
We extract theorem *statements* from PhysLean (4.16), then declare them as `axiom`
in our project (4.27). The extraction guarantees these axioms correspond to proven
PhysLean results. When PhysLean upgrades to 4.27+, we switch to direct `import PhysLean`.

**Regenerate axioms:** `just refresh-axioms` (or `just generate-axioms` for Lean files only).

---

## Layer 0: Mathematical Foundations (from Mathlib4)

These are not listed here — they come from Mathlib4's formalization of:
- ZFC set theory
- Real numbers (complete ordered field)
- Vector spaces, inner product spaces, Hilbert spaces
- Calculus (derivatives, integrals, limits, series)
- Linear algebra (matrices, eigenvalues, tensors)
- Group theory, Lie groups, Lie algebras
- Topology, manifolds, differential geometry
- Measure theory, probability

Mathlib4 provides ~350,000 theorems covering these areas.

---

## Layer 1: Physical Dimensions and Units

```lean
-- Generated/Dimensions.lean (our own — not from PhysLean)

structure Dimension where
  length      : Int
  mass        : Int
  time        : Int
  current     : Int
  temperature : Int
  amount      : Int
  luminosity  : Int
  deriving DecidableEq, Repr

axiom dim_homogeneity : ∀ (d1 d2 : Dimension), d1 = d2 -> True
```

---

## Layer 2: Classical Mechanics (from PhysLean)

```lean
-- Generated/Mechanics.lean — sourced from PhysLean.ClassicalMechanics

axiom euler_lagrange         -- Euler-Lagrange equation
axiom hamilton_equations     -- Hamilton's equations of motion
axiom harmonic_oscillator_solution  -- Sinusoidal solutions to SHO
axiom noether_theorem        -- Continuous symmetries → conserved quantities
```

PhysLean provides strong coverage of classical mechanics including
Euler-Lagrange, Hamiltonian mechanics, oscillators, and Noether's theorem.

---

## Layer 3: Special Relativity (from PhysLean)

```lean
-- Generated/SpecialRelativity.lean — sourced from PhysLean.Relativity

-- Types
structure FourMomentum where
  energy : ℝ
  px : ℝ
  py : ℝ
  pz : ℝ

-- Definitions (for E=mc² derivation chain)
def OnMassShell (p : FourMomentum) (m : ℝ) : Prop := ...
def AtRest (p : FourMomentum) : Prop := ...

-- Theorems (proven in PhysLean, re-axiomatized here)
axiom lorentz_group_SL2C          -- SL(2,C) → Lorentz group homomorphism
axiom four_momentum_on_mass_shell -- E² − p²c² = (mc²)²
axiom four_momentum_invariant     -- Lorentz invariance of mass-energy
axiom pauli_matrices_algebra      -- Pauli algebra relations
axiom lorentz_boost_composition   -- Relativistic velocity addition
axiom time_dilation               -- Time dilation formula
axiom length_contraction          -- Length contraction formula
axiom twin_paradox                -- Traveling twin ages less
```

PhysLean has very strong SR coverage including the full Lorentz group,
SL(2,C) representation, Pauli matrices, and the twin paradox.

**E = mc² is DERIVED, not axiomatized** — see `Derived/RestEnergy.lean`.

---

## Layer 4: Electromagnetism (from PhysLean)

```lean
-- Generated/Electromagnetism.lean — sourced from PhysLean.Electromagnetism

axiom maxwell_field_tensor       -- Maxwell's equations in tensor form
axiom electromagnetic_potential  -- F = dA (exterior derivative)
axiom plane_wave_solution        -- ω = c|k| dispersion relation
axiom gauge_invariance           -- F(A + dχ) = F(A)
```

PhysLean provides strong EM coverage including the field tensor formulation,
four-potential, plane wave solutions, and gauge invariance.

---

## Layer 5: Quantum Mechanics (from PhysLean)

```lean
-- Generated/QuantumMechanics.lean — sourced from PhysLean.QuantumMechanics

axiom harmonic_oscillator_qm             -- E_n = ℏω(n + 1/2)
axiom creation_annihilation_commutation  -- [a, a†] = 1
```

PhysLean has moderate QM coverage — primarily the 1D harmonic oscillator
with creation/annihilation operators. Coverage grows as PhysLean expands.

---

## Layer 6: Thermodynamics (from PhysLean)

```lean
-- Generated/Thermodynamics.lean — sourced from PhysLean.Thermodynamics + StatisticalMechanics

axiom ideal_gas_law           -- PV = nRT
axiom boltzmann_distribution  -- Canonical ensemble probability
```

PhysLean has shallow thermodynamics coverage — ideal gas and Boltzmann
distribution. The GA has fewer axioms to work with in this domain.

---

## General Relativity

**Not available.** PhysLean does not currently cover general relativity
(only 2 FLRW cosmology stubs). No `Generated/GeneralRelativity.lean` exists.

GR axioms will appear automatically when PhysLean adds coverage —
just re-run `just refresh-axioms`.

---

## PhysLean Coverage Summary

| Domain | PhysLean Coverage | Theorem Count | Result |
|--------|------------------|---------------|--------|
| Classical Mechanics | Strong | 4 | Full coverage |
| Special Relativity | Very Strong | 8 | Full coverage |
| Electromagnetism | Strong | 4 | Full coverage |
| Quantum Mechanics | Moderate | 2 | Partial |
| Thermodynamics | Shallow | 2 | Minimal |
| Statistical Mechanics | Shallow | (merged into Thermo) | Minimal |
| General Relativity | Absent | 0 | Empty |

Domains grow automatically as PhysLean adds coverage. Re-run extraction
to pick up new theorems.

---

## Derivation Targets

The GA does NOT know these exist. They are success metrics only
(checked externally, never fed to the engine):

| Target | Domain | From Axioms |
|--------|--------|-------------|
| E = mc² | SR | Mass-shell definition + algebra |
| Lorentz transformation | SR | SR postulates (PhysLean) |
| Time dilation | SR | Lorentz boost (PhysLean) |
| Length contraction | SR | Lorentz boost (PhysLean) |
| Wave equation | EM | Maxwell field tensor (PhysLean) |
| EM wave speed = c | EM | Plane wave dispersion (PhysLean) |
| QHO energy levels | QM | Harmonic oscillator (PhysLean) |
| Ideal gas energy | Thermo | Ideal gas law (PhysLean) |
| Euler-Lagrange equations | Mechanics | Euler-Lagrange (PhysLean) |

---

## Axiom Count Summary

| Layer | Count | Source |
|-------|-------|--------|
| 0: Math foundations | ~350,000 | Mathlib4 |
| 1: Dimensions | ~5 | Our own (not PhysLean) |
| 2: Classical Mechanics | 4 | PhysLean |
| 3: Special Relativity | 8 | PhysLean |
| 4: Electromagnetism | 4 | PhysLean |
| 5: Quantum Mechanics | 2 | PhysLean |
| 6: Thermodynamics | 2 | PhysLean |
| 7: General Relativity | 0 | PhysLean (no coverage yet) |
| **Total physics axioms** | **~25** | **From PhysLean catalog** |
| **Total seed knowledge** | **~350,025** | Math + physics |

---

## Pipeline Commands

```bash
# Extract theorems from PhysLean (requires Lean 4.16 via lean-toolchain)
just extract-physlean

# Generate .lean axiom files from catalog
just generate-axioms

# Full pipeline: extract → generate → build prover
just refresh-axioms
```
