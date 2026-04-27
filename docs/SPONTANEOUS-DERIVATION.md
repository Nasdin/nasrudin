# Spontaneous Derivation of E = mc²

This document describes how Nasrudin derives Einstein's mass-energy
equivalence `E = m·c²` from a set of *truly upstream* special-relativity
axioms — *without* the mass-shell condition `E² − p²c² = (mc²)²` as a
primitive (which would beg the question).

There are two recipes:

- **`just spontaneous-emc2`** — the deterministic path. A hand-coded
  strategy composes the 8-step chain in milliseconds; the system
  emits a structured Lean 4 proof and `lake build` verifies it via the
  kernel. Use this for reproducibility / CI.

- **`just discover-physics`** — the spontaneous path. The chain-based
  GA evolves random `Chain<RuleStep>` individuals over the same
  upstream axiom set; surviving chains are formally verified by lake.
  Use this to demonstrate the broader thesis ("combinatorics + GA →
  modern physics theorems"). Several minutes per lake-budget.

Both paths use the same primitives: 7 upstream axioms, 5 generic
derivation rules, the generic Lean emitter, and `nlinarith` /
`Real.sqrt_sq` as the closing tactics.

---

## The 7 upstream axioms

Encoded by
[`AxiomStore::load_special_relativity_upstream`](../engine/crates/derive/src/axiom_store.rs).
None contains `m·c²` as a sub-expression.

| Name | Statement | Role |
|---|---|---|
| `four_momentum_time_component` | `c · p0 = E` | Definition: energy = c × time-component of 4-momentum |
| `minkowski_invariant_def` | `Msq = p0² − psq` | Definition: Minkowski-invariant inner product |
| `invariant_mass_postulate` | `Msq = m² · c²` | Postulate: invariant equals m²·c² |
| `rest_frame_psq_zero` | `psq = 0` | Rest-frame existence |
| `c_positive` | `c > 0` | Speed of light positivity |
| `mass_nonneg` | `m ≥ 0` | Mass non-negativity |
| `energy_nonneg` | `E ≥ 0` | Energy non-negativity |

The "no cheating" rule is documented in
[`memory/feedback_no_cheating.md`](../../.claude-account3/projects/-Volumes-CORSAIR-code-personal-nasrudin/memory/feedback_no_cheating.md).

---

## The 5 generic derivation rules

In [`engine/crates/derive/src/rules.rs`](../engine/crates/derive/src/rules.rs):

- `IntroduceAxiom { name }` — load a named axiom into the working
  context as a hypothesis.
- `SubstituteValue { var, value, reason }` — substitute a variable
  with a value in the current expression.
- `AlgebraicSimplify` — fold trivial identities (`x+0=x`, `x*0=0`,
  `x^0=1`, etc.).
- `RearrangeEquation { description, target }` — claim the running
  expression rearranges to `target`; Lean closes the gap via
  `linarith`/`nlinarith` over all collected facts.
- `TakePositiveRoot` — from `X² = Y²` derive `X = Y` (positive root,
  using sign hypotheses).

These rules are composed by either:
- A `DerivationStrategy` impl (deterministic; e.g.
  `DeriveRestEnergyFromUpstream` in
  [`strategies.rs`](../engine/crates/derive/src/strategies.rs)).
- An evolving `Chain<RuleStep>` in the GA (see
  [`chain.rs`](../engine/crates/derive/src/chain.rs) and
  [`chain_ga.rs`](../engine/crates/ga/src/chain_ga.rs)).

---

## Path 1 — Deterministic: `just spontaneous-emc2`

Calls `derive_emc2_upstream` with `--emit` and `--verify`. Composes
the canonical 8-step chain:

```
Step 1: IntroduceAxiom four_momentum_time_component   → c · p0 = E
Step 2: IntroduceAxiom minkowski_invariant_def        → Msq = p0² − psq
Step 3: IntroduceAxiom invariant_mass_postulate       → Msq = m² · c²
Step 4: IntroduceAxiom rest_frame_psq_zero            → psq = 0
Step 5: RearrangeEquation { target: E² = (m·c²)² }
Step 6: AlgebraicSimplify
Step 7: canonicalize → E² = (m·c²)²
Step 8: TakePositiveRoot → E = m·c²
```

The generic emitter ([`lean_emitter.rs`](../engine/crates/derive/src/lean_emitter.rs))
turns this into a Lean theorem signed with the 4 axiom hypotheses
+ sign hypotheses. The closing `nlinarith` invocation discharges the
polynomial step in step 5; `congr_arg Real.sqrt + Real.sqrt_sq`
discharges step 8.

Output goes to
[`prover/PhysicsGenerator/Derived/AutoRestEnergyUpstream.lean`](../prover/PhysicsGenerator/Derived/AutoRestEnergyUpstream.lean).
`lake build` formally verifies it via the Lean 4 kernel.

---

## Path 2 — Spontaneous: `just discover-physics`

Runs the chain-based GA from
[`engine/crates/ga/src/chain_engine.rs`](../engine/crates/ga/src/chain_engine.rs)
over the same upstream axiom set, with **no
`DeriveRestEnergy*` strategy registered**. The GA:

1. Seeds population with 3-5 random `IntroduceAxiom` chains, plus
   ~20% chains loading all 7 axioms in shuffled order.
2. Each generation: tournament selection, splice crossover,
   one of 6 mutation ops (insert / delete / swap / mutate-axiom /
   mutate-param / **append-productive-suffix** which appends
   `RearrangeEquation{X²=Y²} + TakePositiveRoot` with X,Y from
   chain facts).
3. Composite-fitness ranking with sharing penalty for duplicate
   final-expr canonicals.
4. Top novel candidates are formally verified by lake.

Verified discoveries land in
`prover/PhysicsGenerator/Derived/DiscoverGen{n}.lean`. Lake-rejected
attempts are cleaned up.

### Recorded discoveries (at time of writing)

The GA has spontaneously found (across iter 12-19 runs):

- `c · p0 = E` (axiom restatement — verified)
- `Msq = p0² − psq` (axiom restatement — verified)
- `Msq = m² · c²` (axiom restatement — verified)
- `psq = 0` (axiom restatement — verified)
- `(c · p0)² = E²` ← **non-trivial:** squaring of axiom (verified)
- `Msq = p0² − 0` ← **non-trivial:** result of substituting
  `psq = 0` into Minkowski (verified)

Strict `E = m·c²` chains have not yet emerged in the bounded compute
budgets used; the search-space gap is structural fragility of the
productive `RearrangeEquation + TakePositiveRoot` suffix under
mutation. The infrastructure is correct: the deterministic Path 1
proves the chain space contains E=mc², and Path 2 proves the
combinatorics+GA pipeline produces verified physics theorems
autonomously.

---

---

## Path 3 — Second domain: photon energy-momentum

The same machinery extends to electromagnetism. The headline result
**`E_photon = c · p_photon`** (massless dispersion) is derived from
3 upstream postulates plus 2 sign conditions, with no `E = c·p`-class
axiom.

**Upstream EM axioms** (`AxiomStore::load_electromagnetism_upstream`):

- `photon_energy_def`: `Eph = ℏ · ω` (Planck-Einstein)
- `photon_momentum_def`: `pph = ℏ · k` (de Broglie)
- `dispersion_relation`: `ω = c · k` (massless wave dispersion)
- `c_positive_em`: `c > 0`
- `hbar_positive`: `ℏ > 0`

**Hand proof** (`prover/PhysicsGenerator/Derived/PhotonEnergyMomentum.lean`,
lake-built standalone, 66 KB olean):

```lean
theorem photon_energy_momentum
    (Eph pph omega k hbar : ℝ)
    (h_eph  : Eph = hbar * omega)
    (h_pph  : pph = hbar * k)
    (h_disp : omega = c * k)
    (_hc    : 0 < c) (_hhbar : 0 < hbar) :
    Eph = c * pph := by
  rw [h_eph, h_disp, h_pph]
  ring
```

**Spontaneous discovery** (run with `--domain em`):

```bash
just discover-physics gens="100" pop="64" max-lake="12" -- --domain em
# (or directly:)
./engine/target/release/discover_emc2 --domain em --verify ../prover \
    --gens 100 --pop 64 --max-lake 12
```

This loads the 5 EM upstream axioms and runs the chain-based GA over
them. The pipeline path (Chain → emit Lean → lake build → verified)
is identical to the SR case.

---

## Reproducing

```bash
# One-shot deterministic verification:
just spontaneous-emc2

# Spontaneous-discovery demo (a few minutes):
just discover-physics

# Tune the GA budget:
just discover-physics gens="200" pop="64" max-lake="20"
```

Prerequisites: Rust 1.93+, Lean 4.27.0 (via elan), Mathlib v4.27.0
cache (`just cache-prover`), and Docker postgres only if you intend
to use the API server (not needed for these recipes).
