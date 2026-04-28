# Rediscover-Physics Architecture

**Goal:** Make the GA's discovery loop sound enough that deriving E=mc² is a meaningful proof-of-concept — i.e. the system actually composes a chain of rewrites starting from the postulates of relativity (and intermediate kinematic identities the GA has to derive on the way), without any headline result baked in.

**Why this matters:** if E=mc² shows up in the output but the AxiomStore already contained a statement of E=mc² (or any of its trivial reformulations), the run proves nothing about the system's discovery capacity. Same goes for shortcuts via `mass_shell_condition`. The whole point of the proof-of-concept is to demonstrate that an arbitrary physics result can emerge from genuinely fundamental premises. Without that property, the system is a search-and-display tool, not a discovery engine.

## Current state (as of 2026-04-28)

- **Corpus**: 12 hand-coded upstream axioms in `engine/crates/derive/src/axiom_store.rs` are the only real `Expr`-tree axioms the GA can compose. The 1907 PhysLean catalog entries are pretty-printed Lean strings referencing PhysLean-internal types — decorative, not GA-usable.
- **Mathlib**: not extracted at all.
- **Classical mechanics**: not present in any corpus consumed by the engine. No `F=ma`, `p=mv`, `dE=F·dx`.
- **Search heuristics**: random mutation + tournament selection over `RuleStep` chains. Memory documents the gap: pure-random GA does not compose the 6-step upstream chain to E=mc² in feasible time.
- **No-cheat firewall**: the server-side chain replay (just landed, see `reverify::check_chain`) catches workers who fabricate steps or misclaim canonical statements. It does **not** catch the upstream issue of headline results sitting in the AxiomStore as starting blocks.

## Architecture

Five components, ordered by dependency:

### 1. Lean→Expr translator (foundation)

**Problem.** PhysLean catalog and Mathlib both ship statements as Lean syntax trees, but the only available extraction (`physlean-extract` today) flattens them to pretty-printed strings. The GA can't rewrite strings.

**Solution.** Replace `ppTypeExpr : Lean.Expr → String` with `exprToAst : Lean.Expr → Json` that walks the Lean AST and emits a structured JSON tree mapping to our `nasrudin_core::Expr` enum. Supported subset:

| Lean form                                         | Output AST                                |
|---------------------------------------------------|-------------------------------------------|
| `@Eq α a b`                                       | `{op: "Eq", lhs, rhs}`                    |
| `@HAdd.hAdd α α α inst a b` (with α := ℝ)         | `{op: "BinOp", kind: "Add", a, b}`        |
| `@HMul.hMul`, `@HSub.hSub`, `@HDiv.hDiv`          | `BinOp`/`Sub`/`Div`                       |
| `@HPow.hPow α ℕ α inst a (Nat.lit n)`             | `{op: "BinOp", kind: "Pow", a, b: Lit(n)}`|
| `Real.sqrt x`                                     | `{op: "UnaryOp", kind: "Sqrt", arg}`      |
| Numeric literals (`OfNat.ofNat`)                  | `{op: "Lit", num, den: 1}`                |
| Free variables / `fvar` of `Real`                 | `{op: "Var", name}`                       |
| Universal binders over Real-typed variables       | absorbed (variables become free `Var`s)   |
| Anything else                                     | reject statement, increment skipped count |

**Carrier specialization.** Most Mathlib statements are polymorphic (`a · b = b · a` over `CommSemigroup`). The translator instantiates the type universe with `ℝ` (or the relevant carrier — `Vector` for SR, `Complex` for QM later) and re-elaborates the term. Statements that don't admit a clean ℝ instance are skipped.

### 2. Configurable walker

`physlean-extract` currently hardcodes a PhysLean prefix whitelist (`Walker.lean:isPhysLeanName`). Make it configurable via CLI flag or env var so we can run:

- `lake exe extract --whitelist=PhysLean.,Lorentz.,SpaceTime.` (existing PhysLean coverage)
- `lake exe extract --whitelist=Mathlib.Algebra.GroupPower,Mathlib.Algebra.Ring.Basic,Mathlib.Algebra.Order.Ring,Mathlib.Analysis.SpecialFunctions.Pow.Real,Mathlib.Data.Real.Basic` (math corpus)

Output goes to `physlean-extract/output/<name>_corpus.json`. The AxiomStore can load multiple corpus files.

### 3. Mechanics postulates (gap fill)

Even after Mathlib is extracted, classical mechanics postulates aren't anywhere. We need:

- `momentum_def`: `p = m · v`
- `newton_second`: `F = m · a`
- `acceleration_def`: `a = dv/dt` (treated as a primitive symbol pair, not actual derivatives)
- `work_def`: `W = F · d` (or `dW = F · dx`)
- `kinetic_energy_def`: `KE = (1/2) · m · v²`
- `force_conservative`: `F = -dU/dx` (similar treatment)

**Where they live.** Until PhysLean adds them upstream, a small `engine/crates/derive/src/postulates_classical.rs` file with each postulate as an `Axiom { name, statement: Expr, domain: ClassicalMechanics, description }`. Cited by name to a textbook (Goldstein, Landau-Lifshitz). Loaded alongside the Mathlib corpus.

This is a small file (≤30 lines per postulate, ~6 postulates). It is *not* hand-written math; it is the irreducible base set of Newtonian mechanics — analogous to the upstream SR axioms already in the repo. The "no hand-writing" rule applies to *derivable* identities, not to *postulates*.

Action item: open a PhysLean issue to upstream these as a `PhysLean.Mechanics.Newtonian` namespace, and remove the local file once they land.

### 4. No-cheat audit harness

Boot-time check, run on both `physics-api` and `discover_emc2`:

1. Walk the AxiomStore.
2. For each axiom, hash its canonical-form statement (`Expr::to_canonical()`).
3. Compare against a deny-list of known headline results, also stored as canonical strings:
   - `(= v:E (* v:m (^ c:SpeedOfLight n:2)))` — E=mc²
   - `(= v:Eγ (* c:SpeedOfLight v:p))` — photon energy-momentum
   - Mass-shell `(= (^ v:E n:2) (+ (* (^ v:p n:2) (^ c:SpeedOfLight n:2)) (* (^ v:m n:2) (^ c:SpeedOfLight n:4))))` — already forbidden by name in worker, generalize to canonical-form match.
   - Maxwell's equations, Schrödinger, Klein-Gordon, etc.
4. Hard-fail boot if any match. Print the matching axiom + its origin (catalog file + name) so it's debuggable.
5. Re-run the audit at the end of `discover_emc2`'s seed-sync.

The deny-list itself is tiny and intentional. Each entry is a target the GA is supposed to derive, not start from.

### 5. Search heuristics

The known gap (per memory: pure-random GA over 7 axioms doesn't compose the 6-step upstream chain). Three additions:

- **Productive-suffix mutation**: when a chain produces an Expr that's structurally close to the canonical target (Levenshtein on the prefix-form string, or tree-edit distance), bias mutation toward extending it rather than replacing prefix. Increases the chance of the GA continuing a productive line of work.
- **Target-synthesis fitness**: add a fitness component scoring the final Expr's similarity to the target's structural signature — count of `=`, `*`, `^`, presence of `c²`, presence of `m`, presence of `E`. Crucially, the target itself is **not** added to the AxiomStore. Fitness shaping is metadata, not a starting block. (This is the cheat-adjacent step that needs the audit harness as the safety net.)
- **Crossover seeds**: at startup, seed ~10% of the population with `Chain::rest_energy_from_upstream()` perturbed by 1–2 random edits (mutate-or-delete a step). Tests whether the GA can *recover* the chain after perturbation, before asking it to discover the chain from nothing. Useful for debugging the search dynamics; turn off for production runs.

## Phased rollout

| Phase | Deliverable                                                                                 | Est. effort  |
|-------|---------------------------------------------------------------------------------------------|--------------|
| α     | Spec doc (this file) + plan doc + skeleton `exprToAst` with 3 unit tests                    | 0.5 day      |
| β     | Full `exprToAst` for the supported subset; `--whitelist` CLI; emit `expr_ast` JSON field    | 2–3 days     |
| γ     | AxiomStore reads `expr_ast`; `postulates_classical.rs`; no-cheat audit harness              | 1 day        |
| δ     | Search heuristics (productive-suffix + target-synthesis + crossover seeds)                  | 1 day        |
| ε     | Run worker, observe ladder: kinematics → momentum → work-energy → SR → E=mc². Document.     | open-ended   |

Phase ε is where "did it work?" gets answered. The earlier phases buy us a shot at it; whether the GA converges to E=mc² in laptop-time even with all this is a search-quality question that may require further iteration on δ.

## Acceptance criteria

1. The AxiomStore loaded by the worker contains zero canonical statements that match the deny-list.
2. The `expr_ast` field in the corpus is populated for ≥80% of statements that pass the supported-subset filter (the rest get rejected with a counted reason).
3. The Mathlib corpus contains ≥50 distinct algebraic identities the GA can pick via `RuleStep::IntroduceAxiom`.
4. The classical-mechanics postulates load cleanly into the AxiomStore.
5. A 30-minute run of `discover_emc2 --domain sr` produces *some* verified intermediate theorem (e.g. `(c·p)² = E²` or one of its equivalents) — proving the search is making progress.
6. (Stretch) A 24-hour run produces a verified statement of E=mc² in canonical form, derived through a chain that does not introduce any headline result as an axiom.

Criteria 1–5 are the proof of plausibility. Criterion 6 is the proof of concept.
