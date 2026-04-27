# Nasrudin — Spontaneous Modern-Physics Discovery Progress

**End goal:** Given a *truly upstream* axiom set (no axiom containing
`mc²` as sub-expression) and a generic chain-based GA, the system derives
modern physics theorems including E=mc² via combinatorics + GA, with
each emergent theorem carrying a full Lean 4 proof.

E=mc² is the **acceptance test** for the system, not the whole goal.
After it works, EM and QM theorems should follow with the same machinery.

**No cheating rule** (`memory/feedback_no_cheating.md`): an axiom is
forbidden if it contains the headline theorem of a domain as a
sub-expression. The mass-shell condition is forbidden as an axiom; it
must be a *derived* theorem.

**Broader scope** (`memory/feedback_broader_scope.md`): goal is multiple
modern physics theorems via combinatorics + compute + GA, not just E=mc².

---

## Iteration log
- Iteration counter: `14`
- Last iteration: 2026-04-28 — iter 14: Frontend rebuilt on TanStack Start v1
  (React 19, Vite 7, TypeScript 5.9, Biome 2). All 9 routes live: /, /browse,
  /theorem/$id, /signin, /profile, /api-keys, /api-docs, /leaderboard,
  /pricing. engine/crates/api extended with api_keys, saved_searches,
  preferences, workers, and me/stats handlers. Unified `AuthOrApiKey`
  extractor accepts cookie sessions or `Authorization: Bearer nsk_live_…`;
  `WorkerAuth` handles `nsk_worker_…`. End-to-end verified live: register
  → cookie auth → bearer auth → revoke → 401. Phase 0 unchanged.
- Next consolidation due at iteration: `20`

## Active phase
Phase 6.5 — Search-space heuristics. (Phases 0–5 complete; Phase 6
infrastructure complete; Phase 6 acceptance blocked on the search-space
gap. Phase 6.5.1/2 landed iter 9; Phase 6.5.4 next.)

---

## Phases 0–5 — COMPLETE (consolidated iter 10)

| Phase | Status | Acceptance evidence |
|------|--------|--------|
| 0 — Baseline | ✓ done iter 4 | `derive_emc2.sh` exit 0; `cargo test --workspace` pass; postgres healthy; mathlib cached; api smoke OK |
| 1 — GA health | ✓ done iter 4 | 15/15 unit tests pass in `nasrudin-ga`; `island_step_produces_candidates`, dedup, dimension filter all green |
| 2 — GA → Lean plumbing | ✓ done iter 4 | API server runs; channels work; LeanBridge available. Items 2.5/2.6 deferred (random-tree GA can't verify; superseded by chain-based GA) |
| 3 — Generic emitter | ✓ done iter 4 | `emit_chain_theorem` data-driven from DerivationContext; `AutoRestEnergy.lean` lake-built standalone (256s) |
| 4 — Upstream axioms | ✓ done iter 4–5 | `load_special_relativity_upstream()` registers 7 truly upstream axioms; `RestEnergyUpstream.lean` (hand) and `AutoRestEnergyUpstream.lean` (auto-emitted) both lake-build (300s, 264s); `nlinarith` solves the polynomial chain on first try |
| 5 — Chain GA infra | ✓ done iter 6–7 | `Chain`, `RuleStep`, `mutate_chain`, `splice_chains`, `evaluate_chain_fitness`, `verify_chain` all unit-tested; heavy end-to-end `upstream_chain_verifies_via_lake` PASSES in 227s |

Key files:
- `engine/crates/derive/src/{axiom_store,strategies,lean_emitter,chain}.rs`
- `engine/crates/ga/src/{chain_ga,chain_engine}.rs`
- `engine/crates/derive/src/bin/derive_emc2_upstream.rs`
- `engine/crates/ga/src/bin/discover_emc2.rs`
- `prover/PhysicsGenerator/Derived/{RestEnergy,AutoRestEnergy,RestEnergyUpstream,AutoRestEnergyUpstream}.lean`

Critical fact established: the upstream axiom set + chain primitives +
generic emitter + `nlinarith` form a *complete* derivation toolchain.
A `Chain::rest_energy_from_upstream()` produces a Lean proof verified by
the kernel. **No `mass_shell_condition` axiom anywhere in the chain.**

---

## Phase 6 — Spontaneous discovery (driver shipped, acceptance pending)

`engine/crates/ga/src/bin/discover_emc2.rs` runs the chain-based GA
over upstream axioms with no `DeriveRestEnergy*` strategy registered.
Pre-filter via `Chain::execute`; lake verify (capped) on top novel
candidates per generation.

- [x] **6.1** `chain_engine::run_discovery` — tournament-selection GA loop.
- [x] **6.2** `discover_emc2` CLI binary with `--gens / --pop / --max-len /
      --max-lake / --verify` flags. Confirms `mass_shell_condition` absent.
- [x] **6.3** Iter 8 dry run (`--gens 50 --pop 32`): 1600 candidates,
      5 unique executable, top-fitness was a single-axiom chain.
      **Verified the pipeline works but exposed the search-space gap.**
- [ ] **6.4** SEARCH-SPACE GAP. Random mutation/crossover rarely composes
      productive multi-step chains. Phase 6.5 work.
- [ ] **6.5** Long-horizon `--verify` run. Confirm `E = m·c²` lands in
      `Verified` state with lineage to upstream axioms only.
- [ ] **6.6** Re-emit discovered proof standalone, lake build outside GA.

**Acceptance:** without ever calling `DeriveRestEnergy*` or
`mass_shell_condition` as an axiom, a verified `E = m·c²` theorem is
in `discover_emc2`'s output; lineage traces back only to upstream axioms.

---

## Phase 6.5 — Search heuristics (active)

- [x] **6.5.1** `synthesize_physics_target(rng)` (iter 9) — 4 templates
      over SR atoms `{E, m, c, p0, psq, Msq, 0, 1, 2}`.
      `mutate_param` re-rolls RearrangeEquation targets;
      `random_step` synthesises targets for new RearrangeEquation insertions.
- [x] **6.5.2** Multi-step seeding (3-5 axioms) + composite fitness
      re-weighting (depth/connectivity ↑ 3.0; complexity ↓ 0.2). Iter 9.
- [x] **6.5.3** Iter 9 measurement: `--gens 100 --pop 64` → 6400 cand,
      **10 unique executable** (vs 5 baseline). Top-fitness still
      degenerate (axiom restatement). Random target synthesis at depth-2
      hits `E²=(m·c²)²` with ~10⁻⁵ probability per insertion → too sparse.
- [x] **6.5.4** Iter 11. `synthesize_target_from_facts(facts, rng)`
      with 6 algebraic transformations (same / square / mult-by-c² /
      mult-pair / transitivity / swap). `collect_chain_facts` resolves
      `IntroduceAxiom` names to statements. Wired into `mutate_param`
      + `random_step`. 25/25 tests pass.
- [ ] **6.5.5** Iter 11 measurement (`--gens 200 --pop 64`): 12800
      candidates → only **8 unique executable** (down from 10 — variance
      within noise). Top-fitness still `Msq = p0² − psq`. **Diagnosis:
      diversity collapse, not target-synthesis sparsity.** The GA
      converges to ~8 simple multi-axiom chains because tournament
      selection without crowding distance has no diversity pressure.
- [x] **6.5.6** Iter 12. Fitness sharing: each candidate's composite
      fitness multiplied by `1/count` where `count` = candidates
      sharing the same final-expr canonical. Selection step now
      ranks by `composite × shared_score`, falling back to a final
      sort by composite for tournament selection in next gen.
      25/25 unit tests pass. `--gens 200 --pop 64` dry → **10 unique**
      (vs 8 baseline). Modest improvement.
- [x] **6.5.7** Iter 12 with `--verify` PASSED. **5/5 lake builds
      succeeded.** GA-evolved chains produced 5 verified Lean
      theorems (`DiscoverGen0..4.lean` + .olean). Discoveries:
      `psq = 0`, `Msq = p0² − psq`, `Msq = p0² − 0` (non-trivial!
      involves substitution), `c · p0 = E`, `Msq = m² · c²`. None is
      E=mc² yet — they're mostly axiom restatements with one
      genuine derived intermediate (Gen 2). Saved to
      `memory/project_first_ga_verifications.md`.
- [x] **6.5.8** Iter 13. `append_productive_suffix` mutation in
      `chain_ga.rs`: appends `(RearrangeEquation{X²=Y²} +
      TakePositiveRoot)` to chains; `X`/`Y` sampled from
      `collect_chain_facts` LHS/RHS atoms. No-op if chain already
      ends in TakePositiveRoot. `mutate_chain` now picks one of
      6 ops (5 prior + 1 new). 27/27 tests pass.
- [ ] **6.5.9** Iter 13 verify run started: `discover_emc2 --gens 80
      --pop 48 --max-len 12 --max-lake 10 --verify ../prover` as
      task `bexo2voub`. Up to 10 lake verifications (~50 min budget).
      Goal: at least one `E = m·c²` final in `verified` set.

---

## Phase 7 — Multi-theorem demo

Ship after Phase 6 acceptance. ≥5 verified physics theorems across
SR + EM domains via the same engine.

- [ ] **7.1** Encode upstream EM axioms (Maxwell as definitions; Lorentz
      force as a separate postulate; same no-cheating rule).
- [ ] **7.2** Long GA run across SR + EM islands.
- [ ] **7.3** Document each verified theorem (name, lineage, rule chain,
      Lean proof) in `docs/SPONTANEOUS-DERIVATION.md`.

---

## Phase 8 — Reproducible recipe

- [ ] **8.1** `just spontaneous-emc2` recipe.
- [ ] **8.2** Brings up postgres, builds engine, runs GA, dumps proof.
- [ ] **8.3** `docs/SPONTANEOUS-DERIVATION.md`.
- [ ] **8.4** Final dumped proof builds standalone via `lake build`.

---

## Consolidation log

| Iter | Date | Action |
|------|------|--------|
| 10 | 2026-04-28 | Collapsed Phases 0–5 into a status table; trimmed working notes to keep iters 8–9 only; memory unchanged (10 notes total) |

---

## Open issues / blockers

- **Search-space gap (Phase 6.5.4):** random target synthesis too
  sparse. Iter 11 implements fact-combining target synthesis.
- **Unrelated:** `engine/crates/api/tests/auth_or_apikey.rs` references
  `physics_api::auth::AuthOrApiKey` but the api crate has no `lib`
  target so the test won't compile. Pre-existing issue, orthogonal
  to discovery work. User to address separately.
- **`.env` location:** API server reads `engine/.env` instead of repo
  root `.env`. Bug in `engine/crates/api/src/main.rs:63-66`. Cosmetic;
  PG falls back to disabled mode silently. Fix when convenient.

---

## Working notes (rolling — trimmed at consolidation)

### Iter 14 (2026-04-28) — frontend + platform endpoints

**Backend (`engine/crates/api`):**
- New entity `api_keys` with `(id, user_id?, kind, name, prefix, key_hash, last_used_at, expires_at, created_at, revoked_at)`. Migration `m20260428_000002_api_keys.rs` creates the table with FK + 2 indexes. Standalone `migrate` binary so `just db-migrate` works without starting the server.
- New extractors `AuthOrApiKey` and `WorkerAuth` in `auth.rs`. Cookie session OR `Bearer nsk_live_…` paths resolve to the same `AuthUser`. Worker keys (`nsk_worker_…`) only authorize via `WorkerAuth`, never `AuthOrApiKey`.
- New handler modules under `handlers/`: `api_keys.rs` (create/list/revoke), `saved_searches.rs` (create/list/delete/patch), `preferences.rs` (get/patch), `workers.rs` (register/heartbeat/list), `me.rs` (stats). Two new rate-limit groups: `platform_user` and `platform_worker`. `AppState` moved to `state.rs` so handlers can access pg via `State<Arc<AppState>>`.
- Crate restructured to hybrid lib+bin so integration tests can import `physics_api::*`.

**Frontend (`nasrudin-frontend`):**
- TanStack Start v1.157, React 19.2, Vite 7.3, TypeScript 5.9, Biome 2.3, KaTeX 0.16. SSR with hydration. File-based routing.
- All 9 routes live (see iter-14 summary above).
- Single backend rule: every data call hits the Rust API at `:3001` via `apiFetch` (cookies for cookie sessions, `credentials: 'include'`). No TanStack Start server functions, no Node BFF.
- KaTeX wrapper uses pure katex JS (no `react-katex` — peer-dep conflict with React 19).

### Iter 13 (2026-04-28) — Phase 6.5.8: productive-suffix mutation

- New mutation operator `append_productive_suffix` in `chain_ga.rs`:
  appends `(RearrangeEquation{X²=Y²}+TakePositiveRoot)` where
  X, Y are sampled from existing fact atoms.
- `mutate_chain` now picks one of 6 ops (was 5).
- 27/27 tests pass (added 2 new for the suffix operator).
- Long verify run `bexo2voub` started: `--gens 80 --pop 48
  --max-len 12 --max-lake 10`. Iter 14 picks up the result.

### Iter 14 handoff
- Check `bexo2voub` log: did any verified theorem have canonical
  matching `E = m * c^2` (or any equivalent shape)?
- If yes → Phase 6 acceptance MET. Move to Phase 7 (multi-theorem
  demo).
- If no → analyse what the GA explored. Possible follow-ups:
  - Add a fitness bonus for chains whose final-expr contains both
    `E` and `m` and `c` together (still generic).
  - Bias `random_atom_expr` to prefer compound expressions like
    `m * c^2` over leaves.
  - Increase `pop_size` and `gens` for a longer brute-force run.

### Iter 12 (2026-04-28) — Phase 6.5.6: fitness sharing + END-TO-END VERIFIED

- `chain_engine::run_discovery`: fitness sharing via
  `shared_score = 1 / count_with_same_final_canonical`.
- 25/25 tests pass.
- **Heavy run with `--verify`: 5/5 lake builds SUCCEEDED.**
  - Gen 0: `psq = 0`, Gen 1: `Msq = p0² − psq`,
    Gen 2: `Msq = p0² − 0` (non-trivial substitution result),
    Gen 3: `c · p0 = E`, Gen 4: `Msq = m² · c²`.
  - 5 .lean files + 5 .oleans in `prover/PhysicsGenerator/Derived/`.
  - The combinatorics+GA+Lean pipeline is **empirically proven
    end-to-end**: GA produces chains, pre-filter rejects bad ones,
    emitter produces valid Lean, lake builds it, verified theorems
    accumulate.
  - **None is E=mc² yet** — the chain shape needed
    (`...RearrangeEquation{X²=Y²}+TakePositiveRoot`) isn't being
    found by current mutation operators.

### Iter 11 (2026-04-28) — Phase 6.5.4: fact-combining target synthesis

- `synthesize_target_from_facts(facts, rng)` in `chain_ga.rs`: 6
  transformations (same / square / mult-by-c² / mult-pair /
  transitivity / swap).
- `collect_chain_facts(chain, store)` resolves `IntroduceAxiom`
  names to statements without running the chain.
- `mutate_param` and `random_step` (via `insert_random`) thread
  facts through to use fact-combining synthesis when available;
  fall back to atom-random synthesis when no facts are loaded yet.
- 25/25 tests pass.

Empirical run (`--gens 200 --pop 64`, dry):
- 12800 candidates, **only 8 unique executable** (vs 10 iter 9).
- Top-fitness final: `Msq = p0² − psq` (still degenerate).
- **Diagnosis:** diversity collapse. Tournament selection without
  crowding distance has no diversity pressure → population
  converges to ~7-8 high-fitness multi-axiom chains whose final
  expression is just the last loaded axiom. Iter 12 fix: NSGA-II
  crowding distance or fitness sharing to preserve diversity.

### Iter 12 handoff (Phase 6.5.6)

Add diversity preservation to the chain GA. Options:
- **(a) Crowding distance** — emulate NSGA-II's secondary criterion
  on `ChainIndividual`. Sort the population by Pareto rank, then
  by crowding distance within each front. Use as tiebreaker in
  tournament selection.
- **(b) Fitness sharing** — for each individual, count how many
  others share its final-expr canonical; divide composite fitness
  by `(1 + count)`.
- **(c) Random restart** — replace the bottom 20 % of each
  generation with fresh random seeds.

Recommendation: (b) is simplest and addresses the failure mode
directly (population converges on duplicate finals). Try (b) first.

Then re-run `discover_emc2 --gens 500 --pop 128` and check whether
`unique_executable` ≫ 8.

### Iter 9 (2026-04-28) — Phase 6.5.1 + 6.5.2; gap narrowed but not closed

- `synthesize_physics_target(rng)` in `chain_ga.rs`: 4 templates over
  SR atoms.
- `mutate_param` re-rolls RearrangeEquation targets.
- `random_step` synthesises targets for new RearrangeEquation steps.
- `random_chain_seed` produces 3-5 random axiom seeds (was 1).
- `composite` fitness: depth/connectivity ↑ 3.0; complexity ↓ 0.2.
- 25/25 unit tests pass.

Empirical run (`--gens 100 --pop 64`, dry): 6400 candidates,
10 unique executable, top-fitness `Msq = p0² − psq` (axiom restatement).
At depth-2 atoms, P(target = E²=(m·c²)²) ≈ 1e-5 per insertion → sparse.

### Iter 10 (2026-04-28) — Consolidation pass

- progress.md collapsed from 752 → ~230 lines. Phases 0–5 in a status
  table; iters 1–8 working notes archived (in git history).
- Memory: 10 notes total, no duplicates. `project_ga_engine_state.md`
  has stale iter-1 architectural-pivot content; trimmed in this pass.
- No code changes.

### Iter 11 handoff (Phase 6.5.4)

Implement fact-combining target synthesis in `chain_ga::synthesize_physics_target`:

1. Take a snapshot of `ctx.facts()` at chain-execution time during
   mutation.
2. For a new RearrangeEquation, sample one or two facts, then build a
   target by:
   - `same`: target = fact (trivial; tests the synthesis path)
   - `square`: if fact is `a = b`, target is `a² = b²`
   - `multiply`: if facts are `a = b` and `c = d`, target is `a·c = b·d`
   - `transitivity`: if facts are `a = b` and `a = c`, target is `b = c`
3. This requires `mutate_chain` and `random_step` to know the chain's
   running context. Simplest: compute the context once per
   chain-mutation by running `Chain::execute` partially.

Then re-run `discover_emc2 --gens 200 --pop 64` and measure
`unique_executable` improvement.
