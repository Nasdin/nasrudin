# Nasrudin

**Derive physics from pure logic.** Nasrudin discovers theorems by generating candidates and formally proving them in Lean 4. A distributed theorem generation engine that starts from mathematical axioms and physics postulates, then uses genetic algorithms to evolve new theorems -- eventually rediscovering known physics (like E=mc^2) without being told what to find. Synthetic theorem generation with formal verification.

Named after [Nasrudin](https://en.wikipedia.org/wiki/Nasreddin), the wise fool of Sufi tradition who found truth through unconventional paths.

## How It Works

```
Mathematical Axioms (Mathlib full corpus) + Physics Postulates (~43)
        |
        v
[ LLM Steerer (Kimi K2.6) ]  <-- emits SteeringConfig every 2 hours (configurable):
        |                         domain weights, mutation knobs,
        |                         per-cluster directives, target proposals
        v
[ Reinforcement Learning layer ]  <-- four UCB1/LinUCB bandits learn:
        |                              · K (clusters per island)
        |                              · per-cluster directive multipliers
        |                              · test-time compute scaling
        |                              · contextual generalisation across
        |                                (strength, choice) via LinUCB
        v
   Rust GA Engine (island model · combine · mutate · crossover)
        |
   Candidate Theorems
        |
   Lean4 Formal Verifier (grind · simp · omega · ring · linarith)
        |
   Verified Theorems --> RocksDB
        |
   Server re-verifies --> Accepted into global theorem database
        |
        +----> Reward signal feeds back to bandits + LLM prompt
                (per-cluster fitness deltas, γ-discounted over 3 chunks,
                 plus intrinsic-motivation novelty bonus)
```

Nasrudin doesn't know what physics looks like. It generates candidate mathematical statements by combining and mutating existing theorems, then uses Lean4 to formally prove or reject them. An LLM sets coarse strategy every two hours (or as configured), while four bandits update continuously every `STEERER_CADENCE_SECONDS` using verification rewards. Over time, the system builds up a corpus of verified mathematical truths, with the steering loop continuously self-tuning toward more productive directions. Some of those truths turn out to be real physics; the longer it runs, the more original the discoveries.

Every theorem carries its full Lean4 proof. Academics can inspect proofs in the web UI, download any theorem as a standalone `.lean` file, and independently re-verify it with `lake build` -- no trust in the server required.

## Platform features

The web UI and API server share a single auth model:

- **Cookie sessions** for the web UI (axum-login + tower-sessions, Argon2 passwords).
- **Bearer API keys** (`Authorization: Bearer nsk_live_…`) for programmatic clients.

Both flow through the same `AuthOrApiKey` extractor and resolve to the same user.
Worker registration uses a separate `nsk_worker_…` key issued at registration time.

Generate keys at `/api-keys` once you're signed in.

## VISION: Distributed Architecture

Nasrudin is designed as a **distributed compute network**. Anyone can contribute by running a worker node:

```
                    ┌──────────────────────┐
                    │   Central Server     │
                    │                      │
                    │  Axum API (:3001)    │
                    │  RocksDB (theorems)  │
                    │  PostgreSQL (users)  │
                    │  Lean4 (re-verify)   │
                    └──────────┬───────────┘
                               │
              POST /api/ingest │  (verified theorems)
              POST /api/workers/heartbeat
                               │
          ┌────────────────────┼────────────────────┐
          │                    │                    │
   ┌──────▼──────┐     ┌──────▼──────┐     ┌──────▼──────┐
   │  Worker 1   │     │  Worker 2   │     │  Worker N   │
   │  (home PC)  │     │  (cloud)    │     │  (your PC)  │
   │             │     │             │     │             │
   │  Rust GA    │     │  Rust GA    │     │  Rust GA    │
   │  Lean4      │     │  Lean4      │     │  Lean4      │
   │  RocksDB    │     │  RocksDB    │     │  RocksDB    │
   │  (local)    │     │  (local)    │     │  (local)    │
   └─────────────┘     └─────────────┘     └─────────────┘
```

**Workers** run the full Rust engine + Lean4 prover locally. They generate and verify theorems independently, then POST discoveries to the central server. The server performs a **second round of verification** with its own Lean4 instance before accepting theorems into the global database. This double-verification prevents invalid or malicious submissions.

Workers also pull a fresh `SteeringConfig` (see below) from `/api/seed` on every chunk boundary so the LLM-driven steerer can re-bias the entire fleet's exploration without requiring a worker restart.

**Download a release binary** and you're contributing compute to the network. No setup beyond running the executable.

## LLM-Driven Cluster Steering

A naïve genetic algorithm running across thousands of volunteer workers is unfocused: it grinds through the entire axiom space with no notion of what the corpus actually needs next. Nasrudin solves this by having an LLM **steer the cluster** at most every `LLM_STEER_INTERVAL_SECONDS` (default 2h), while RL bandits apply feedback on each `STEERER_CADENCE_SECONDS` tick. The refresh gate is claimed in persisted `cluster_steering` history before any prompt construction or provider call, so restarts and multiple API processes do not reset or duplicate the two-hour budget window. The interval is an upper bound, not a scheduled spend: with `LLM_STEER_REQUIRE_NEW_EVIDENCE=1` the daemon first checks that fresh RL/GA telemetry exists in the rolling window, defaulting to at least one worker `cluster_report` before it spends Gradient tokens. LLM spend is separately capped with `LLM_STEER_MAX_TOTAL_TOKENS` (default 10000) and `LLM_STEER_MAX_COMPLETION_TOKENS` (default 2048). Before each provider call, the daemon sums actual provider-reported prompt+completion usage in the rolling `LLM_STEER_ROLLING_WINDOW_SECONDS` window (default: the same 2h interval), subtracts that from the cap, and clamps the new request to the remaining budget. If there is not enough new evidence, the prompt plus a minimum completion cannot fit, or Gradient fails, the daemon reuses the last validated strategy and the RL/GA loop keeps running.

```
   Aggregate user demand            Last 10 cycles' outcomes
   (saved searches, paid hunches,   (theorems verified, domain split,
    active conjecture jobs)          cascade rejects, lake fail rate)
                  \                 /
                   \               /
                    v             v
            ┌────────────────────────────┐
            │  DigitalOcean Gradient     │
            │  Latest GLM model          │
            │  (auto from /v1/models)
            │  POST /v1/chat/completions │
            └────────────┬───────────────┘
                         │
                  SteeringConfig JSON
                  (domain weights, axiom emphasis,
                   mutation knobs, soft + hard targets)
                         │
                         v
              ArcSwap snapshot in API
                         │
        ┌────────────────┼────────────────┐
        │                │                │
   /api/steering    /api/seed (folded)  workers fold + bias
   (ETag/304)       on every poll       next chunk's GA run
```

The steerer runs in two modes:

- **Mode C — full authority.** When no paid Researcher jobs are running, Kimi has full control: it sets `domain_weights` (a probability simplex over physics domains), `axiom_emphasis` (per-axiom multiplicative bias), `fitness_weights` (novelty / dimensional elegance / chain-length penalty / target proximity), and `mutation_knobs` (rate, suffix bias, population size, elitism fraction). It can also inject `soft_targets` and `hard_targets` to point the explorer fleet at specific lemmas.

- **Mode B — knobs locked.** As soon as ≥1 paid conjecture job is `claimed` or `running`, the steerer flips to mode B: it can still re-balance domain weights and emphasis, but `mutation_knobs` are forced `null` and `hard_targets` are emptied. This keeps the slot-hour accounting paid customers are billed against predictable; the steerer's job in mode B is to bias the *explorer fleet* toward prerequisite lemmas in the active-job domains, not to retune the GA out from under a running paid slice.

Each cycle's *outcome* (theorems verified, actual domain distribution, cascade rejects, lake failure rate, manual verifies) is captured and fed back into the next cycle's prompt — so the steerer learns from what actually happened, not just what it asked for.

**Validation & safety.** Every emitted `SteeringConfig` is range-checked (domain weights sum to 1, mutation rate ∈ [0.05, 0.30], population size ∈ [32, 512], etc.). On any failure — Gradient outage, parse error, validator reject — the daemon transparently falls back to the last-known-good config and flags the row in `cluster_steering`. The cluster keeps running with stale-but-validated steering indefinitely.

The Gradient API key (`GRADIENT_API_KEY`) is server-owned and lives only in the daemon's environment. It is never exposed to clients and is distinct from the per-user encrypted-key flow used by the FunSearch-style conjecture creator. By default, the server key is reserved for the two-hour strategy refresh path; cosmetic per-theorem LLM naming stays disabled unless `LLM_NAMING_ENABLED=1` is explicitly set.

**Dynamic model selection.** Leave `STEERER_MODEL` unset to have the daemon query Gradient's live `/v1/models` catalog and select the newest GLM-family model it can identify, such as `glm-5.2`. Set `STEERER_MODEL` only when you intentionally want to pin a specific model. If catalog probing fails, `GRADIENT_GLM_MODEL_FALLBACK` is used. The resolved model is cached locally for `GRADIENT_MODEL_CACHE_TTL_SECONDS` (default 86400) so restarts do not repeatedly hit the catalog; set the TTL to `0` to force a fresh probe on every boot.

**AlphaEvolve-style strategy genomes.** The LLM steerer is not disabled locally; it is made sparse and high-leverage. In addition to ordinary `SteeringConfig` fields, the model can emit `extension.strategy_genome_v1`, a compact domain policy that workers expand into GA/RL moves:

```json
{
  "extension": {
    "strategy_genome_v1": {
      "domain_policies": {
        "special_relativity": {
          "compute_scale": 1.5,
          "mutation_rate_mult": 1.1,
          "suffix_bias_delta": 0.2,
          "elitism_delta": 0.05,
          "operator_bias": {
            "append_productive_suffix": 1.6
          }
        }
      }
    }
  }
}
```

Workers apply only the matching domain policy in scope C, clamp every value, fingerprint the policy, and store local reward history for repeated genomes. Each repeated genome gets a tiny local evolution-strategy controller over macro-policy strength: the worker samples antithetic strength perturbations across chunks, rewards them by novelty, Lake pass rate, and verified theorem yield, then updates the controller mean/sigma in `worker_rl_state.json`. Strong genomes are amplified, weak genomes are dampened toward neutral, and promising variants keep improving between LLM refreshes and restarts. This is the intended 10k-token/2h pattern: the LLM proposes compact strategic variants; RL/ES and the GA do the expensive evaluation.

**Local desktop low-LLM profile.** `just up` defaults to the safe local profile even when `.env` contains a real Gradient key:

- `LLM_STEER_INTERVAL_SECONDS=7200`
- `LLM_STEER_MAX_TOTAL_TOKENS=10000`
- `LLM_STEER_MAX_COMPLETION_TOKENS=2048`
- `LLM_NAMING_ENABLED=0`
- `NASRUDIN_NO_PAID_JOBS=1`
- `NASRUDIN_AUTO_TARGETS=1`
- `NASRUDIN_WORKER_DOMAIN=all`
- `NASRUDIN_RL_HALF_LIFE_HOURS=168`
- `NASRUDIN_WORKER_LOAD_CATALOG=1`

Override these only when you intentionally want different behavior. By default the local worker runs `--domain all --target auto`, so the laptop-origin stack starts with the featured-first curriculum rather than a single hardcoded SR target. The local worker persists scoped RL/QD state in `~/.local/share/nasrudin-worker/worker_rl_state.json`, while the LLM remains a high-level strategy source rather than the workhorse. When `physlean-extract/output/catalog.json` is present, standalone workers also load safe local PhysLean catalog propositions into the hot tier before chunks run; the loader skips non-propositional placeholders and any canonical statement on the no-cheat headline deny-list.

**Cloudflare desktop deployment.** For the cost-minimized deployment, your desktop/laptop is the origin server. The frontend, API, workers, local RocksDB corpus, Lean verifier, RL state, and GA run on your machine; Cloudflare only provides the public edge, TLS, DNS, and tunnel/proxy routing. Use [deploy/cloudflare-local.example.yml](deploy/cloudflare-local.example.yml) as the tunnel template:

- `nasrudin.org` → `http://localhost:3000` (local frontend)
- `api.nasrudin.org` → `http://localhost:3001` (local API/backend)

Keep the services bound to localhost. Cloudflare Tunnel exposes them globally without moving compute to GCP/AWS or opening raw inbound ports on the laptop.

Before starting long-running services, run:

```bash
just local-origin-check
```

Then start the local origin and tunnel:

```bash
just up
cloudflared tunnel run nasrudin-local
```

**Local no-cheat E=mc² smoke.** To prove the workhorse path without an API key or submission daemon, run:

```bash
just smoke-emc2-local
```

Or invoke the SR worker directly with local Lake verification only:

```bash
NASRUDIN_NO_PAID_JOBS=1 \
cargo run -p nasrudin-ga --bin worker -- \
  --domain sr \
  --target sr_rest_energy \
  --verify ../prover \
  --gens 1 \
  --pop 8 \
  --chunks 1 \
  --max-lake 1 \
  --no-persistent-elaborator \
  --no-submit \
  --submit-top-k 0
```

The expected smoke result is `Lake attempts: 1`, `Lake passed: 1`, and the `E = m·c² SPONTANEOUSLY DERIVED AND VERIFIED` banner. This uses upstream SR postulates and confirms `mass_shell_condition` is not loaded as an axiom.

**Local quantum smoke.** To prove the same GA/RL/Lake path can run a quantum target locally, run:

```bash
just smoke-qm-local
```

Expected result: one Lake attempt, one Lake pass, and the `QUANTUM PLANCK-EINSTEIN RELATION DERIVED AND VERIFIED` banner. This runs `--domain qm --target qm_planck_einstein` with no API submission and the same low-LLM local profile.

The featured quantum ladder also has a local Schrödinger anchor:

```bash
cd engine
PATH="$HOME/.elan/bin:$PATH" NASRUDIN_NO_PAID_JOBS=1 cargo run -p nasrudin-ga --bin worker -- \
  --domain qm \
  --target qm_schrodinger \
  --verify ../prover \
  --gens 1 \
  --pop 8 \
  --chunks 1 \
  --max-lake 1 \
  --no-persistent-elaborator \
  --no-submit \
  --submit-top-k 0
```

Expected result: one Lake attempt, one Lake pass, and a verified theorem whose chain starts from `qm_schrodinger_evolution`.

**Local auto-target smoke.** To prove the RL target portfolio can choose a target while the GA remains the workhorse, run:

```bash
just smoke-auto-qm-local
```

Expected result: the worker logs `Auto-target RL selected 'qm_planck_einstein'`, then one Lake attempt, one Lake pass, and the same quantum verification banner. The recipe uses a temporary `NASRUDIN_WORKER_RL_STATE` file so the run demonstrates cold-start target selection rather than reusing local history.

**Local featured-ladder smoke.** To prove the local auto-target curriculum advances across featured QM targets, run:

```bash
just smoke-featured-qm-local
```

Expected result: the first run logs `featured 0/2 proved`, selects `qm_planck_einstein`, and verifies `Eph = hbar * omega`; the second run reuses the same temporary RL state, logs `featured 1/2 proved`, selects `qm_schrodinger`, and verifies a chain starting from `qm_schrodinger_evolution`.

To test the same featured-first policy used by the default laptop-origin worker in `just up`, run:

```bash
just smoke-featured-all-local
```

Expected result: the first run uses `--domain all --target auto`, selects `sr_rest_energy`, and verifies `E = m·c²`; the second run reuses the same temporary RL state, logs `featured 1/7 proved`, selects `qm_planck_einstein`, and verifies `Eph = hbar * omega`.

**Verifier-budget policy.** Lake/Lean calls are treated as scarce evaluator budget. When a target is active, the worker now ranks proof attempts by target completion before generic novelty, prefers shorter proof contexts, and pre-rejects chains whose introduced axiom context contains formalization plumbing symbols. This keeps the GA/RL workhorse from spending the only verifier slot on unrelated Mathlib scaffolding when a clean target-complete chain is available.

**LLM prompt-budget policy.** LLM steering calls are sparse strategy updates, not search steps. Before the steerer builds its user prompt, recent worker cluster reports are passed through a lossy evidence condenser: it keeps reward, fitness, target-progress, verifier, QD/archive, and mutation-operator evidence, while dropping raw populations, example chains, Lean source, stdout/stderr, and log blobs. This keeps the 10k-token / 2h ceiling available for high-level strategy genomes and curriculum choices instead of accidental telemetry dumps.

The budget cap is enforced twice: first by conservative prompt estimation before the call, then by a rolling `cluster_steering` usage ledger using provider-reported prompt and completion tokens. Budget refusals persist a validation-failed strategy marker with no token counts, so operators can distinguish "no LLM spend because budget exhausted" from normal RL-only cycles.

The evidence gate is separate from the hard token ledger. `LLM_STEER_MIN_CLUSTER_REPORTS=1` means "do not call the LLM just because two hours passed; wait until workers have produced new cluster telemetry." Paid active jobs bypass the gate because the steerer may need to rebalance prerequisites for the job domain. Set `LLM_STEER_MIN_CLUSTER_REPORTS=0` only if you intentionally want the older timer-driven behavior.

The steerer also has a local-RL confidence skip enabled by default (`LLM_STEER_SKIP_IF_RL_CONFIDENT=1`). When recent cluster summaries contain compact `rl_policy_evidence` showing both the GA workhorse policy and target-selector policy are no longer low-sample and are clearing the configured conservative-score and Lake-pass thresholds, a due strategy refresh is skipped and the worker keeps running RL/GA-only. Tune `LLM_STEER_RL_CONFIDENT_MIN_REPORTS`, `LLM_STEER_RL_CONFIDENT_MIN_EPISODES`, `LLM_STEER_RL_CONFIDENT_MIN_SCORE`, and `LLM_STEER_RL_CONFIDENT_MIN_LAKE_PASS_RATE` if the laptop is spending too often or waiting too long before asking the LLM for a new high-level move.

Admins can inspect current LLM steering spend without triggering a provider call:

```bash
curl -H "Authorization: Bearer $ADMIN_TOKEN" http://localhost:3001/api/admin/steering/budget
```

The response reports the configured strategy interval, rolling token window, max tokens, provider-reported tokens used, remaining tokens, latest strategy-attempt metadata, and whether the interval is currently open. Use this endpoint on the local origin before long unattended runs to confirm the steerer is staying under the 10k-token/2h ceiling.

**Auto-target RL policy.** `--target auto` / `NASRUDIN_AUTO_TARGETS=1` uses a nonstationary verifier-aware portfolio controller. Cold targets are tried first; after that, a local meta-controller chooses among target-scoring policies (`verifier_ucb`, `recent_verifier`, `novelty_seeker`, `stall_rescue`) using prior verifier reward, then the selected policy scores targets from lifetime reward, recent reward EMA, recent Lake pass EMA, novelty EMA, UCB exploration, and stall signals. This is the inner "how to search" RL layer; it does not call the LLM. Tune `NASRUDIN_TARGET_RL_EMA_ALPHA` to control how quickly target choice reacts to recent verifier outcomes. Tune `NASRUDIN_TARGET_RL_STALL_THRESHOLD` to control how many consecutive no-proof chunks a target gets before it is reported as stalled and skipped so it cannot block frontier/novelty search forever. Tune `NASRUDIN_TARGET_RL_STALL_RETRY_SECONDS` to control when a stalled featured theorem re-enters priority; corpus-size drift also makes it eligible again because new local discoveries may have changed the proof landscape.

**GA workhorse RL policy.** Every background chunk also selects a local GA policy (`steady_verify`, `wide_explore`, `deep_recombine`, `mutation_sweep`, `lake_focus`) from persisted verifier reward. The selected policy makes bounded changes to population size, mutation rate, crossover rate, tournament pressure, max chain depth, and Lake budget before the GA runs. This is the workhorse equivalent of test-time compute scaling: the LLM can still provide rare high-level steering, but the laptop worker learns the per-chunk "how hard and in what style should I search?" decision locally from Lake/verifier feedback.

**RL episode replay buffer.** Each background chunk appends a compact JSONL episode beside the worker RL state by default (`worker_rl_episodes.jsonl`, override with `NASRUDIN_RL_EPISODE_LOG_PATH`). The row records observation/action/reward data: domain, target, selected target policy, GA policy, strategy genome fingerprint/weight, replay elite ids, effective GA hyperparameters, verifier metrics, verified canonicals, and scalar reward. This is the offline RL substrate for later policy evaluation or training; it intentionally excludes raw Lean source, stdout/stderr, and full populations. The worker automatically compacts the log after scheduled evaluation refresh, keeping the newest `NASRUDIN_RL_EPISODE_LOG_MAX_LINES` rows (default 100000, set 0 to disable) so unattended laptop-origin runs do not grow the replay buffer forever.

The worker automatically refreshes a compact policy-ranking snapshot beside the log by default (`worker_rl_episode_eval.json`, override with `NASRUDIN_RL_EPISODE_EVAL_PATH`) on a cooldown (`NASRUDIN_RL_EPISODE_EVAL_INTERVAL_SECONDS`, default 1800). That means the local origin continuously maintains ranked GA policies, target-selector policies, strategy genomes, and domain/target curriculum choices from verifier rewards without a human, cron job, or LLM call. The snapshot reports recency-weighted means, UCB exploration scores, conservative lower-confidence scores, Lake pass rates, and low-sample warnings. The worker also reads the latest snapshot back as an exploitation prior for GA workhorse policy choice, target-selector policy choice, domain/target scoring inside the currently allowed curriculum tier, and LLM strategy-genome strength after each policy family has received local evidence, preserving exploration while letting offline verifier evidence steer later chunks automatically. The manual CLI remains only for inspection/debugging: `cargo run -p nasrudin-ga --bin rl_episode_eval -- ~/.local/share/nasrudin-worker/worker_rl_episodes.jsonl`. This keeps policy analysis local and token-free: the LLM sees only condensed strategic evidence, not the raw replay log.

**Verified-chain replay archive.** When local Lake verification is enabled, every verified discovery is stored in the worker's scoped RL state as a bounded replay elite. Future chunks inject prioritized proof-backed chains as elite seeds before random mutation/crossover starts. This is the local analogue of an AlphaEvolve archive: successful derivation programs are reused and mutated without another LLM call. Replay entries track pulls, reward EMA, best reward, and last replay time from later chunk outcomes, so the worker learns which verified derivations are actually useful as reusable stepping stones instead of replaying only the newest chain. Credit assignment is descendant-aware: exact replay hits get full credit, verified chains that extend a replayed prefix get strong credit, and unrelated chunk success gives only fallback credit. `NASRUDIN_REPLAY_ELITE_ARCHIVE_LIMIT` caps persisted memory, and `NASRUDIN_REPLAY_ELITES_PER_CHUNK` caps how many archived chains enter a chunk. The archive does not learn from `--no-local-lake` harvested candidates because those still need server-side verification.

**Featured-first curriculum.** Production workers claim platform conjecture jobs before background discovery, so the API queue prioritizes the featured physics rediscoveries first. Local/full-auto workers mirror that behavior: `--target auto` ranks unproved featured targets ahead of frontier targets, persists a per-target `proved` bit only when a verified theorem matches the built-in target spec, then falls through to frontier targets and finally untargeted novelty search once the featured curriculum is exhausted. This gives the system a visible proof ladder: rediscover known physics first, then travel beyond it.

For local unattended deployment, keep `NASRUDIN_WORKER_RL_STATE` on a persistent path and run workers with `--target auto` / `NASRUDIN_AUTO_TARGETS=1`. The target portfolio state is what carries "featured theorem already proved" across worker restarts and lets the next run advance the curriculum instead of re-proving the same headline.

In auto-target mode, worker startup logs include `Auto-target curriculum: featured X/Y proved; pending featured: ...; stalled featured: ...; pending frontier: ...` and the chosen target log includes `policy=...`. Each chunk also logs `GA workhorse policy=...` with the actual population, generation, mutation, crossover, tournament, chain-depth, and Lake settings used for that chunk. Treat this as the runtime audit trail: featured pending drains first, stalled featured targets have exceeded the local no-proof threshold and temporarily stop blocking progress, frontier pending starts after featured targets are proved or currently stalled, and `curriculum exhausted` means the worker has intentionally fallen through to untargeted novelty search. Stalled featured targets are retried after `NASRUDIN_TARGET_RL_STALL_RETRY_SECONDS` or after corpus-size drift.

Featured seed coverage currently includes SR rest energy, Planck-Einstein, Schrödinger, Boltzmann entropy, Newton's second law, and the no-cosmological-constant Einstein field equation. Gauss's law remains featured but has no permanent elite until the upstream EM store has a clean `div_E`, `rho`, and `epsilon_0` postulate path.

## Reinforcement-Learning Layer

The LLM emits *intent* (which clusters to focus on, when to spend more compute, which physics targets to chase). Four bandits handle the *numerical optimisation* — given the LLM's intent, which actual multiplier values produce more verified discoveries. The bandits train online from worker reward signals, no GPU, no offline pipeline:

| Bandit | What it learns | Action space | Storage |
|---|---|---|---|
| **K-bandit** (UCB1) | Number of K-means clusters per island | K ∈ {2,3,4,5,6,7,8,10,12} | `cluster_bandit_arms` |
| **Directive bandit** (UCB1 + LinUCB) | Multiplier per (action, strength) for each LLM directive | 9 × 5 × 4 actions per island | `cluster_directive_arms` + `cluster_directive_linucb` |
| **Compute bandit** (UCB1) | Population_size & generations multiplier | {0.5×, 0.75×, 1×, 1.5×, 3×, 3.5×, 4×, 4.5×, 5×} | `cluster_compute_arms` |

All bandits use **UCB1** for exploration vs exploitation. The directive bandit also runs a **pure-Rust LinUCB** contextual layer (hand-coded 6×6 ridge regression) that generalises across the (strength, choice) plane — a pull at strength=0.5 informs neighbouring strengths via Bayesian linear regression, not just the discrete arm. Updates are rank-1, ~120 flops, microseconds per pull.

**Reward attribution** uses **eligibility traces with γ=0.7 over a 3-chunk horizon**: each directive applies → its matched cluster's mean fitness is sampled at chunks N, N+1, N+2 → the γ-discounted return drives the bandit. This averages out single-chunk noise. **Intrinsic motivation** adds a capped novelty bonus (≤0.10) for directives applied to rarely-seen cluster lineages, encouraging exploration of new structural patterns.

**Online action expansion.** When a bandit's outermost arm dominates with high confidence (≥30 pulls, ≥0.65 mean reward), the next-finer-grained arm is materialised lazily — the action space grows past the spec author's initial guess.

**Self-curriculum.** The LLM proposes physics targets via `soft_targets` with stable `target_id` strings; targets persist in `llm_proposed_targets` with a {open → proving → proved | abandoned} lifecycle. Subsequent cycles surface in-flight targets in the prompt so the LLM tracks its own curriculum across days, not just the 10-cycle history.

**Replay buffer.** Every reward observation is also written to `directive_pull_events` (raw event log, 30-day retention). The aggregate path keeps the live bandit responsive; the event log preserves per-pull data for any future offline analysis.

The system is fully autonomous: every `/api/directive-feedback` POST trains the model inline as a side effect, no scheduled jobs, no batch training, no manual ops. As you swap in stronger LLMs over time (`STEERER_MODEL` env var), the intent quality improves and the bandits' job gets easier — the curriculum compounds, the corpus grows, and the search converges on more original physics.

## Project Structure

```
nasrudin/
├── engine/                  # Rust workspace (7 crates)
│   ├── crates/
│   │   ├── core/            # Expr AST, Dimension types, Theorem, xxHash IDs
│   │   ├── rocks/           # RocksDB embedded theorem store (9 column families)
│   │   ├── pg/              # SeaORM 2 PostgreSQL (users, auth, workers)
│   │   ├── lean-bridge/     # C ABI FFI bridge to Lean4 prover
│   │   ├── api/             # Axum HTTP server (REST + SSE + WebSocket)
│   │   ├── mcp/             # MCP server for LLM-guided exploration
│   │   └── importer/        # Mathlib/Metamath/PhysLean ingestion
│   └── Cargo.toml           # Workspace root
├── prover/                  # Lean4 formal verification
│   ├── PhysicsGenerator/
│   │   ├── Axioms/          # Formalized physics (mechanics, SR, EM, QM, thermo)
│   │   └── Bridge/          # FFI exports (pg_init, pg_verify, pg_shutdown)
│   ├── lakefile.lean
│   └── lean-toolchain       # Lean4 v4.27.0
├── nasrudin-frontend/       # TanStack Start v1 web UI (React 19, TS, Biome)
│   └── src/
│       ├── routes/          # /, /browse, /theorem/$id, /signin, /profile,
│       │                    # /api-keys, /api-docs, /leaderboard, /pricing
│       ├── components/      # platform shell, landing, browse, theorem, auth, apikeys
│       ├── lib/             # apiFetch, queries, types, katex helper
│       └── styles/          # tokens.css, styles.css, platform.css
├── docs/                    # Design documents
│   ├── PLAN.md              # Master plan
│   ├── ARCHITECTURE.md      # System diagrams
│   ├── DATA-MODEL.md        # Type definitions (Rust + TypeScript)
│   ├── PHYSICS-AXIOMS.md    # All 43 physics axioms formalized
│   ├── LEAN4-BRIDGE.md      # FFI specification
│   ├── FRONTEND.md          # UI architecture
│   └── LLM-INTEGRATION.md  # MCP + LLM-guided exploration
├── justfile                 # Cross-ecosystem task runner
└── pnpm-workspace.yaml      # Monorepo config
```

## Getting Started

### Prerequisites

- **Rust** 1.92+ (`curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh`)
- **Lean4** v4.27.0 (`curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh`)
- **Node.js** 22+ and **pnpm** 9+ (`corepack enable && corepack prepare pnpm@latest --activate`)
- **PostgreSQL** 18 (for user accounts -- workers don't need this)
- **Docker** (optional, for easy PostgreSQL setup)

### Run the Server

```bash
# 1. Start PostgreSQL
just db-start

# 2. Build and run the Rust engine + API server
just dev-engine
# -> Axum API on http://localhost:3001

# 3. Start the frontend
just dev-frontend
# -> TanStack Start on http://localhost:3000
```

### Run as a Worker

Download the latest release binary for your platform, then:

```bash
# Connect to the Nasrudin network. By default the worker contributes
# to paid-Researcher compute alongside background research — the
# platform is sustained by paying customers, so spare capacity helps
# pay the bills.
./nasrudin-worker --server https://nasrudin.org

# Background research only (skip paid jobs):
./nasrudin-worker --server https://nasrudin.org --no-paid-jobs

# Legacy LLM-guided FunSearch flow:
./nasrudin-worker --server https://nasrudin.org --research-mode
```

The worker binary bundles the Rust GA engine and Lean4 prover. It runs locally on your machine, generates and verifies theorems, and submits discoveries to the central server. Your local RocksDB persists across restarts so no work is lost.

The 96 slot-hour quota per paid job and the cluster's 10 % explorer floor mean a vanilla worker still spends the bulk of its compute on background research even with paid-jobs enabled — paid claims are gated server-side so they can never starve the explorer fleet.

**What workers do each chunk** (a chunk is a few generations of GA, roughly 30–60 s):

1. **Try a paid claim first** (default; suppress with `--no-paid-jobs`). POST `/api/jobs/claim` with the worker's currently-available lake slots. On award, hand the entire chunk to the paid-slice runner — it heartbeats every 30 s with deltas (candidates attempted, candidates verified, slot-hours consumed) and on a kernel-verified theorem calls `/api/jobs/{id}/mark_proved`.
2. **Otherwise**, sync from `/api/seed`: pull any new peer-verified theorems into the local AxiomStore, refresh the `rejected_canonicals` memo (so we skip lake-builds the cluster has already failed), and read the current `SteeringConfig`.
3. **Run a chunk of GA** under the active config and submit kernel-verified discoveries to `/api/ingest`.

### Build Everything

```bash
just build           # Build frontend + engine + prover
just test            # Run all tests
just check           # Lint and typecheck
just clean           # Remove all build artifacts
```

## Tech Stack

| Layer | Technology | Version |
|-------|-----------|---------|
| **GA Engine** | Rust | 2024 edition |
| **Formal Prover** | Lean4 + Mathlib | v4.27.0 |
| **Theorem Store** | RocksDB (embedded) | 0.24 |
| **User Database** | PostgreSQL + SeaORM 2 | 18 / 2.0.0-rc |
| **API Server** | Axum | 0.8 |
| **Frontend** | TanStack Start + React 19 | v1 |
| **Math Rendering** | KaTeX | 0.16 |
| **Graph Canvas** | React Flow | 12 |
| **LLM Integration** | MCP (Model Context Protocol) | -- |
| **Cluster Steerer** | Latest GLM via DigitalOcean Gradient | auto from `/v1/models` |

## The GA Engine

The genetic algorithm evolves mathematical expressions using an **island model** where each island focuses on a physics domain (mechanics, electromagnetism, quantum mechanics, special relativity, thermodynamics, general relativity).

**Selection**: NSGA-II multi-objective optimization balancing proof depth, novelty, dimensional correctness, and domain coverage.

**Crossover**: Subtree exchange between two parent expressions, guided optionally by LLM suggestions (FunSearch pattern).

**Pre-filters** reject candidates before they reach Lean4:
- Dimensional analysis (SI 7-tuple type system)
- Deduplication (xxHash64 + Bloom filter)
- Complexity bounds (max AST node count)
- Fast type checking

Only candidates that pass all pre-filters are sent to Lean4 for formal verification.

## Dual Database Design

| Database | Purpose | Access Pattern |
|----------|---------|----------------|
| **RocksDB** | Theorems, proofs, lineage graphs, indexes | Embedded in Rust process -- zero-latency for the GA write loop |
| **PostgreSQL** | Users, sessions, saved searches, worker metadata | Network-accessible for distributed workers and the web UI |

Workers maintain their own local RocksDB. When a worker discovers a verified theorem, it POSTs to the server's `/api/ingest` endpoint. The server re-verifies with its own Lean4 instance and, if valid, adds the theorem to the global RocksDB.

## Contributing Compute

Nasrudin is designed so anyone can contribute. When you run a worker:

1. The binary starts the Rust GA engine and Lean4 prover on your machine
2. It fetches the current axiom set and seed theorems from the server
3. Your machine generates candidate theorems via genetic algorithms
4. Lean4 formally verifies each candidate locally
5. Verified theorems are submitted to the central server
6. The server re-verifies before accepting (double verification)
7. Your contribution is tracked and attributed

All theorem generation and verification happens on your hardware. The server only receives pre-verified results and confirms them.

## Admin panel

`https://nasrudin.org/admin` (gated by `users.is_admin`). After your
first deploy, sign in once via Firebase, then promote yourself:

```
NASRUDIN_DATABASE_URL=postgres://... \
  deploy/scripts/admin-bootstrap.sh you@example.com
```

Capabilities: user CRUD (plan tier, credits, trust toggle, per-key
trust override), API-key revoke, conjecture-job cancel, Stripe refunds
with reconciler crash recovery, user impersonation (HMAC-signed,
15 min default), bulk operations with SSE progress, audit log,
existing `reload_corpus` / `steering/force` endpoints. Every mutation
writes a transactionally-bound audit row with required reason ≥ 10
chars. Full runbook in [`docs/admin/runbook.md`](docs/admin/runbook.md).

## Trust bypass

`users.is_trusted = true` (or `api_keys.trust_override = true`) skips
the redundant server-side `lake build` confirmation for that
contributor's submissions. Sampled spot-check (1-in-N, env default 50)
preserves cascade-reject and reputation-EMA safety.

The local-droplet worker auto-trusts via a unix-domain socket at
`/run/nasrudin/api-local.sock` — Caddy proxies only TCP, so the socket
is private to processes on the host. The worker reads
`NASRUDIN_API_URL=unix:///run/nasrudin/api-local.sock`.

## Paid Researcher Tier

The $19/mo Researcher tier turns Nasrudin into a **research assistant**: hand the system a specific conjecture you can't prove, and a slice of the GA cluster will try to evolve a Lean 4 proof of that statement for up to 24 hours.

```
User submits hunch ──> POST /api/research/jobs (one credit debited atomically)
                              │
                              v
                       conjecture_jobs row queued
                       (96 lake-slot-hour quota,
                        4 slots × 24 h)
                              │
              workers polling /api/jobs/claim with FOR UPDATE SKIP LOCKED
                              │
                              v
                       Paid GA slice runs on N worker(s)
                              │
                       heartbeat every 30 s ──> /api/jobs/{id}/heartbeat
                       (server clamps slot-hour delta at
                        2 × wallclock × slots_held to defeat
                        a worker that lies about its progress)
                              │
                ┌─────────────┴────────────┐
                │                          │
       kernel-verified theorem      budget exhausted (96h reached)
                │                          │
                v                          v
       POST /api/jobs/{id}/mark_proved   release; SSE BudgetExhausted
       state='proved'                   state='budget_exhausted'
```

**Capacity policy.** Every paid job has a hard cap of **96 lake-slot-hours** (4 slots × 24 h). The cluster always reserves at least 10 % of total worker slots (or a minimum of 2) for the explorer fleet — the claim path runs `floor_satisfied(total, paid + new_claim)` before awarding any job, so paid load can never starve background research. Excess paid jobs queue on `slice_priority DESC, created_at ASC` until capacity frees up.

**Refund rule.** A credit is refunded only if the run produced **zero verified results AND fewer than 1000 candidates attempted** (the user's hunch genuinely got no traction). Anything past those thresholds is "value delivered" — partial chains are published as ChainVerified theorems under the user's attribution and the credit stays consumed.

**Live progress.** Every paid job has a per-job SSE stream at `/api/research/jobs/{id}/events` carrying `Progress`, `TheoremVerified`, `Proved`, `BudgetExhausted`, and `Cancelled` events. The user's dashboard subscribes once when they open a job and watches it run live.

**Resilience.** Each claim grants a 5-minute lease, refreshed by every heartbeat. If a worker dies mid-grind the lease falls into the past and the reaper task (running every 60 s) requeues the job — another worker picks it up within seconds, no human intervention.

The Researcher tier also includes 10K API requests/day and unlimited corpus access. Submit a paid conjecture from the [Pricing](https://nasrudin.org/pricing) page once you're signed in.

## Support

The corpus is open by principle and built by volunteer worker compute. What it costs us to run — central Lean4 re-verification, the embedding index, hosting, ingest, the engineering time that keeps all of it improving — is funded by sponsorships.

If Nasrudin is useful to you, sponsor it: **https://nasrudin.org/sponsor** (Stripe-hosted, $5/mo and up; one-time gifts also welcome).

Sponsorship is a donation, not a subscription tier — it doesn't grant Researcher quota. If you need targeted GA compute pointed at your own conjecture, see the **Paid Researcher Tier** section above and the [Pricing](https://nasrudin.org/pricing) page.

## License

AGPL-3.0. See [`LICENSE`](./LICENSE).

The platform has a SaaS component (`api.nasrudin.org`) — the network-use clause means anyone running modified versions as a hosted service must publish their changes.

## Cutting a worker release

All cross-platform worker binaries are built locally on macOS via `just`; we do not use GitHub Actions for release builds.

```bash
# release-worker requires a clean tree — stash any in-flight work first:
git stash push -u -m "pre-release-WIP"

# Cut the release. Cross-compiles the worker binary for Linux x86_64/aarch64,
# macOS x86_64/arm64, and Windows x86_64 locally via cargo-zigbuild, then
# uploads everything to a GitHub release.
just release-worker v0.1.0

# Pop your in-flight work:
git stash pop
```

Prerequisites: `zig` and `cargo-zigbuild` installed (`brew install zig && cargo install cargo-zigbuild`); `gh auth status` shows write access to `Nasdin/nasrudin`. The recipe will add any missing rustup targets automatically.
