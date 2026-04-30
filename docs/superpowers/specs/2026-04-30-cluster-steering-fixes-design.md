# LLM Cluster Steering — Audit Fixes & Genotype Clustering Design

**Date:** 2026-04-30
**Phase:** Post Phase 9 cluster-steerer + paid-researcher (`docs/superpowers/specs/2026-04-30-cluster-steerer-and-paid-research-design.md`).
**Status:** Brainstorming complete; awaiting user spec review.

---

## Goal

Close the gaps surfaced by the 2026-04-30 LLM-steering audit. The audit found steering is wired end-to-end and PhysLean+Mathlib are extracted into 1,907 + 13,532 entries used as GA building blocks, but five gaps remain:

1. **No genotype clustering** — "cluster steering" today means *worker-cluster coordination* (global), not population clustering by similarity. The LLM cannot tell stagnant sub-populations from productive ones.
2. **No end-to-end integration test** for steering — only parse/validate is covered.
3. **Mathlib loading is soft-optional** — `tracing::warn!` on missing/empty file. User wants Mathlib as a hard dependency.
4. **`mutation_priors`** is fully plumbed through the GA (`chain_ga.rs:111-141`) but the LLM cannot emit it — schema field, validation, prompt hint missing.
5. **CLAUDE.md** marks `importer` as `[STUB]`; importer is functional.

After this spec, the LLM has a true cluster-aware view of the GA population, can emit per-cluster directives, and the number-of-clusters K is auto-learned per island via UCB1 — no hardcoded constants.

## Non-goals

- Replacing the 6-domain island topology. Clustering is *within* islands.
- Replacing UCB1 with deep-RL. UCB1 is the right shape for low-cardinality scalar arms with bounded reward.
- Auto-learning the cluster directive strength caps. Safety guardrails stay constant.
- Removing the existing `mutation_knobs` (population-level). Cluster directives multiply on top.
- Streaming cluster updates. `POST /api/cluster-report` is per-chunk, not real-time.

---

## Component map

```
┌──────────────────────────────────────────────────────────────────────┐
│ Worker (engine/crates/ga/src/bin/worker.rs)                           │
│                                                                        │
│  per chunk:                                                           │
│    1. run_discovery (existing)                                        │
│    2. NEW: cluster_population(individuals, K_chosen) ──┐              │
│    3. NEW: compute_cluster_summaries(clusters)         │              │
│    4. POST /api/cluster-report ── ClusterReport ──────┐│              │
│    5. fetch /api/seed (existing) ─ steering JSON ────┐││              │
│    6. apply_steering_knobs (existing, extended)      │││              │
│    7. NEW: apply_cluster_directives(cluster_dirs)    │││              │
│    8. NEW: apply_mutation_priors_from_steering       │││              │
└──────────────────────────────────────────────────────┼┼┼──────────────┘
                                                      │││
┌─────────────────────────────────────────────────────▼▼▼──────────────┐
│ API daemon (engine/crates/api)                                        │
│                                                                        │
│  POST /api/cluster-report ── handler ── upsert into                   │
│      cluster_reports table                                            │
│                                                                        │
│  steerer cycle (every 600s):                                          │
│    1. read latest cluster_reports for previous K_per_island            │
│    2. compute reward per (island, K_prev); update_arm(...)            │
│    3. UCB1::select_k(island) → K_next per island                      │
│    4. build_prompt: + cluster_summaries + bandit_state + K_next       │
│    5. LLM call (existing)                                             │
│    6. parse + validate (existing, schema extended)                    │
│    7. persist; ArcSwap pushes BOTH steering and cluster_config        │
└──────────────────────────────────────────────────────────────────────┘
```

---

## Part 1 — Genotype clustering inside islands

### Feature vector

Per individual, a deterministic 4-component projection:

```rust
pub struct ClusterFeatures {
    pub axiom_usage: SparseVec<u32>,      // axiom_id → count from IntroduceAxiom steps
    pub op_skeleton: [u32; 6],            // count per RuleStep variant in MUTATION_OPS order
    pub skeleton_bucket: u32,             // skeleton_hash(chain) modulo K (init partition)
    pub fitness_components: [f32; 4],     // (novelty, dim_elegance, length_penalty, target_proximity)
}
```

All four are reproducible from a `Chain` + `Theorem` already in scope inside `engine/crates/ga/src/island.rs`. No new state needed on the individual.

### K-means with auto-K

Algorithm: K-means++, max 20 iterations, deterministic seeding from `(chunk_index, island_domain)` hash.

Distance: weighted L2 over normalized features. Axiom usage uses Jaccard distance via min-hash signature (cheap; converts the sparse vector to a 16-byte signature).

K is **not** chosen by the GA, **not** chosen by the LLM. The API steerer's UCB1 bandit (next section) chooses K per island independently of the LLM emission and ships it through `/api/seed` as a sibling field of `steering`:

```json
{
  "axioms": [...],
  "steering": { "config": <SteeringConfig>, "etag": ... },
  "cluster_config": { "k_per_island": { "special_relativity": 6, "electromagnetism": 4, ... }, "etag": ... }
}
```

The worker reads `cluster_config.k_per_island[domain]`, runs k-means with that K, returns summaries via `POST /api/cluster-report`. The bandit and the LLM are decoupled: bandit handles structural decisions (how many clusters), LLM handles tactical decisions (what to do with each cluster).

### Cluster summary (worker → API)

```rust
pub struct ClusterSummary {
    pub cluster_id: u32,                   // island-local
    pub size: u32,
    pub mean_fitness: f32,
    pub fitness_stddev: f32,
    pub silhouette: f32,                   // [-1, 1], higher = better-separated
    pub dominant_axioms: Vec<(String, u32)>, // top-5 by frequency
    pub novelty_trend: f32,                // chunk-over-chunk delta of mean novelty
    pub stagnation_chunks: u32,            // consecutive chunks with no new Pareto-front entry
    pub centroid_skeleton_hash: u64,       // for cluster identity tracking across chunks
}
```

Per-chunk size is bounded: 6 islands × ≤12 clusters × ~200 bytes ≈ 14 KB per worker per chunk. Trivial.

---

## Part 2 — UCB1 bandit for K

### Per-island arm state

```rust
pub struct BanditArm {
    pub island_domain: String,
    pub k_value: u8,        // ∈ {2, 3, 4, 5, 6, 7, 8, 10, 12}
    pub pulls: u64,
    pub total_reward: f64,
    pub last_reward: f64,
    pub updated_at: DateTime<Utc>,
}
```

Persisted in new PG table `cluster_bandit_arms` (PK `(island_domain, k_value)`).

### Selection — UCB1

```
ucb_score(arm) = (total_reward / pulls) + sqrt(2 * ln(N_island) / pulls)
                  ↑ exploitation                 ↑ exploration

choose_k(island) =
    if any arm has 0 pulls → that arm (cold start)
    else                   → argmax over arms of ucb_score
```

Deterministic. No ε to tune.

### Reward signal

Computed by the steerer at cycle close (alongside `compute_outcome`):

```
reward(island, K_t) =
    w_v * verified_per_pop      // 0.40
  + w_s * mean_silhouette       // 0.25
  + w_n * novelty_delta         // 0.20
  - w_g * stagnation_penalty    // 0.15

clamp to [0.0, 1.0]
```

Inputs come from the latest `cluster_reports` rows for that island in the cycle window. Weights are constants in `engine/crates/api/src/steerer/bandit.rs` — *not* LLM-steerable (would create reward hacking).

### Stagnation threshold (auxiliary online learner)

Per (island, cluster_id), track an EWMA of novelty deltas with α=0.3. A cluster is "stagnant" when EWMA < (per-island mean - 1 stddev). Threshold updates per chunk; no separate state table — derived on-the-fly from the last N `cluster_reports` rows.

---

## Part 3 — LLM emission: cluster_directives + mutation_priors

### Schema additions to `SteeringConfig`

```rust
pub struct SteeringConfig {
    // ... existing fields ...

    /// Per-operator weight overrides for mutation. Keys must be in
    /// MUTATION_OPS; unknown keys silently ignored. Each value
    /// in [0.0, 2.0]. Empty/missing → uniform fallback.
    /// (Fully plumbed in chain_ga.rs since Phase E; LLM was not
    /// previously asked to emit this.)
    pub mutation_priors: HashMap<String, f32>,

    /// Per-cluster steering. Empty in scope=B (paid jobs running).
    pub cluster_directives: Vec<ClusterDirective>,
}

pub struct ClusterDirective {
    pub island_domain: String,
    /// Identifies the cluster by its centroid skeleton hash from the
    /// previous chunk's ClusterSummary — NOT by cluster_id, because
    /// k-means re-numbers clusters every chunk. Worker matches new
    /// clusters to directives by minimum hash distance (Hamming on
    /// the skeleton-hash bits) with a max-distance threshold; if no
    /// new cluster is close enough, the directive is dropped.
    pub centroid_skeleton_hash: u64,
    pub action: ClusterAction,
    pub strength: f32,                    // [0.0, 1.0]
}

pub enum ClusterAction {
    Boost,        // multiply mutation rate for this cluster
    Exploit,      // multiply elitism for this cluster
    Diversify,    // re-seed the worst N% with random + axiom samples
    Kill,         // drop a fraction of the cluster, refill from migrants
}
```

### Validation

- `mutation_priors` values ∈ [0.0, 2.0]; keys must be subset of `MUTATION_OPS` (unknown → warn, not reject).
- `cluster_directives` must be empty when `scope == "B"` (new validation error `BHasClusterDirectives`).
- `strength` ∈ [0.0, 1.0].
- `centroid_skeleton_hash` is referenced from a `ClusterSummary` the LLM saw in the prompt; if the next chunk's k-means produces no cluster within the matching threshold, the worker drops the directive with a warning. The cycle still validates.

### Worker application — strength → multiplier

Bounded multipliers prevent the LLM from wedging the GA:

| Action     | Strength → effect                              |
|-----------|-----------------------------------------------|
| Boost     | mutation_rate *= 1.0 + 1.0 * strength  (≤2×) |
| Exploit   | elitism_fraction *= 1.0 + 1.0 * strength (≤2×) |
| Diversify | reseed bottom (0.3 * strength) of cluster      |
| Kill      | drop (0.5 * strength) of cluster, refill from migrants |

All multipliers compose with the global `mutation_knobs` (e.g., a Boost cluster's effective rate is `global_rate * cluster_multiplier`, then clamped to existing GA bounds).

---

## Part 4 — `POST /api/cluster-report`

### Endpoint

```
POST /api/cluster-report
Authorization: Bearer <worker_token>
Content-Type: application/json

{
  "worker_id": "uuid",
  "chunk_index": 1234,
  "k_used": 6,
  "island_reports": [
    { "island_domain": "special_relativity", "summaries": [<ClusterSummary>, ...] },
    ...
  ]
}

→ 200 {"received": true, "stored": 6}
```

### Storage

New PG table:

```sql
CREATE TABLE cluster_reports (
    id          BIGSERIAL PRIMARY KEY,
    worker_id   UUID NOT NULL,
    chunk_index BIGINT NOT NULL,
    k_used      SMALLINT NOT NULL,
    island_domain TEXT NOT NULL,
    cluster_id  SMALLINT NOT NULL,
    summary     JSONB NOT NULL,           -- ClusterSummary
    received_at TIMESTAMPTZ NOT NULL DEFAULT now()
);

CREATE INDEX cluster_reports_recent
    ON cluster_reports (island_domain, received_at DESC);

CREATE INDEX cluster_reports_chunk
    ON cluster_reports (worker_id, chunk_index);
```

Rate-limited (≤ 1 report per worker per chunk; chunk index dedup at the table level).

Retention: 7 days. Cron deletes older rows; bandit arm state retains the long-running statistics.

### Auth

Reuses the existing worker bearer-token middleware (`engine/crates/api/src/auth.rs`). Workers already authenticate for `/api/ingest` — same token, same middleware.

---

## Part 5 — Mathlib hard-required

### Change in `engine/crates/api/src/main.rs:117-121`

```rust
const MATHLIB_MIN_ENTRIES: usize = 10_000;

let math_count = axiom_store
    .load_math_corpus(&math_corpus_path)
    .unwrap_or_else(|e| {
        panic!(
            "Mathlib corpus REQUIRED at boot. Failed to load {}: {e}\n\
             Run `just extract-mathlib` first.",
            math_corpus_path.display()
        )
    });

if math_count < MATHLIB_MIN_ENTRIES {
    panic!(
        "Mathlib corpus too small ({math_count} entries, need ≥{MATHLIB_MIN_ENTRIES}). \
         Re-run `just extract-mathlib` — corpus appears truncated."
    );
}
tracing::info!("Loaded {math_count} Mathlib identities");
```

### Bootstrap chain

`justfile`: add `bootstrap` recipe that runs `extract-physlean → extract-mathlib → start-api` in order, and update `start-api`'s pre-checks to verify both files exist before exec.

### CI / dev path

Update `README.md` quickstart to call `just bootstrap`. Existing CI already runs `just extract-mathlib` so no CI changes needed.

---

## Part 6 — `mutation_priors` LLM emission

### Schema additions

(Listed in Part 3.) Validation: `engine/crates/api/src/steerer/schema.rs` adds the field, validates non-negative + ≤2.0 + empty-or-known-keys.

### Prompt extension

`engine/crates/api/src/steerer/prompt.rs::SCHEMA_HINT`:

```
"mutation_priors": { "<op_name>": <0..2> }
    -- op_name ∈ ["insert_random", "delete_random", "swap_adjacent",
                  "mutate_axiom_name", "mutate_param", "append_productive_suffix"]
```

System prompt addendum:

> When you observe a cluster making productive use of `append_productive_suffix` or
> `mutate_axiom_name`, bias `mutation_priors` toward those operators. Default behaviour
> is uniform 1.0 across all six.

### GA wiring

The GA crate's `apply_steering_knobs` already reads `config.mutation_knobs` from the steering JSON. Extend it to also read `config.mutation_priors` into the new `chunk_config.mutation_priors: Option<HashMap<String, f32>>` field, which `chain_engine.rs` already passes to `mutate_chain_weighted_with_suffix_bias`.

---

## Part 7 — End-to-end integration test

### Test file: `engine/crates/api/tests/steering_e2e.rs`

```rust
#[tokio::test]
async fn llm_steering_changes_ga_behavior() {
    let state = test_app_state().await;          // in-memory, sqlite-backed alt
    let fake = FakeLlmCaller::returning(
        json!({
            "version": 1, "scope": "C",
            "domain_weights": {"special_relativity": 1.0},
            "fitness_weights": {...},
            "mutation_knobs": {"rate": 0.25, "suffix_bias": 1.0,
                               "population_size": 64, "elitism_fraction": 0.1},
            "mutation_priors": {"append_productive_suffix": 2.0},
            "cluster_directives": [
                {"island_domain": "special_relativity", "cluster_id": 0,
                 "action": "Boost", "strength": 0.5}
            ],
            ...
        })
    );

    // 1. Cycle runs and persists
    let id = run_one_cycle(&state, &state.db, &fake, "test-model").await.unwrap();
    assert!(state.steering.load().etag != 0);

    // 2. /api/seed returns the new config
    let seed: serde_json::Value = get("/api/seed").await;
    assert_eq!(seed["steering"]["config"]["mutation_knobs"]["rate"], 0.25);

    // 3. apply_steering_knobs patches DiscoveryConfig
    let mut cfg = DiscoveryConfig::default();
    let baseline_rate = cfg.mutation_rate;
    apply_steering_knobs(&mut cfg, &seed["steering"]);
    assert_eq!(cfg.mutation_rate, 0.25);
    assert_ne!(cfg.mutation_rate, baseline_rate);

    // 4. Operator distribution actually shifts
    let mut rng = StdRng::seed_from_u64(42);
    let priors = parse_mutation_priors(&seed["steering"]);
    let counts = sample_op_distribution(&priors, 1.0, 10_000, &mut rng);
    let suffix_share = counts[5] as f32 / 10_000.0;
    let uniform_share = 1.0 / 6.0;
    assert!(suffix_share > uniform_share * 2.5,
            "expected ≥2.5× uniform, got {suffix_share}");

    // 5. Cluster directive surfaces and applies
    let directives = parse_cluster_directives(&seed["steering"]);
    assert_eq!(directives.len(), 1);
    let mult = compute_cluster_multiplier(&directives[0]);
    assert!((mult - 1.5).abs() < 1e-6);
}
```

Also covers: scope=B path returns empty `cluster_directives`, parser rejects out-of-range strength, bandit arm updates after cycle close, `POST /api/cluster-report` round-trip.

---

## Migration & rollout

1. PG migration: `cluster_reports`, `cluster_bandit_arms`. Both new tables, no schema changes to existing rows.
2. Worker rollout: workers without the cluster code keep working — they ignore unknown fields in `/api/seed` and never POST to `/api/cluster-report`. The bandit cold-starts as soon as the first new-version worker reports.
3. API rollout: schema change is additive. Old `SteeringConfig` JSON without `mutation_priors`/`cluster_directives` deserializes via `#[serde(default)]`.
4. Mathlib hard-fail is the only breaking change. Communicated in `README.md` and `justfile bootstrap`.

---

## Failure modes & guardrails

- **LLM emits hallucinated cluster_id**: drop directive with warn; cycle persists; bandit unaffected.
- **Bandit converges on a poor K**: UCB1 exploration term keeps re-pulling other arms periodically; if reward signal is genuinely flat (no signal that K matters), the bandit harmlessly oscillates.
- **`/api/cluster-report` flooded**: per-worker per-chunk uniqueness enforced at write; rate-limit middleware caps at 6 reports/min/worker.
- **Worker without cluster support reports nothing**: bandit reward defaults to 0.5 (neutral), keeps exploring.
- **`mutation_priors` keys all unknown**: `chain_ga.rs:128-130` already falls back to uniform — no new code needed.
- **Mathlib corpus partially extracted (e.g. crash mid-extract)**: hard-fail catches via min-entries threshold; user must re-run `just extract-mathlib`.

---

## Open issues (none blocking — flagged for visibility)

- Bandit weights `(w_v, w_s, w_n, w_g)` start as `(0.40, 0.25, 0.20, 0.15)`. If post-launch we see the bandit converging to too-low or too-high K, revisit weights — but don't expose them to the LLM.
- `silhouette` is O(N²) per island. For population_size ≤ 512 this is fine (~250K ops); document the bound, revisit if pop grows.
- No frontend visualization of clusters yet. Out of scope; admin SQL is sufficient until product needs it.
