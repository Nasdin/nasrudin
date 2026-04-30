# Per-Cluster Directive Multiplier Bandit — Design

**Date:** 2026-04-30
**Phase:** Builds on `docs/superpowers/specs/2026-04-30-cluster-steering-fixes-design.md`
(LLM cluster steering closed-loop). That spec wired the LLM to emit
`cluster_directives`; this spec closes the last open gap by automating
how those directives translate into actual mutation-rate / elitism /
kill / diversify multipliers per cluster.
**Status:** Brainstorming complete; awaiting user spec review.

---

## Goal

The 2026-04-30 cluster-steering fixes left one pragmatic gap: the LLM
emits `cluster_directives` of the form `(island_domain,
centroid_skeleton_hash, action, strength)`, but the worker currently
applies them through a *static formula* (`mutation_rate_mult = 1.0 +
1.0 * strength` for `Boost`, etc.). A static formula can't adapt — the
mapping from `strength=0.5` to "what multiplier actually helps" is
domain-dependent and changes as the search landscape shifts.

This spec automates that mapping. The LLM continues to handle semantic
decisions (which cluster, what action, rough magnitude), and a new
**per-action UCB1 bandit** learns the actual numerical multiplier
that should fire for each `(island, action, strength_bucket)` slot.
Reward signal is the matched cluster's mean-fitness delta one chunk
later. Over time the bandit's pulls converge on multipliers that
genuinely help downstream search; until convergence the spec's static
formula serves as the prior.

After this spec lands, the LLM-driven cluster steering loop is fully
self-tuning end-to-end:
- **K** (number of clusters per island) — UCB1 over `K_VALUES`
- **Action multiplier** (per cluster, per action, per strength bucket)
  — UCB1 over the multiplier-choice table (this spec)
- **Tactical decisions** (which cluster, which action, what magnitude)
  — LLM, with both bandit states visible in the prompt

## Scope dependency

This spec **includes** the per-cluster knob application work that the
prior 2026-04-30 cluster-steering-fixes plan flagged as deferred
follow-up (Task 20: `ClusterMultiplier` + `DiscoveryConfig
.cluster_multipliers` + per-individual rate adjustment in the GA
inner loop). The bandit and the application surface ship together —
splitting them creates a half-finished system where the bandit
records pulls against a knob that doesn't yet adjust the GA.

Concretely, this spec adds (in `nasrudin_ga::chain_engine`):

```rust
#[derive(Debug, Clone, Default)]
pub struct ClusterMultiplier {
    pub mutation_rate_mult: f32,    // default 1.0 (no-op)
    pub elitism_mult: f32,          // default 1.0
    pub kill_fraction: f32,         // default 0.0
    pub diversify_fraction: f32,    // default 0.0
}

// DiscoveryConfig additions:
pub cluster_multipliers: HashMap<u32, ClusterMultiplier>,
pub cluster_assignments: Vec<u32>,   // per-individual cluster_id
```

The mutation site in `run_discovery` resolves a per-individual rate
via `mutation_rate * cluster_multipliers[cluster_assignments[i]]
.mutation_rate_mult`, clamped to the existing GA bounds. Empty
`cluster_assignments` keeps current behaviour exactly.

## Non-goals

- Replacing the LLM emission of `cluster_directives` itself. The LLM
  still picks targets and magnitudes; the bandit learns the
  translation, not the intent.
- Changing the cluster directive schema. Adding `mutation_rate_mult`,
  etc. to the LLM emission would force the model to guess exact
  numbers — wasting tokens and creating a wider validation surface.
- Cross-island arm sharing. Each island's bandit table is independent
  so SR's "Boost strength=0.5 → 1.5×" doesn't get muddied by EM
  preferring a different multiplier under different fitness landscapes.
- Replacing the static formula for the cold-start window. Until each
  arm has ≥3 pulls, the static formula serves as the prior.
- Touching the `cluster_directives` schema's B/C scope rules.

---

## Component map

```
┌────────────────────────────────────────────────────────────────────────┐
│ Worker (engine/crates/ga/src/bin/worker.rs)                            │
│                                                                          │
│  per chunk N:                                                           │
│    1. fetch /api/seed → steering + cluster_config + directive_arms      │
│    2. for each directive matching a current cluster (by hash):          │
│         strength_bucket = bucketize(directive.strength)                 │
│         arms = directive_arms.lookup(island, action, strength_bucket)   │
│         multiplier_choice = ucb1_select(arms)  // 5 candidates per slot │
│         mult_value = ACTION_MULTIPLIER_TABLE[action][multiplier_choice] │
│         apply_to_cluster(cluster_id, action, mult_value)                │
│         worker_directive_log.push((centroid_hash, action,               │
│                                     strength_bucket, multiplier_choice))│
│    3. run_discovery(...)                                                │
│    4. cluster final_population, POST /api/cluster-report (existing)     │
│                                                                          │
│  per chunk N+1:                                                         │
│    5. re-cluster, match worker_directive_log entries to new clusters    │
│       (by centroid_skeleton_hash, Hamming ≤ 0.10):                       │
│         reward = clamp((mean_fitness_now - mean_fitness_then) + 0.5,    │
│                        0.0, 1.0)                                        │
│         POST /api/directive-feedback with [(arm_key, reward)] batch    │
└────────────────────────────────────────────────────────────────────────┘
                                  │
┌─────────────────────────────────▼──────────────────────────────────────┐
│ API daemon (engine/crates/api)                                          │
│                                                                           │
│  POST /api/directive-feedback ── handler ── for each (arm_key, reward): │
│    cluster_directive_arms::record_pull(...)                             │
│                                                                           │
│  GET  /api/seed ── now also folds compact directive_arms snapshot       │
│    (~5KB gzip; refreshed each cycle alongside steering + cluster_config)│
│                                                                           │
│  steerer cycle (every 600s):                                            │
│    (existing K-bandit reward + UCB1 + cluster_config swap)              │
│    NEW: snapshot directive_arms table → ArcSwap →                       │
│         folded into /api/seed                                            │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Part 1 — Strength bucketing

The LLM's `strength` is continuous in `[0, 1]`. Bucket into 5 fixed bins:

| `strength_bucket` | range          |
|------------------|----------------|
| 0                | `[0.0, 0.2)`   |
| 1                | `[0.2, 0.4)`  |
| 2                | `[0.4, 0.6)`  |
| 3                | `[0.6, 0.8)`  |
| 4                | `[0.8, 1.0]`  |

Bucketing trades off resolution vs convergence speed. 5 buckets means
each (island, action) bandit has 5 strength slots × 5 multiplier
choices = 25 arms; with ~10 cycles per hour that's ~12-hour cold-start
per (island, action) before useful exploitation. More buckets → finer
control, slower convergence; fewer → coarser, faster. 5 is the
spec's chosen middle ground.

## Part 2 — Multiplier-choice table

```rust
pub const BOOST_MULTIPLIERS:     &[f32; 5] = &[1.00, 1.25, 1.50, 1.75, 2.00];
pub const EXPLOIT_MULTIPLIERS:   &[f32; 5] = &[1.00, 1.25, 1.50, 1.75, 2.00];
pub const DIVERSIFY_FRACTIONS:   &[f32; 5] = &[0.00, 0.10, 0.20, 0.30, 0.50];
pub const KILL_FRACTIONS:        &[f32; 5] = &[0.00, 0.10, 0.20, 0.30, 0.50];

pub fn lookup(action: ClusterAction, choice: u8) -> f32 {
    let table: &[f32; 5] = match action {
        ClusterAction::Boost     => BOOST_MULTIPLIERS,
        ClusterAction::Exploit   => EXPLOIT_MULTIPLIERS,
        ClusterAction::Diversify => DIVERSIFY_FRACTIONS,
        ClusterAction::Kill      => KILL_FRACTIONS,
    };
    table[(choice as usize).min(4)]
}
```

`Boost` and `Exploit` start at 1.0 (no-op) so the bandit can learn that
weak strengths *should* be no-ops. `Diversify` and `Kill` start at 0.0
for the same reason — a `Diversify` with strength=0.1 should arguably
do nothing.

## Part 3 — `cluster_directive_arms` table

```sql
CREATE TABLE cluster_directive_arms (
    island_domain     TEXT       NOT NULL,
    action            TEXT       NOT NULL,  -- 'boost'|'exploit'|'diversify'|'kill'
    strength_bucket   SMALLINT   NOT NULL,  -- 0..4
    multiplier_choice SMALLINT   NOT NULL,  -- 0..4
    pulls             BIGINT     NOT NULL DEFAULT 0,
    total_reward      DOUBLE PRECISION NOT NULL DEFAULT 0.0,
    last_reward       DOUBLE PRECISION NOT NULL DEFAULT 0.0,
    updated_at        TIMESTAMPTZ NOT NULL DEFAULT now(),
    PRIMARY KEY (island_domain, action, strength_bucket, multiplier_choice)
);

-- Index for the common "all arms for this slot" lookup:
CREATE INDEX idx_directive_arms_slot
    ON cluster_directive_arms (island_domain, action, strength_bucket);
```

Total rows: 6 islands × 4 actions × 5 strength buckets × 5 multiplier
choices = **600 rows**, materialised at API boot with zero stats
(idempotent `ensure_all_arms`, parallels the existing K-bandit boot).

## Part 4 — UCB1 selection

Same as the K-bandit: cold-start picks any unpulled arm, then
`mean + sqrt(2 * ln(N_slot) / pulls)`. `N_slot` is the sum of pulls
across the 5 multiplier choices for one (island, action,
strength_bucket) — local exploration term, not global.

```rust
pub fn select_multiplier(arms: &[DirectiveArmStat]) -> u8 {
    if let Some(unpulled) = arms.iter().find(|a| a.pulls == 0) {
        return unpulled.multiplier_choice;
    }
    let total_pulls: i64 = arms.iter().map(|a| a.pulls).sum();
    let ln_n = (total_pulls as f64).ln();
    let mut best = arms[0].multiplier_choice;
    let mut best_score = f64::NEG_INFINITY;
    for a in arms {
        let mean = a.total_reward / a.pulls as f64;
        let exploration = (2.0 * ln_n / a.pulls as f64).sqrt();
        let score = mean + exploration;
        if score > best_score {
            best_score = score;
            best = a.multiplier_choice;
        }
    }
    best
}
```

## Part 5 — Reward attribution

Per-cluster reward signal computed worker-side at chunk N+1, then
batched up and POSTed.

```rust
pub struct WorkerDirectiveEntry {
    pub centroid_hash_at_apply: u64,   // chunk N's matched cluster hash
    pub action: ClusterAction,
    pub strength_bucket: u8,
    pub multiplier_choice: u8,
    pub mean_fitness_at_apply: f32,    // captured at apply time
}

// At chunk N+1, after re-clustering:
for entry in worker_directive_log.drain(..) {
    let Some(new_cluster) = match_directive_to_cluster(
        entry.centroid_hash_at_apply,
        &current_cluster_centroids,
        0.10, // matches existing threshold from clustering::mod
    ) else {
        // Cluster identity drifted too far; reward unobservable, drop entry.
        continue;
    };
    let new_mean = current_summaries[new_cluster as usize].mean_fitness;
    // Translate fitness delta in [-1, 1] to reward in [0, 1] via
    // affine mapping; clamp so a single-chunk regression doesn't
    // permanently damn an arm.
    let reward = ((new_mean - entry.mean_fitness_at_apply) + 0.5)
        .clamp(0.0, 1.0) as f64;
    feedback_batch.push(DirectiveFeedback {
        island_domain, action: entry.action,
        strength_bucket: entry.strength_bucket,
        multiplier_choice: entry.multiplier_choice,
        reward,
    });
}
post_directive_feedback(api_cfg, &feedback_batch).await;
```

The `+0.5` shift keeps `reward ∈ [0, 1]` instead of negative; the
clamp prevents a one-chunk regression from saturating the arm to
zero. Directives whose cluster hash drifted beyond the 0.10 Hamming
threshold are dropped — that's not "the directive failed", it's "we
can't tell what happened", which is the correct treatment for noisy
attribution.

## Part 6 — `POST /api/directive-feedback`

```
POST /api/directive-feedback
Authorization: Bearer <worker_token>
Content-Type: application/json

{
  "feedback": [
    {
      "island_domain": "special_relativity",
      "action": "boost",
      "strength_bucket": 2,
      "multiplier_choice": 3,
      "reward": 0.62
    },
    ...
  ]
}

→ 200 {"received": true, "applied": 4}
```

Handler iterates the batch, calls `record_pull` per arm. Same auth and
rate-limit layer as `/api/cluster-report`. The "applied" counter
mirrors the cluster_report endpoint so we can spot drops via logs.

## Part 7 — Snapshotting `directive_arms` into `/api/seed`

Steerer cycle (after the K-bandit step, before the LLM call) takes a
read snapshot of the full 600-row table into a compact in-process
struct, ArcSwap-publishes it, invalidates seed cache. `/api/seed`
folds it as a sibling of `cluster_config`:

```json
{
  "axioms": [...],
  "steering": { "config": ..., "etag": ... },
  "cluster_config": { "k_per_island": ..., "etag": ... },
  "directive_arms": {
    "snapshot": [
      { "island_domain": "special_relativity", "action": "boost",
        "strength_bucket": 2,
        "arms": [
          { "multiplier_choice": 0, "pulls": 12, "mean_reward": 0.41 },
          { "multiplier_choice": 1, "pulls": 18, "mean_reward": 0.55 },
          ...
        ]
      },
      ...
    ],
    "etag": "..."
  }
}
```

Compact form (only one row per slot, with the 5 arms inlined) keeps
the JSON ~30 KB plain / ~5 KB gzip — negligible compared to the axiom
list. Compression's already on the seed handler.

## Part 8 — Worker-side application

At chunk N, after parsing `cluster_directives` from steering and
matching them to current clusters (existing code from
2026-04-30 plan task 19):

```rust
// Bucket the LLM's continuous strength into one of 5 bins.
fn strength_bucket(strength: f32) -> u8 {
    (strength.clamp(0.0, 1.0) * 5.0).floor().min(4.0) as u8
}

// Look up the bandit arms for this slot from the seed payload.
let arms = directive_arms_lookup(
    &last_seed["directive_arms"],
    domain, action, strength_bucket,
);
let multiplier_choice = ucb1::select_multiplier(&arms);
let mult_value = lookup(action, multiplier_choice);

// Apply to the cluster's per-cluster knob entry. The application
// surface is the existing ClusterMultiplier struct from the
// 2026-04-30 plan (Boost → mutation_rate_mult, Exploit → elitism_mult,
// Diversify → diversify_fraction, Kill → kill_fraction).
let m = chunk_config
    .cluster_multipliers
    .entry(cluster_id)
    .or_default();
match action {
    Boost     => m.mutation_rate_mult = mult_value,
    Exploit   => m.elitism_mult       = mult_value,
    Diversify => m.diversify_fraction = mult_value,
    Kill      => m.kill_fraction      = mult_value,
}

// Log for next-chunk reward attribution.
worker_directive_log.push(WorkerDirectiveEntry {
    centroid_hash_at_apply: matched_centroid_hash,
    action, strength_bucket, multiplier_choice,
    mean_fitness_at_apply: matched_cluster.mean_fitness,
});
```

If the seed payload's `directive_arms` snapshot is absent (e.g. first
boot before the steerer cycle has run) the worker falls back to the
spec's static formula, exactly as today. No behavioural regression.

## Part 9 — Bootstrap fallback

Until each arm in a slot has ≥3 pulls, blend bandit choice with the
static formula proportionally. Concretely:

```rust
let total_slot_pulls: i64 = arms.iter().map(|a| a.pulls).sum();
if total_slot_pulls < 15 {
    // 15 = 3 pulls × 5 arms; below this, the bandit is too noisy to
    // exploit yet. Use a strength-linear interpolation against the
    // multiplier table as a smooth prior.
    return strength_to_static_choice(action, strength);
}
ucb1::select_multiplier(&arms)
```

This avoids the bandit early-locking on a poor first reward.
`strength_to_static_choice` maps strength linearly across the 5-entry
table (e.g. strength=0.3 → choice 1).

## Part 10 — Configuration constants

All in a new `engine/crates/api/src/steerer/directive_bandit.rs`
alongside the K-bandit module:

```rust
pub const STRENGTH_BUCKETS: u8 = 5;
pub const MULTIPLIER_CHOICES: u8 = 5;
pub const COLD_START_PULL_THRESHOLD: i64 = 15;  // 3 pulls × 5 arms
pub const REWARD_BIAS: f32 = 0.5;               // affine shift in reward computation
pub const HASH_MATCH_THRESHOLD: f32 = 0.10;    // shared with clustering matching
pub const ACTIONS: &[ClusterAction] = &[
    ClusterAction::Boost,
    ClusterAction::Exploit,
    ClusterAction::Diversify,
    ClusterAction::Kill,
];
```

## Migration & rollout

1. PG migration adds `cluster_directive_arms`. New table, no schema
   change to existing rows.
2. API rollout: schema for `/api/seed` is additive — workers without
   the directive-bandit code see the new `directive_arms` field and
   ignore it. Steerer's snapshot + ArcSwap publication is independent
   of the worker's path; rollback is just dropping the new endpoint.
3. Worker rollout: workers without the new code never POST
   `/api/directive-feedback`; bandit arms simply don't accumulate
   pulls and the spec's static formula remains the fallback.
4. Boot: `ensure_all_arms_directive` runs alongside the existing K
   `ensure_all_arms`, materialising the 600 rows.

## Failure modes & guardrails

- **LLM emits a directive whose strength bucket has all-zero arms**:
  fallback path activates (Part 9), behaviour matches the static
  formula until the bandit warms up.
- **Worker can't match a directive's hash to any current cluster**:
  log entry dropped, no reward emitted, no arm pull. Cluster identity
  truly drifted; arm should not be rewarded or punished.
- **All clusters in an island regress (chunk-wide bad luck)**: every
  arm in the affected slots gets a low reward simultaneously. UCB1's
  exploration term re-pulls them on subsequent cycles, so a single
  bad-luck chunk doesn't permanently lock the bandit out of any
  multiplier_choice.
- **`POST /api/directive-feedback` rate-limited or down**: feedback
  silently dropped (existing rate-limit middleware behaviour). Arm
  pulls are best-effort; missing pulls don't corrupt state, they just
  slow convergence.
- **Multiplier-choice tables drift from the worker's lookup**: tables
  are constants in `nasrudin-ga` and re-exported via `nasrudin-api`;
  any mismatch is a compile error. Add an asserted-equal test in
  `directive_bandit::tests` so future edits to one stay synced with
  the other.
- **Cold-start window for a brand-new island domain**: would take 600
  ÷ (~10 cycles/hour × workers) ≈ a few hours to cover all arms once.
  Static-formula fallback handles the gap. Acceptable.

## Test coverage

Unit:
- `bucketize_strength` boundary tests (0.0 → 0, 0.199999 → 0,
  0.2 → 1, ..., 1.0 → 4).
- `lookup(action, choice)` for each action × all 5 choices.
- `select_multiplier` cold-start, exploit, exploration paths
  (parallels existing K-bandit tests).
- `compute_reward` affine clamp boundary tests.

Integration:
- New e2e test `directive_bandit_e2e.rs` extending the existing
  `steering_e2e.rs` harness:
  1. Seed the directive_arms table with skewed pulls so one
     multiplier_choice is the obvious UCB1 pick.
  2. Run a cycle; assert `/api/seed` carries the snapshot.
  3. Worker-side: parse, call `select_multiplier`, assert the picked
     multiplier matches the expected (from the skewed seed).
  4. POST `/api/directive-feedback` with a known reward; assert
     `record_pull` mutated the arm.

---

## Open issues (none blocking — flagged for visibility)

- Reward window is single-chunk delta. If post-launch we see noisy
  attribution (cluster identity drifting too often → too many drops),
  revisit by switching to 3-chunk rolling delta. The bandit's long-run
  mean is robust to the window choice; only convergence speed
  changes.
- 600 arms × periodic snapshot is fine today. If the (island, action,
  strength_bucket, multiplier_choice) cardinality grows (e.g. someone
  splits Boost into Boost-rate vs Boost-suffix-bias), revisit the
  snapshot strategy — at 5000+ arms we'd want delta-encoded updates
  via SSE rather than full snapshots in `/api/seed`.
- The ACTION_MULTIPLIER_TABLE values themselves (the 5 candidate
  multipliers per action) are constants, not learned. The bandit
  picks among them; it doesn't generate new candidates. Adding
  candidates is a code change. This is intentional — auto-generating
  candidates is an unbounded optimization problem and not worth the
  complexity for a per-cluster knob.
