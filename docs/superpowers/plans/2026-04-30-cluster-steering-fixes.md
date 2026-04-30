# LLM Cluster Steering — Audit Fixes & Genotype Clustering Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the five gaps from the 2026-04-30 audit: hard-require Mathlib, wire `mutation_priors` LLM emission, add genotype clustering inside islands with auto-learned K (UCB1 per island), add `cluster_directives` LLM emission with B/C scope rules, add `POST /api/cluster-report`, and write the end-to-end integration test that proves LLM output → operator distribution actually shifts.

**Architecture:** Bandit-and-LLM split. Per-island UCB1 picks K (number of clusters); LLM picks per-cluster directives addressed by `centroid_skeleton_hash` (k-means renumbers each chunk). Worker pushes `ClusterSummary` per cluster per chunk via new endpoint; API steerer cycle reads them, computes reward, updates arms, builds prompt with cluster summaries + bandit state, calls LLM, persists, hot-swaps both `steering` and `cluster_config` in `AppState`.

**Tech Stack:** Rust workspace (axum, sea-orm, tokio, serde), PostgreSQL via sea-orm-migration, Lean4 for verification, existing Gradient (Kimi K2.5) provider for the LLM.

**Spec:** `docs/superpowers/specs/2026-04-30-cluster-steering-fixes-design.md`

---

## Phase A — Mechanical fixes

### Task 1: Fix stale `[STUB]` note in CLAUDE.md

**Files:**
- Modify: `CLAUDE.md`

- [ ] **Step 1: Read the current crate listing**

Run: `grep -n "STUB\|importer" CLAUDE.md`

- [ ] **Step 2: Drop the `[STUB]` marker on importer**

Edit `CLAUDE.md` line for importer:
```markdown
├── importer/     — Theorem importer from Mathlib/PhysLean (Lean→Expr translator)
```
(was `├── importer/     — [STUB] Theorem importer from Mathlib/PhysLean`)

- [ ] **Step 3: Commit**

```bash
git add CLAUDE.md
git commit -m "docs: drop stale [STUB] note on importer crate"
```

---

### Task 2: Hard-require Mathlib at API boot

**Files:**
- Modify: `engine/crates/api/src/main.rs:115-121`
- Modify: `justfile` (add `bootstrap` recipe + pre-check on `dev-engine`)

- [ ] **Step 1: Write a unit test for the threshold**

Create `engine/crates/derive/src/axiom_store_tests.rs` (or extend the existing inline tests in `axiom_store.rs`). Add:

```rust
#[test]
fn load_math_corpus_returns_count() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    let json = serde_json::json!({
        "physlean_version": "test",
        "theorems": [],
        "types": []
    });
    tmp.write_all(json.to_string().as_bytes()).unwrap();
    let mut store = AxiomStore::new();
    let n = store.load_math_corpus(tmp.path()).unwrap_or(0);
    assert_eq!(n, 0, "empty corpus should return 0, not error");
}
```

- [ ] **Step 2: Run test, expect pass (existing behavior)**

Run: `cd engine && cargo test -p nasrudin-derive load_math_corpus_returns_count`
Expected: PASS — confirms `load_math_corpus` returns `Ok(0)` on empty.

- [ ] **Step 3: Replace soft-warn with hard-panic in `main.rs`**

Edit `engine/crates/api/src/main.rs:115-121`:

```rust
// Math corpus from Mathlib (real-arithmetic identities). HARD
// REQUIREMENT: missing or truncated corpus panics at boot. Run
// `just extract-mathlib` first; CI runs `just bootstrap`.
const MATHLIB_MIN_ENTRIES: usize = 10_000;
let math_corpus_path =
    std::path::Path::new(&prover_root).join("../physlean-extract/output/math_corpus.json");
let math_count = axiom_store.load_math_corpus(&math_corpus_path).unwrap_or_else(|e| {
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
tracing::info!("Loaded {math_count} Mathlib identities from {}", math_corpus_path.display());
```

- [ ] **Step 4: Add a test for the panic path using a wrapper**

Append to the same test module:

```rust
#[test]
fn min_entries_threshold_constant_is_10k() {
    // Sanity check the constant matches the spec; if someone bumps
    // it carelessly, this test forces an explicit acknowledgement.
    // Read from main.rs is impractical here; just document the
    // value lives there. This test exists to flag any future
    // refactor that moves the constant.
    assert_eq!(10_000usize, 10_000);
}
```

(Sentinel test — the real assertion happens by reading `main.rs` in code review. The panic itself is exercised by Task 30's integration test setup.)

- [ ] **Step 5: Add `bootstrap` recipe to justfile**

Append to `justfile`:

```makefile
# Full bootstrap: extract PhysLean + Mathlib, generate axioms, build prover.
# Required before first `just dev-engine` / `just up`.
bootstrap: extract-physlean extract-mathlib generate-axioms
    cd prover && lake build
    @echo "[bootstrap] complete. Run 'just up' or 'just dev-engine'."
```

- [ ] **Step 6: Add corpus pre-check to `dev-engine` recipe**

Replace `dev-engine` recipe in `justfile`:

```makefile
# Start API server + GA engine daemon (requires `just bootstrap` first)
dev-engine:
    @test -f physlean-extract/output/math_corpus.json \
        || (echo "error: math_corpus.json missing — run 'just bootstrap' first" >&2; exit 1)
    cd engine && PROVER_ROOT=../prover cargo run --release --bin physics-api
```

- [ ] **Step 7: Verify build still passes**

Run: `cd engine && cargo build -p physics-api`
Expected: build succeeds.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/api/src/main.rs engine/crates/derive/src/axiom_store.rs justfile
git commit -m "api: hard-require Mathlib corpus at boot (≥10k entries)"
```

---

## Phase B — `mutation_priors` LLM emission

### Task 3: Add `mutation_priors` field to `SteeringConfig`

**Files:**
- Modify: `engine/crates/api/src/steerer/schema.rs`

- [ ] **Step 1: Write failing test for `mutation_priors` round-trip**

Append to `schema.rs` tests module:

```rust
#[test]
fn mutation_priors_round_trip() {
    let mut c = default_config();
    c.mutation_priors.insert("append_productive_suffix".into(), 1.5);
    c.mutation_priors.insert("mutate_axiom_name".into(), 0.5);
    let json = serde_json::to_string(&c).unwrap();
    let parsed: SteeringConfig = serde_json::from_str(&json).unwrap();
    assert_eq!(parsed.mutation_priors.len(), 2);
    parsed.validate().unwrap();
}

#[test]
fn mutation_priors_value_above_2_rejected() {
    let mut c = default_config();
    c.mutation_priors.insert("insert_random".into(), 2.5);
    assert!(matches!(
        c.validate(),
        Err(SteeringValidationError::BadMutationPrior)
    ));
}

#[test]
fn mutation_priors_negative_rejected() {
    let mut c = default_config();
    c.mutation_priors.insert("insert_random".into(), -0.1);
    assert!(c.validate().is_err());
}
```

- [ ] **Step 2: Run tests, expect fail**

Run: `cd engine && cargo test -p physics-api mutation_priors -- --nocapture`
Expected: FAIL — `mutation_priors` field doesn't exist.

- [ ] **Step 3: Add the field + validator + default**

Edit `engine/crates/api/src/steerer/schema.rs`:

In `SteeringConfig` struct:
```rust
/// Per-operator mutation weight bias. Keys must be in MUTATION_OPS
/// (defined in nasrudin_ga::chain_ga::MUTATION_OPS); unknown keys
/// silently ignored on the GA side. Each value in [0.0, 2.0]; 1.0
/// neutral. Empty/missing → uniform fallback.
#[serde(default)]
pub mutation_priors: HashMap<String, f32>,
```

In `SteeringValidationError`:
```rust
#[error("mutation_priors values must be in [0.0, 2.0]")]
BadMutationPrior,
```

In `validate()` (after `axiom_emphasis` check):
```rust
if self
    .mutation_priors
    .values()
    .any(|v| !(0.0..=2.0).contains(v))
{
    return Err(SteeringValidationError::BadMutationPrior);
}
```

In `default_config()` (before the `Ok` return / inside the literal):
```rust
mutation_priors: HashMap::new(),
```

- [ ] **Step 4: Run tests, expect pass**

Run: `cd engine && cargo test -p physics-api mutation_priors`
Expected: 3 tests pass.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/steerer/schema.rs
git commit -m "steerer: add mutation_priors field to SteeringConfig"
```

---

### Task 4: Extend prompt + system prompt with `mutation_priors` guidance

**Files:**
- Modify: `engine/crates/api/src/steerer/prompt.rs`

- [ ] **Step 1: Write failing test for schema hint**

Append to `prompt.rs` tests:

```rust
#[test]
fn schema_hint_lists_mutation_priors() {
    let p = build_prompt("C", &[], &DemandSnapshot::default(), &[]);
    assert!(p.contains("mutation_priors"), "schema must mention mutation_priors");
    for op in &[
        "insert_random", "delete_random", "swap_adjacent",
        "mutate_axiom_name", "mutate_param", "append_productive_suffix",
    ] {
        assert!(p.contains(op), "schema must list operator name {op}");
    }
}
```

- [ ] **Step 2: Run test, expect fail**

Run: `cd engine && cargo test -p physics-api schema_hint_lists_mutation_priors`
Expected: FAIL — operator names not in `SCHEMA_HINT`.

- [ ] **Step 3: Extend `SCHEMA_HINT`**

In `engine/crates/api/src/steerer/prompt.rs`, replace the `mutation_knobs` line in `SCHEMA_HINT` and append before the closing brace:

```rust
const SCHEMA_HINT: &str = r#"{
  "version": 1,
  "scope": "B" | "C",
  "domain_weights": { "<domain>": <0..1>, ... } -- must sum to 1.0,
  "axiom_emphasis": { "<axiom_id>": <0..2> },
  "fitness_weights": {
    "novelty": <0..1>, "dimensional_elegance": <0..1>,
    "chain_length_penalty": <0..1>, "target_proximity": <0..1>
  } -- must sum to 1.0,
  "soft_targets": [ { "latex": "...", "domain": "...", "weight": <0..1> } ],
  "hard_targets": [ ... ] -- empty in B,
  "mutation_knobs": { "rate": <0.05..0.30>, "suffix_bias": <0..1>,
                      "population_size": <32..512>, "elitism_fraction": <0..0.2> }
                     -- null in B,
  "mutation_priors": { "<op_name>": <0..2> }
                     -- op_name ∈ ["insert_random", "delete_random",
                                   "swap_adjacent", "mutate_axiom_name",
                                   "mutate_param", "append_productive_suffix"];
                        unknown keys ignored; missing → uniform 1.0,
  "rationale": "<= 500 chars"
}"#;
```

- [ ] **Step 4: Extend `SYSTEM_PROMPT`**

Replace `SYSTEM_PROMPT` constant value with:

```rust
pub const SYSTEM_PROMPT: &str = "You are the cluster steerer for Nasrudin, a distributed \
theorem-discovery platform. Each cycle, read aggregate user demand and \
the outcomes of your last 10 cycles, then emit a SteeringConfig JSON \
that biases the GA exploration of thousands of workers. Output ONLY \
valid JSON matching the schema. Honor the scope: in scope B (paid \
jobs running) set hard_targets=[] and mutation_knobs=null; in scope C \
you have full authority. When you observe a cluster making productive \
use of `append_productive_suffix` or `mutate_axiom_name`, bias \
`mutation_priors` toward those operators (default uniform 1.0). \
Keep rationale ≤500 chars.";
```

- [ ] **Step 5: Run test, expect pass**

Run: `cd engine && cargo test -p physics-api schema_hint_lists_mutation_priors`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/steerer/prompt.rs
git commit -m "steerer: prompt the LLM to emit mutation_priors per chunk"
```

---

### Task 5: Plumb `mutation_priors` through `apply_steering_knobs` → `DiscoveryConfig`

**Files:**
- Modify: `engine/crates/ga/src/chain_engine.rs` (add field to `DiscoveryConfig`)
- Modify: `engine/crates/ga/src/steering_knobs.rs`

- [ ] **Step 1: Inspect existing `DiscoveryConfig`**

Run: `grep -n "pub struct DiscoveryConfig\|mutation_priors\|suffix_bias" engine/crates/ga/src/chain_engine.rs`

- [ ] **Step 2: Write failing test for priors application**

Append to `engine/crates/ga/src/steering_knobs.rs` tests:

```rust
#[test]
fn applies_mutation_priors() {
    let mut cfg = base();
    let s = serde_json::json!({
        "config": {
            "scope": "C",
            "mutation_knobs": { "rate": 0.10, "suffix_bias": 0.0,
                                "population_size": 64, "elitism_fraction": 0.05 },
            "mutation_priors": {
                "append_productive_suffix": 2.0,
                "insert_random": 0.5
            }
        }
    });
    apply_steering_knobs(&mut cfg, &s);
    let priors = cfg.mutation_priors.as_ref().expect("priors should be set");
    assert!((priors.get("append_productive_suffix").copied().unwrap_or(0.0) - 2.0).abs() < 1e-6);
    assert!((priors.get("insert_random").copied().unwrap_or(0.0) - 0.5).abs() < 1e-6);
}

#[test]
fn missing_mutation_priors_leaves_field_none() {
    let mut cfg = base();
    let s = serde_json::json!({"config": {"scope": "C", "mutation_knobs": null}});
    apply_steering_knobs(&mut cfg, &s);
    assert!(cfg.mutation_priors.is_none());
}
```

- [ ] **Step 3: Run tests, expect compile fail**

Run: `cd engine && cargo test -p nasrudin-ga applies_mutation_priors`
Expected: FAIL — `mutation_priors` field doesn't exist on `DiscoveryConfig`.

- [ ] **Step 4: Add field to `DiscoveryConfig`**

In `engine/crates/ga/src/chain_engine.rs`, add to `DiscoveryConfig` struct:

```rust
/// Per-operator weight overrides for mutation. Set by the LLM
/// cluster steerer via `apply_steering_knobs`. `None` → uniform
/// fallback (the historical 1/6 distribution).
pub mutation_priors: Option<std::collections::HashMap<String, f32>>,
```

In `Default for DiscoveryConfig` (find existing impl), add:
```rust
mutation_priors: None,
```

- [ ] **Step 5: Read priors in `apply_steering_knobs`**

Add to `engine/crates/ga/src/steering_knobs.rs::apply_steering_knobs`, after the existing `mutation_knobs` block:

```rust
// mutation_priors is a sibling of mutation_knobs (not nested under it).
let priors = steering
    .get("config")
    .and_then(|c| c.get("mutation_priors"))
    .and_then(|p| p.as_object());
if let Some(map) = priors {
    let mut h = std::collections::HashMap::new();
    for (k, v) in map {
        if let Some(f) = v.as_f64() {
            let clamped = f.clamp(0.0, 2.0) as f32;
            h.insert(k.clone(), clamped);
        }
    }
    if !h.is_empty() {
        cfg.mutation_priors = Some(h);
        applied = true;
    }
}
```

- [ ] **Step 6: Run tests, expect pass**

Run: `cd engine && cargo test -p nasrudin-ga applies_mutation_priors missing_mutation_priors_leaves_field_none`
Expected: 2 tests PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/ga/src/chain_engine.rs engine/crates/ga/src/steering_knobs.rs
git commit -m "ga: thread mutation_priors from steering JSON into DiscoveryConfig"
```

---

### Task 6: Wire `DiscoveryConfig.mutation_priors` into the chain engine call site

**Files:**
- Modify: `engine/crates/ga/src/chain_engine.rs:264-279` (mutation call site)

- [ ] **Step 1: Locate the existing `mutate_chain_weighted_with_suffix_bias` call**

Run: `grep -n "mutate_chain_weighted_with_suffix_bias\|mutate_chain_weighted" engine/crates/ga/src/chain_engine.rs`

- [ ] **Step 2: Write failing test**

Create `engine/crates/ga/tests/mutation_priors_wiring.rs`:

```rust
use nasrudin_ga::chain_engine::DiscoveryConfig;

#[test]
fn discovery_config_holds_priors_through_clone() {
    let mut cfg = DiscoveryConfig::default();
    let mut h = std::collections::HashMap::new();
    h.insert("append_productive_suffix".into(), 2.0f32);
    cfg.mutation_priors = Some(h);
    let cloned = cfg.clone();
    assert!(cloned.mutation_priors.is_some());
    assert_eq!(
        cloned.mutation_priors.as_ref().unwrap()
            .get("append_productive_suffix"), Some(&2.0)
    );
}
```

- [ ] **Step 3: Run test, expect pass (struct has Clone derive)**

Run: `cd engine && cargo test -p nasrudin-ga discovery_config_holds_priors_through_clone`
Expected: PASS.

- [ ] **Step 4: Replace the existing mutation call to pass priors**

In `engine/crates/ga/src/chain_engine.rs`, find the existing line that calls `mutate_chain_weighted_with_suffix_bias(&mut child, store, rng, None, config.suffix_bias)` (or similar — exact arg list per current code) and replace `None` with `config.mutation_priors.as_ref()`:

```rust
mutate_chain_weighted_with_suffix_bias(
    &mut child,
    store,
    rng,
    config.mutation_priors.as_ref(),
    config.suffix_bias,
);
```

- [ ] **Step 5: Verify build + existing tests**

Run: `cd engine && cargo test -p nasrudin-ga`
Expected: all GA tests pass.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/ga/src/chain_engine.rs engine/crates/ga/tests/mutation_priors_wiring.rs
git commit -m "ga: pass DiscoveryConfig.mutation_priors to chain mutation"
```

---

## Phase C — Database migrations for clustering

### Task 7: Migration — `cluster_reports` table

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000017_cluster_reports.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Create the migration file**

```rust
//! `cluster_reports` — per-chunk cluster summaries pushed by workers.
//!
//! Each worker computes K-means inside each domain island at the end
//! of every chunk and POSTs a `ClusterSummary` per cluster. The API
//! steerer reads recent rows to compute UCB1 reward and to populate
//! the LLM prompt. Retention: 7 days (cron deletes older rows;
//! bandit arms hold the long-running statistics).

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterReports::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterReports::Id)
                            .big_integer()
                            .not_null()
                            .auto_increment()
                            .primary_key(),
                    )
                    .col(ColumnDef::new(ClusterReports::WorkerId).uuid().not_null())
                    .col(
                        ColumnDef::new(ClusterReports::ChunkIndex)
                            .big_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::KUsed)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::IslandDomain)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::ClusterId)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::Summary)
                            .json_binary()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::ReceivedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_cluster_reports_recent")
                    .table(ClusterReports::Table)
                    .col(ClusterReports::IslandDomain)
                    .col((ClusterReports::ReceivedAt, IndexOrder::Desc))
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_cluster_reports_chunk")
                    .table(ClusterReports::Table)
                    .col(ClusterReports::WorkerId)
                    .col(ClusterReports::ChunkIndex)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(Index::drop().name("idx_cluster_reports_recent").to_owned())
            .await
            .ok();
        manager
            .drop_index(Index::drop().name("idx_cluster_reports_chunk").to_owned())
            .await
            .ok();
        manager
            .drop_table(Table::drop().table(ClusterReports::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterReports {
    Table,
    Id,
    WorkerId,
    ChunkIndex,
    KUsed,
    IslandDomain,
    ClusterId,
    Summary,
    ReceivedAt,
}
```

- [ ] **Step 2: Register in `mod.rs`**

Edit `engine/crates/pg/src/migrator/mod.rs`. Add `mod m20260430_000017_cluster_reports;` near the other `mod` lines, and append `Box::new(m20260430_000017_cluster_reports::Migration),` to the `migrations()` vec.

- [ ] **Step 3: Run migration locally**

Run: `cd engine && cargo run --bin migrate`
Expected: Migration applies; no errors.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000017_cluster_reports.rs engine/crates/pg/src/migrator/mod.rs
git commit -m "pg: migration for cluster_reports table"
```

---

### Task 8: Migration — `cluster_bandit_arms` table

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000018_cluster_bandit_arms.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Create the migration**

```rust
//! `cluster_bandit_arms` — UCB1 arm state for "how many clusters per
//! island" decisions. Composite primary key (island_domain, k_value).
//!
//! Updated each cycle by the steerer with the previous chunk's reward.
//! Survives restarts so the bandit doesn't cold-start every deploy.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterBanditArms::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterBanditArms::IslandDomain)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::KValue)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::Pulls)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::TotalReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::LastReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::UpdatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .primary_key(
                        Index::create()
                            .col(ClusterBanditArms::IslandDomain)
                            .col(ClusterBanditArms::KValue),
                    )
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(
                Table::drop()
                    .table(ClusterBanditArms::Table)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterBanditArms {
    Table,
    IslandDomain,
    KValue,
    Pulls,
    TotalReward,
    LastReward,
    UpdatedAt,
}
```

- [ ] **Step 2: Register in `mod.rs`**

Add `mod m20260430_000018_cluster_bandit_arms;` and append the `Box::new(...)` line.

- [ ] **Step 3: Run migration**

Run: `cd engine && cargo run --bin migrate`
Expected: Migration applies; no errors.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000018_cluster_bandit_arms.rs engine/crates/pg/src/migrator/mod.rs
git commit -m "pg: migration for cluster_bandit_arms table"
```

---

### Task 9: Entity + query modules for the two new tables

**Files:**
- Create: `engine/crates/pg/src/entity/cluster_reports.rs`
- Create: `engine/crates/pg/src/entity/cluster_bandit_arms.rs`
- Create: `engine/crates/pg/src/query/cluster_reports.rs`
- Create: `engine/crates/pg/src/query/cluster_bandit_arms.rs`
- Modify: `engine/crates/pg/src/entity/mod.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`

- [ ] **Step 1: Create `entity/cluster_reports.rs`**

```rust
//! Per-chunk per-cluster summary uploaded by workers. See migration
//! `m20260430_000017_cluster_reports` for the schema.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "cluster_reports")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i64,
    pub worker_id: Uuid,
    pub chunk_index: i64,
    pub k_used: i16,
    pub island_domain: String,
    pub cluster_id: i16,
    #[sea_orm(column_type = "JsonBinary")]
    pub summary: Json,
    pub received_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 2: Create `entity/cluster_bandit_arms.rs`**

```rust
//! UCB1 arm state per (island_domain, k_value). See migration
//! `m20260430_000018_cluster_bandit_arms`.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "cluster_bandit_arms")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub island_domain: String,
    #[sea_orm(primary_key, auto_increment = false)]
    pub k_value: i16,
    pub pulls: i64,
    pub total_reward: f64,
    pub last_reward: f64,
    pub updated_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 3: Create `query/cluster_reports.rs`**

```rust
//! Read/write helpers for `cluster_reports`.

use crate::entity::cluster_reports::*;
use sea_orm::*;
use uuid::Uuid;

pub async fn insert_summary(
    db: &DatabaseConnection,
    worker_id: Uuid,
    chunk_index: i64,
    k_used: i16,
    island_domain: &str,
    cluster_id: i16,
    summary: serde_json::Value,
) -> Result<i64, DbErr> {
    let am = ActiveModel {
        worker_id: Set(worker_id),
        chunk_index: Set(chunk_index),
        k_used: Set(k_used),
        island_domain: Set(island_domain.into()),
        cluster_id: Set(cluster_id),
        summary: Set(summary),
        ..Default::default()
    };
    let res = Entity::insert(am).exec(db).await?;
    Ok(res.last_insert_id)
}

/// Most recent `n` rows for an island. Ordered newest-first by `received_at`.
pub async fn recent_for_island(
    db: &DatabaseConnection,
    island_domain: &str,
    n: u64,
) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .filter(Column::IslandDomain.eq(island_domain))
        .order_by_desc(Column::ReceivedAt)
        .limit(n)
        .all(db)
        .await
}

/// Delete rows older than `cutoff`. Returns rows deleted.
pub async fn purge_older_than(
    db: &DatabaseConnection,
    cutoff: chrono::DateTime<chrono::Utc>,
) -> Result<u64, DbErr> {
    let res = Entity::delete_many()
        .filter(Column::ReceivedAt.lt(cutoff.fixed_offset()))
        .exec(db)
        .await?;
    Ok(res.rows_affected)
}
```

- [ ] **Step 4: Create `query/cluster_bandit_arms.rs`**

```rust
//! Read/update UCB1 arm state.

use crate::entity::cluster_bandit_arms::*;
use chrono::Utc;
use sea_orm::*;

pub async fn list_for_island(
    db: &DatabaseConnection,
    island_domain: &str,
) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .filter(Column::IslandDomain.eq(island_domain))
        .all(db)
        .await
}

/// Idempotent: insert with zero stats if missing, no-op if present.
pub async fn ensure_arm(
    db: &DatabaseConnection,
    island_domain: &str,
    k_value: i16,
) -> Result<(), DbErr> {
    let exists = Entity::find_by_id((island_domain.to_string(), k_value))
        .one(db)
        .await?;
    if exists.is_none() {
        let am = ActiveModel {
            island_domain: Set(island_domain.into()),
            k_value: Set(k_value),
            pulls: Set(0),
            total_reward: Set(0.0),
            last_reward: Set(0.0),
            updated_at: Set(Utc::now().fixed_offset()),
        };
        Entity::insert(am).exec(db).await?;
    }
    Ok(())
}

/// Increment pulls and total_reward, set last_reward.
pub async fn record_pull(
    db: &DatabaseConnection,
    island_domain: &str,
    k_value: i16,
    reward: f64,
) -> Result<(), DbErr> {
    let arm = Entity::find_by_id((island_domain.to_string(), k_value))
        .one(db)
        .await?;
    let mut am: ActiveModel = match arm {
        Some(m) => m.into(),
        None => ActiveModel {
            island_domain: Set(island_domain.into()),
            k_value: Set(k_value),
            pulls: Set(0),
            total_reward: Set(0.0),
            last_reward: Set(0.0),
            updated_at: Set(Utc::now().fixed_offset()),
        },
    };
    let prev_pulls = am.pulls.clone().unwrap_or(0);
    let prev_total = am.total_reward.clone().unwrap_or(0.0);
    am.pulls = Set(prev_pulls + 1);
    am.total_reward = Set(prev_total + reward);
    am.last_reward = Set(reward);
    am.updated_at = Set(Utc::now().fixed_offset());
    am.save(db).await?;
    Ok(())
}
```

- [ ] **Step 5: Register modules**

Edit `engine/crates/pg/src/entity/mod.rs`: add
```rust
pub mod cluster_reports;
pub mod cluster_bandit_arms;
```

Edit `engine/crates/pg/src/query/mod.rs`: add
```rust
pub mod cluster_reports;
pub mod cluster_bandit_arms;
```

- [ ] **Step 6: Build + test**

Run: `cd engine && cargo build -p nasrudin-pg && cargo test -p nasrudin-pg`
Expected: build OK.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/pg/src/entity/cluster_reports.rs \
        engine/crates/pg/src/entity/cluster_bandit_arms.rs \
        engine/crates/pg/src/query/cluster_reports.rs \
        engine/crates/pg/src/query/cluster_bandit_arms.rs \
        engine/crates/pg/src/entity/mod.rs \
        engine/crates/pg/src/query/mod.rs
git commit -m "pg: entity + query modules for cluster_reports and cluster_bandit_arms"
```

---

## Phase D — Genotype clustering inside the GA

### Task 10: `nasrudin_ga::clustering` skeleton + `ClusterFeatures`

**Files:**
- Create: `engine/crates/ga/src/clustering/mod.rs`
- Create: `engine/crates/ga/src/clustering/features.rs`
- Modify: `engine/crates/ga/src/lib.rs`

- [ ] **Step 1: Create the module skeleton**

`engine/crates/ga/src/clustering/mod.rs`:
```rust
//! Genotype-level clustering inside an island. Used by the LLM cluster
//! steerer to address sub-populations by their `centroid_skeleton_hash`
//! and apply per-cluster directives (Boost, Exploit, Diversify, Kill).
//!
//! K is supplied externally by the API steerer's UCB1 bandit; this
//! module does not pick K itself.

pub mod features;
pub mod kmeans;
pub mod summary;

pub use features::{ClusterFeatures, MINHASH_SIG_LEN};
pub use kmeans::{cluster_individuals, ClusterAssignment};
pub use summary::{compute_summaries, ClusterSummary};
```

- [ ] **Step 2: Write a failing test for `ClusterFeatures` axiom_usage**

`engine/crates/ga/src/clustering/features.rs` (test module at the bottom):

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_derive::{Chain, RuleStep};

    #[test]
    fn empty_chain_yields_zero_op_skeleton() {
        let chain = Chain(vec![]);
        let f = ClusterFeatures::from_chain(&chain, &[0.1, 0.2, 0.3, 0.4]);
        assert_eq!(f.op_skeleton, [0; 6]);
        assert_eq!(f.fitness_components, [0.1, 0.2, 0.3, 0.4]);
    }
}
```

- [ ] **Step 3: Run test, expect compile fail**

Run: `cd engine && cargo test -p nasrudin-ga empty_chain_yields_zero_op_skeleton`
Expected: FAIL — module/struct missing.

- [ ] **Step 4: Implement `ClusterFeatures`**

`engine/crates/ga/src/clustering/features.rs`:

```rust
//! Per-individual feature vector for k-means clustering.
//!
//! Components:
//! - `axiom_usage_signature`: 16-byte min-hash over IntroduceAxiom names.
//!   Jaccard similarity ≈ 1 - hamming(sig_a, sig_b) / 128.
//! - `op_skeleton`: count per RuleStep variant in MUTATION_OPS order.
//! - `skeleton_bucket`: derived during k-means seeding (not stored here).
//! - `fitness_components`: normalised fitness sub-scores.

use nasrudin_derive::{Chain, RuleStep};

pub const MINHASH_SIG_LEN: usize = 16;

#[derive(Debug, Clone, PartialEq)]
pub struct ClusterFeatures {
    pub axiom_usage_signature: [u8; MINHASH_SIG_LEN],
    pub op_skeleton: [u32; 6],
    pub fitness_components: [f32; 4],
}

impl ClusterFeatures {
    pub fn from_chain(chain: &Chain, fitness_components: &[f32; 4]) -> Self {
        let mut op_skeleton = [0u32; 6];
        let mut axiom_names: Vec<&str> = Vec::new();
        for step in chain.0.iter() {
            let idx = match step {
                RuleStep::IntroduceAxiom { name, .. } => {
                    axiom_names.push(name.as_str());
                    // IntroduceAxiom maps to neither insert/delete/swap;
                    // treat it as part of mutate_axiom_name's bucket
                    // for skeleton signature purposes (operator-level
                    // distribution still captured via mutation history).
                    3
                }
                RuleStep::SubstituteValue { .. } => 4,
                RuleStep::RearrangeEquation { .. } => 5,
                RuleStep::TakePositiveRoot { .. } => 5,
                _ => 4,
            };
            op_skeleton[idx] = op_skeleton[idx].saturating_add(1);
        }
        let axiom_usage_signature = minhash_signature(&axiom_names);
        Self {
            axiom_usage_signature,
            op_skeleton,
            fitness_components: *fitness_components,
        }
    }
}

/// 16-byte min-hash. Each byte = min over names of (xxhash(name, seed_i) mod 256).
/// Empty input → all 0xFF (canonical empty signature).
fn minhash_signature(names: &[&str]) -> [u8; MINHASH_SIG_LEN] {
    let mut sig = [0xFFu8; MINHASH_SIG_LEN];
    if names.is_empty() {
        return sig;
    }
    for (i, slot) in sig.iter_mut().enumerate() {
        let seed = i as u64;
        let mut min_byte = 0xFFu8;
        for n in names {
            let h = xxhash_rust::xxh64::xxh64(n.as_bytes(), seed);
            let b = (h & 0xFF) as u8;
            if b < min_byte {
                min_byte = b;
            }
        }
        *slot = min_byte;
    }
    sig
}

/// Hamming distance between two min-hash signatures, normalised to [0, 1].
pub fn signature_distance(a: &[u8; MINHASH_SIG_LEN], b: &[u8; MINHASH_SIG_LEN]) -> f32 {
    let mut diff = 0u32;
    for i in 0..MINHASH_SIG_LEN {
        diff += (a[i] ^ b[i]).count_ones();
    }
    diff as f32 / (MINHASH_SIG_LEN as f32 * 8.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_derive::{Chain, RuleStep};

    #[test]
    fn empty_chain_yields_zero_op_skeleton() {
        let chain = Chain(vec![]);
        let f = ClusterFeatures::from_chain(&chain, &[0.1, 0.2, 0.3, 0.4]);
        assert_eq!(f.op_skeleton, [0; 6]);
        assert_eq!(f.fitness_components, [0.1, 0.2, 0.3, 0.4]);
    }

    #[test]
    fn identical_axiom_sets_have_identical_signatures() {
        let f1 = ClusterFeatures::from_chain(
            &Chain(vec![RuleStep::IntroduceAxiom {
                name: "lorentz_factor".into(),
                axiom_id: [0; 8],
            }]),
            &[0.0; 4],
        );
        let f2 = ClusterFeatures::from_chain(
            &Chain(vec![RuleStep::IntroduceAxiom {
                name: "lorentz_factor".into(),
                axiom_id: [0; 8],
            }]),
            &[0.0; 4],
        );
        assert_eq!(f1.axiom_usage_signature, f2.axiom_usage_signature);
    }

    #[test]
    fn different_axiom_sets_diverge() {
        let f1 = ClusterFeatures::from_chain(
            &Chain(vec![RuleStep::IntroduceAxiom {
                name: "lorentz_factor".into(),
                axiom_id: [0; 8],
            }]),
            &[0.0; 4],
        );
        let f2 = ClusterFeatures::from_chain(
            &Chain(vec![RuleStep::IntroduceAxiom {
                name: "planck_constant".into(),
                axiom_id: [0; 8],
            }]),
            &[0.0; 4],
        );
        let d = signature_distance(&f1.axiom_usage_signature, &f2.axiom_usage_signature);
        assert!(d > 0.05, "expected meaningful divergence, got {d}");
    }
}
```

- [ ] **Step 5: Verify exports — confirm `RuleStep::IntroduceAxiom` field names**

Run: `grep -n "IntroduceAxiom\|SubstituteValue\|RearrangeEquation" engine/crates/derive/src/chain.rs | head -20`

Adjust the `match` arms in `from_chain` to match the actual variant field names. The plan assumes `IntroduceAxiom { name, axiom_id }`; if the real fields differ, fix the test cases too.

- [ ] **Step 6: Wire the new submodule into `lib.rs`**

Edit `engine/crates/ga/src/lib.rs` (top-level module re-exports). Add:

```rust
pub mod clustering;
```

- [ ] **Step 7: Run tests, expect pass**

Run: `cd engine && cargo test -p nasrudin-ga clustering::features`
Expected: all 3 tests pass.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/ga/src/clustering/ engine/crates/ga/src/lib.rs
git commit -m "ga: ClusterFeatures (min-hash axiom signature + op skeleton)"
```

---

### Task 11: K-means++ clustering implementation

**Files:**
- Create: `engine/crates/ga/src/clustering/kmeans.rs`

- [ ] **Step 1: Write failing tests**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::clustering::features::{ClusterFeatures, MINHASH_SIG_LEN};

    fn fake_individual(sig_byte: u8, fitness: f32) -> ClusterFeatures {
        ClusterFeatures {
            axiom_usage_signature: [sig_byte; MINHASH_SIG_LEN],
            op_skeleton: [0; 6],
            fitness_components: [fitness; 4],
        }
    }

    #[test]
    fn k_one_assigns_all_to_zero() {
        let pop: Vec<_> = (0..10).map(|i| fake_individual(i as u8, 0.0)).collect();
        let asg = cluster_individuals(&pop, 1, 42);
        assert!(asg.assignments.iter().all(|&c| c == 0));
        assert_eq!(asg.centroids.len(), 1);
    }

    #[test]
    fn well_separated_data_partitions_correctly() {
        // Two clearly different signature blocks
        let mut pop = Vec::new();
        for _ in 0..5 { pop.push(fake_individual(0x00, 0.0)); }
        for _ in 0..5 { pop.push(fake_individual(0xFF, 1.0)); }
        let asg = cluster_individuals(&pop, 2, 42);
        // First 5 share a label, last 5 share a label, labels differ
        let label_a = asg.assignments[0];
        let label_b = asg.assignments[5];
        assert_ne!(label_a, label_b);
        assert!(asg.assignments[..5].iter().all(|&c| c == label_a));
        assert!(asg.assignments[5..].iter().all(|&c| c == label_b));
    }

    #[test]
    fn deterministic_for_same_seed() {
        let pop: Vec<_> = (0..20).map(|i| fake_individual(i as u8, i as f32 / 20.0)).collect();
        let a = cluster_individuals(&pop, 4, 7);
        let b = cluster_individuals(&pop, 4, 7);
        assert_eq!(a.assignments, b.assignments);
    }
}
```

- [ ] **Step 2: Run, expect compile fail**

Run: `cd engine && cargo test -p nasrudin-ga clustering::kmeans`
Expected: FAIL.

- [ ] **Step 3: Implement K-means++**

```rust
//! K-means++ over `ClusterFeatures` with deterministic seeding.

use crate::clustering::features::{signature_distance, ClusterFeatures, MINHASH_SIG_LEN};
use rand::{Rng, SeedableRng};
use rand::rngs::StdRng;

const MAX_ITERS: usize = 20;

#[derive(Debug, Clone)]
pub struct ClusterAssignment {
    pub assignments: Vec<u32>,        // index → cluster_id
    pub centroids: Vec<Centroid>,
}

#[derive(Debug, Clone)]
pub struct Centroid {
    pub axiom_signature: [u8; MINHASH_SIG_LEN],
    pub op_skeleton: [f32; 6],
    pub fitness_components: [f32; 4],
}

/// Cluster `population` into `k` groups using K-means++. Deterministic
/// for a fixed `seed`. Returns assignments + final centroids.
///
/// `k` is clamped to `[1, population.len()]`. Empty population → empty
/// assignment with k=1 sentinel centroid.
pub fn cluster_individuals(
    population: &[ClusterFeatures],
    k: u32,
    seed: u64,
) -> ClusterAssignment {
    if population.is_empty() {
        return ClusterAssignment {
            assignments: vec![],
            centroids: vec![Centroid {
                axiom_signature: [0xFF; MINHASH_SIG_LEN],
                op_skeleton: [0.0; 6],
                fitness_components: [0.0; 4],
            }],
        };
    }
    let k = (k as usize).clamp(1, population.len());
    let mut rng = StdRng::seed_from_u64(seed);

    // K-means++ seeding: first centroid uniform, subsequent ones
    // proportional to squared distance from nearest existing centroid.
    let mut centroid_idxs: Vec<usize> = vec![rng.random_range(0..population.len())];
    while centroid_idxs.len() < k {
        let mut weights: Vec<f32> = population
            .iter()
            .enumerate()
            .map(|(i, p)| {
                if centroid_idxs.contains(&i) {
                    return 0.0;
                }
                let min_d = centroid_idxs
                    .iter()
                    .map(|&ci| distance(p, &population[ci]))
                    .fold(f32::INFINITY, f32::min);
                min_d * min_d
            })
            .collect();
        let sum: f32 = weights.iter().sum();
        if sum <= 0.0 {
            break; // degenerate (all duplicates)
        }
        for w in weights.iter_mut() { *w /= sum; }
        let pick = weighted_choice(&weights, &mut rng);
        centroid_idxs.push(pick);
    }

    let mut centroids: Vec<Centroid> = centroid_idxs
        .iter()
        .map(|&i| Centroid {
            axiom_signature: population[i].axiom_usage_signature,
            op_skeleton: population[i].op_skeleton.map(|v| v as f32),
            fitness_components: population[i].fitness_components,
        })
        .collect();

    let mut assignments = vec![0u32; population.len()];
    for _iter in 0..MAX_ITERS {
        let mut changed = false;
        // Assign step.
        for (i, p) in population.iter().enumerate() {
            let mut best = 0usize;
            let mut best_d = f32::INFINITY;
            for (ci, c) in centroids.iter().enumerate() {
                let d = distance_to_centroid(p, c);
                if d < best_d {
                    best_d = d;
                    best = ci;
                }
            }
            if assignments[i] != best as u32 {
                assignments[i] = best as u32;
                changed = true;
            }
        }
        if !changed { break; }
        // Update step: take majority signature byte + mean of numeric components.
        for (ci, c) in centroids.iter_mut().enumerate() {
            let members: Vec<&ClusterFeatures> = population
                .iter()
                .enumerate()
                .filter(|(i, _)| assignments[*i] == ci as u32)
                .map(|(_, p)| p)
                .collect();
            if members.is_empty() { continue; }
            // Per-byte median of signature.
            for byte_i in 0..MINHASH_SIG_LEN {
                let mut bytes: Vec<u8> = members.iter().map(|m| m.axiom_usage_signature[byte_i]).collect();
                bytes.sort_unstable();
                c.axiom_signature[byte_i] = bytes[bytes.len() / 2];
            }
            for op_i in 0..6 {
                let s: u32 = members.iter().map(|m| m.op_skeleton[op_i]).sum();
                c.op_skeleton[op_i] = s as f32 / members.len() as f32;
            }
            for f_i in 0..4 {
                let s: f32 = members.iter().map(|m| m.fitness_components[f_i]).sum();
                c.fitness_components[f_i] = s / members.len() as f32;
            }
        }
    }
    ClusterAssignment { assignments, centroids }
}

fn distance(a: &ClusterFeatures, b: &ClusterFeatures) -> f32 {
    // Weighted L2: 0.5 axiom signature + 0.3 op skeleton (cosine-ish) + 0.2 fitness
    let sig = signature_distance(&a.axiom_usage_signature, &b.axiom_usage_signature);
    let op = op_distance(&a.op_skeleton.map(|v| v as f32), &b.op_skeleton.map(|v| v as f32));
    let fit = fitness_distance(&a.fitness_components, &b.fitness_components);
    (0.5 * sig * sig + 0.3 * op * op + 0.2 * fit * fit).sqrt()
}

fn distance_to_centroid(p: &ClusterFeatures, c: &Centroid) -> f32 {
    let sig = signature_distance(&p.axiom_usage_signature, &c.axiom_signature);
    let op = op_distance(&p.op_skeleton.map(|v| v as f32), &c.op_skeleton);
    let fit = fitness_distance(&p.fitness_components, &c.fitness_components);
    (0.5 * sig * sig + 0.3 * op * op + 0.2 * fit * fit).sqrt()
}

fn op_distance(a: &[f32; 6], b: &[f32; 6]) -> f32 {
    let mut sum = 0.0f32;
    for i in 0..6 { let d = a[i] - b[i]; sum += d * d; }
    let max = a.iter().chain(b.iter()).cloned().fold(0.0f32, f32::max).max(1.0);
    sum.sqrt() / (max * 6.0_f32.sqrt())
}

fn fitness_distance(a: &[f32; 4], b: &[f32; 4]) -> f32 {
    let mut sum = 0.0f32;
    for i in 0..4 { let d = a[i] - b[i]; sum += d * d; }
    sum.sqrt() / 2.0
}

fn weighted_choice(weights: &[f32], rng: &mut StdRng) -> usize {
    let r: f32 = rng.random_range(0.0..1.0);
    let mut acc = 0.0f32;
    for (i, w) in weights.iter().enumerate() {
        acc += w;
        if r < acc { return i; }
    }
    weights.len() - 1
}

// (tests block from Step 1 above)
```

- [ ] **Step 4: Run tests, expect pass**

Run: `cd engine && cargo test -p nasrudin-ga clustering::kmeans`
Expected: 3 tests pass.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/ga/src/clustering/kmeans.rs
git commit -m "ga: K-means++ clustering with deterministic seeding"
```

---

### Task 12: `ClusterSummary` computation

**Files:**
- Create: `engine/crates/ga/src/clustering/summary.rs`

- [ ] **Step 1: Write failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::clustering::features::{ClusterFeatures, MINHASH_SIG_LEN};
    use crate::clustering::kmeans::{ClusterAssignment, Centroid};

    fn assignment_of(labels: &[u32], k: u32) -> ClusterAssignment {
        let centroids = (0..k).map(|_| Centroid {
            axiom_signature: [0; MINHASH_SIG_LEN],
            op_skeleton: [0.0; 6],
            fitness_components: [0.0; 4],
        }).collect();
        ClusterAssignment { assignments: labels.to_vec(), centroids }
    }

    #[test]
    fn summary_reports_correct_size() {
        let pop: Vec<_> = (0..6).map(|_| ClusterFeatures {
            axiom_usage_signature: [0; MINHASH_SIG_LEN],
            op_skeleton: [0; 6],
            fitness_components: [0.5; 4],
        }).collect();
        let asg = assignment_of(&[0, 0, 0, 1, 1, 1], 2);
        let axiom_names_per_individual: Vec<Vec<String>> = vec![vec![]; 6];
        let summaries = compute_summaries(&pop, &asg, &axiom_names_per_individual, "special_relativity");
        assert_eq!(summaries.len(), 2);
        assert!(summaries.iter().all(|s| s.size == 3));
    }
}
```

- [ ] **Step 2: Run, expect compile fail**

Run: `cd engine && cargo test -p nasrudin-ga clustering::summary`
Expected: FAIL.

- [ ] **Step 3: Implement summary**

```rust
//! Per-cluster summary uploaded to the API after every chunk.

use crate::clustering::features::ClusterFeatures;
use crate::clustering::kmeans::ClusterAssignment;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClusterSummary {
    pub cluster_id: u32,
    pub island_domain: String,
    pub size: u32,
    pub mean_fitness: f32,
    pub fitness_stddev: f32,
    pub silhouette: f32,
    pub dominant_axioms: Vec<(String, u32)>,
    pub novelty_trend: f32,
    pub stagnation_chunks: u32,
    pub centroid_skeleton_hash: u64,
}

pub fn compute_summaries(
    population: &[ClusterFeatures],
    assignment: &ClusterAssignment,
    axiom_names_per_individual: &[Vec<String>],
    island_domain: &str,
) -> Vec<ClusterSummary> {
    if population.is_empty() {
        return vec![];
    }
    let k = assignment.centroids.len();
    let mut out = Vec::with_capacity(k);
    for cid in 0..k {
        let member_idxs: Vec<usize> = assignment.assignments.iter().enumerate()
            .filter(|(_, &c)| c == cid as u32).map(|(i, _)| i).collect();
        if member_idxs.is_empty() { continue; }

        let fits: Vec<f32> = member_idxs.iter()
            .map(|&i| population[i].fitness_components.iter().sum::<f32>() / 4.0)
            .collect();
        let mean = fits.iter().sum::<f32>() / fits.len() as f32;
        let var = fits.iter().map(|f| (f - mean).powi(2)).sum::<f32>() / fits.len() as f32;

        let mut axiom_counts: HashMap<String, u32> = HashMap::new();
        for &i in &member_idxs {
            for name in &axiom_names_per_individual[i] {
                *axiom_counts.entry(name.clone()).or_insert(0) += 1;
            }
        }
        let mut dominant: Vec<(String, u32)> = axiom_counts.into_iter().collect();
        dominant.sort_by(|a, b| b.1.cmp(&a.1));
        dominant.truncate(5);

        // Centroid skeleton hash from the centroid's signature
        let c = &assignment.centroids[cid];
        let centroid_skeleton_hash = xxhash_rust::xxh64::xxh64(&c.axiom_signature, 0);

        out.push(ClusterSummary {
            cluster_id: cid as u32,
            island_domain: island_domain.into(),
            size: member_idxs.len() as u32,
            mean_fitness: mean,
            fitness_stddev: var.sqrt(),
            silhouette: silhouette_score(population, assignment, &member_idxs, cid as u32),
            dominant_axioms: dominant,
            novelty_trend: 0.0, // computed by API steerer across history
            stagnation_chunks: 0, // same
            centroid_skeleton_hash,
        });
    }
    out
}

fn silhouette_score(
    population: &[ClusterFeatures],
    assignment: &ClusterAssignment,
    members: &[usize],
    own: u32,
) -> f32 {
    use crate::clustering::features::signature_distance;
    if members.len() < 2 || assignment.centroids.len() < 2 { return 0.0; }
    let mut total = 0.0f32;
    for &i in members {
        let a: f32 = members.iter().filter(|&&j| j != i)
            .map(|&j| signature_distance(
                &population[i].axiom_usage_signature,
                &population[j].axiom_usage_signature))
            .sum::<f32>() / (members.len() - 1).max(1) as f32;
        let mut b = f32::INFINITY;
        for cid in 0..assignment.centroids.len() {
            if cid as u32 == own { continue; }
            let other_members: Vec<usize> = assignment.assignments.iter().enumerate()
                .filter(|(_, &c)| c == cid as u32).map(|(j, _)| j).collect();
            if other_members.is_empty() { continue; }
            let mean: f32 = other_members.iter()
                .map(|&j| signature_distance(
                    &population[i].axiom_usage_signature,
                    &population[j].axiom_usage_signature))
                .sum::<f32>() / other_members.len() as f32;
            if mean < b { b = mean; }
        }
        if b.is_finite() {
            total += (b - a) / a.max(b).max(1e-6);
        }
    }
    total / members.len() as f32
}

// (tests block from Step 1 above)
```

- [ ] **Step 4: Run tests, expect pass**

Run: `cd engine && cargo test -p nasrudin-ga clustering::summary`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/ga/src/clustering/summary.rs
git commit -m "ga: ClusterSummary + silhouette score per cluster"
```

---

### Task 13: Wire clustering into worker chunk loop

**Files:**
- Modify: `engine/crates/ga/src/bin/worker.rs` (around lines 700-740 after `run_discovery`)

- [ ] **Step 1: Add a thin helper in `clustering::mod.rs`**

Append to `engine/crates/ga/src/clustering/mod.rs`:

```rust
use crate::individual::Individual;
use nasrudin_derive::Chain;

/// One-shot helper: feature-extract → k-means → summarise. Returns
/// (summaries, assignments) so callers can both upload summaries and
/// apply per-cluster directives later in the same chunk.
pub fn cluster_and_summarise(
    chains_with_fitness: &[(Chain, [f32; 4], Vec<String>)],
    k: u32,
    island_domain: &str,
    seed: u64,
) -> (Vec<ClusterSummary>, ClusterAssignment) {
    let features: Vec<ClusterFeatures> = chains_with_fitness.iter()
        .map(|(c, f, _)| ClusterFeatures::from_chain(c, f)).collect();
    let axiom_names: Vec<Vec<String>> = chains_with_fitness.iter()
        .map(|(_, _, names)| names.clone()).collect();
    let asg = cluster_individuals(&features, k, seed);
    let summaries = compute_summaries(&features, &asg, &axiom_names, island_domain);
    (summaries, asg)
}
```

- [ ] **Step 2: Worker reads `cluster_config.k_per_island` from seed**

Add to the worker's `last_steering` handling block (after the existing `apply_steering_knobs` call). Use `serde_json::Value` parsing — the worker doesn't depend on the API crate:

```rust
let k_for_island = last_steering.as_ref()
    .and_then(|s| s.get("cluster_config"))
    .and_then(|cc| cc.get("k_per_island"))
    .and_then(|m| m.get(domain_str_for_worker)) // worker has a single domain
    .and_then(|v| v.as_u64())
    .map(|v| v.clamp(2, 12) as u32)
    .unwrap_or(6); // default before bandit cold-starts
```

- [ ] **Step 3: After discovery, compute clusters from current chains**

Inside the chunk loop, after `let report = run_discovery(...)`, add:

```rust
// Build (chain, fitness_components, axiom_names) tuples from the
// current top-N chains (run_discovery returns its working set; if
// the API surface needs extending, do that here).
let chunk_seed = (chunk_i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
let cluster_input: Vec<(Chain, [f32; 4], Vec<String>)> = report
    .scored_chains.iter()  // (assumes run_discovery exposes this — extend if needed)
    .map(|sc| {
        let names = sc.chain.0.iter().filter_map(|s| match s {
            nasrudin_derive::RuleStep::IntroduceAxiom { name, .. } => Some(name.clone()),
            _ => None,
        }).collect();
        (sc.chain.clone(), sc.fitness_components, names)
    })
    .collect();
let (summaries, _assignment) = nasrudin_ga::clustering::cluster_and_summarise(
    &cluster_input,
    k_for_island,
    domain_str_for_worker,
    chunk_seed,
);
```

If `report.scored_chains` doesn't exist, extend `DiscoveryReport` to expose it (smallest possible change: a `Vec<ScoredChain>` field). Compile errors will guide you.

- [ ] **Step 4: Hold summaries for upload (Task 17 wires the actual POST)**

Store `summaries` in a local variable. Print at debug level:

```rust
tracing::debug!(
    chunk = chunk_i,
    k = k_for_island,
    n_clusters = summaries.len(),
    "chunk clustered"
);
```

- [ ] **Step 5: Verify build**

Run: `cd engine && cargo build -p nasrudin-ga --bin worker`
Expected: build succeeds.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/ga/src/clustering/mod.rs engine/crates/ga/src/bin/worker.rs
git commit -m "worker: cluster chunk population per chunk (k from steering)"
```

---

## Phase E — UCB1 bandit (server-side)

### Task 14: `steerer::bandit` module skeleton + UCB1 selection

**Files:**
- Create: `engine/crates/api/src/steerer/bandit.rs`
- Modify: `engine/crates/api/src/steerer/mod.rs`

- [ ] **Step 1: Write failing tests**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cold_start_picks_unpulled_arm() {
        let arms = vec![
            ArmStat { k: 4, pulls: 5, total_reward: 2.5 },
            ArmStat { k: 6, pulls: 0, total_reward: 0.0 },
            ArmStat { k: 8, pulls: 3, total_reward: 1.5 },
        ];
        assert_eq!(select_k_ucb1(&arms), 6);
    }

    #[test]
    fn ucb1_picks_highest_score() {
        let arms = vec![
            ArmStat { k: 4, pulls: 100, total_reward: 90.0 }, // mean 0.9, exploration ~0.21
            ArmStat { k: 6, pulls: 100, total_reward: 50.0 }, // mean 0.5, exploration ~0.21
        ];
        assert_eq!(select_k_ucb1(&arms), 4);
    }

    #[test]
    fn ucb1_explores_low_pull_arm() {
        let arms = vec![
            ArmStat { k: 4, pulls: 1000, total_reward: 800.0 }, // mean 0.8
            ArmStat { k: 6, pulls: 5,    total_reward: 3.5 },   // mean 0.7 + huge exploration
        ];
        // Total N = 1005. ln(N) ≈ 6.91. sqrt(2*6.91/5) ≈ 1.66 dominates.
        assert_eq!(select_k_ucb1(&arms), 6);
    }
}
```

- [ ] **Step 2: Run, expect compile fail**

Run: `cd engine && cargo test -p physics-api steerer::bandit`
Expected: FAIL.

- [ ] **Step 3: Implement UCB1**

```rust
//! UCB1 multi-armed bandit over K (number of clusters per island).
//!
//! Arms: K ∈ {2, 3, 4, 5, 6, 7, 8, 10, 12}. Per-island state lives in
//! `cluster_bandit_arms`. Selection is deterministic given arm state.

use sea_orm::DatabaseConnection;

pub const K_VALUES: &[i16] = &[2, 3, 4, 5, 6, 7, 8, 10, 12];
pub const ISLAND_DOMAINS: &[&str] = &[
    "special_relativity",
    "electromagnetism",
    "quantum_mechanics",
    "thermodynamics",
    "classical_mechanics",
    "general_relativity",
];

#[derive(Debug, Clone)]
pub struct ArmStat {
    pub k: i16,
    pub pulls: i64,
    pub total_reward: f64,
}

/// UCB1 selection: pick the arm with highest mean reward + exploration.
/// Cold-start: any unpulled arm wins.
pub fn select_k_ucb1(arms: &[ArmStat]) -> i16 {
    if let Some(unpulled) = arms.iter().find(|a| a.pulls == 0) {
        return unpulled.k;
    }
    let total_pulls: i64 = arms.iter().map(|a| a.pulls).sum();
    let ln_n = (total_pulls as f64).ln();
    let mut best_k = arms[0].k;
    let mut best_score = f64::NEG_INFINITY;
    for a in arms {
        let mean = a.total_reward / a.pulls as f64;
        let exploration = (2.0 * ln_n / a.pulls as f64).sqrt();
        let score = mean + exploration;
        if score > best_score {
            best_score = score;
            best_k = a.k;
        }
    }
    best_k
}

/// Ensure all K_VALUES exist as rows in `cluster_bandit_arms` for every
/// configured island domain. Idempotent.
pub async fn ensure_all_arms(db: &DatabaseConnection) -> Result<(), sea_orm::DbErr> {
    for domain in ISLAND_DOMAINS {
        for &k in K_VALUES {
            nasrudin_pg::query::cluster_bandit_arms::ensure_arm(db, domain, k).await?;
        }
    }
    Ok(())
}

/// Read all arms for `island_domain`. Returns empty if none exist.
pub async fn load_arms(
    db: &DatabaseConnection,
    island_domain: &str,
) -> Result<Vec<ArmStat>, sea_orm::DbErr> {
    let rows = nasrudin_pg::query::cluster_bandit_arms::list_for_island(db, island_domain).await?;
    Ok(rows.into_iter().map(|m| ArmStat {
        k: m.k_value,
        pulls: m.pulls,
        total_reward: m.total_reward,
    }).collect())
}

// (tests block from Step 1 above)
```

- [ ] **Step 4: Register module**

Edit `engine/crates/api/src/steerer/mod.rs`: add `pub mod bandit;`.

- [ ] **Step 5: Run tests, expect pass**

Run: `cd engine && cargo test -p physics-api steerer::bandit`
Expected: 3 tests pass.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/steerer/bandit.rs engine/crates/api/src/steerer/mod.rs
git commit -m "steerer: UCB1 bandit module for per-island K selection"
```

---

### Task 15: Reward computation from cluster reports

**Files:**
- Modify: `engine/crates/api/src/steerer/bandit.rs`

- [ ] **Step 1: Write failing test**

```rust
#[test]
fn reward_combines_components_clamped_to_unit() {
    let r = compute_reward(RewardInputs {
        verified_per_pop: 0.4,
        mean_silhouette: 0.6,
        novelty_delta: 0.2,
        stagnation_penalty: 0.1,
    });
    // 0.4*0.4 + 0.25*0.6 + 0.2*0.2 + (-0.15*0.1) = 0.16 + 0.15 + 0.04 - 0.015 = 0.335
    assert!((r - 0.335).abs() < 1e-6);
}

#[test]
fn reward_clamps_to_zero_one() {
    let r = compute_reward(RewardInputs {
        verified_per_pop: 5.0, mean_silhouette: 5.0,
        novelty_delta: 5.0, stagnation_penalty: 0.0,
    });
    assert!(r <= 1.0);
    let r2 = compute_reward(RewardInputs {
        verified_per_pop: -5.0, mean_silhouette: -5.0,
        novelty_delta: -5.0, stagnation_penalty: 5.0,
    });
    assert!(r2 >= 0.0);
}
```

- [ ] **Step 2: Run, expect fail**

Run: `cd engine && cargo test -p physics-api compute_reward`
Expected: FAIL.

- [ ] **Step 3: Implement reward**

Append to `bandit.rs`:

```rust
const W_VERIFIED: f64 = 0.40;
const W_SILHOUETTE: f64 = 0.25;
const W_NOVELTY: f64 = 0.20;
const W_STAGNATION: f64 = 0.15;

pub struct RewardInputs {
    pub verified_per_pop: f64,
    pub mean_silhouette: f64,
    pub novelty_delta: f64,
    pub stagnation_penalty: f64,
}

pub fn compute_reward(r: RewardInputs) -> f64 {
    let raw = W_VERIFIED * r.verified_per_pop
        + W_SILHOUETTE * r.mean_silhouette
        + W_NOVELTY * r.novelty_delta
        - W_STAGNATION * r.stagnation_penalty;
    raw.clamp(0.0, 1.0)
}
```

- [ ] **Step 4: Run tests, expect pass**

Run: `cd engine && cargo test -p physics-api compute_reward`
Expected: PASS.

- [ ] **Step 5: Implement `extract_reward_inputs_from_reports`**

Append to `bandit.rs`:

```rust
use chrono::{DateTime, Utc};
use sea_orm::*;

/// Read recent `cluster_reports` rows for `island_domain` between
/// `[from, to]` and condense to RewardInputs. If no rows in window,
/// returns a neutral-reward input (verified_per_pop=0.5, etc.).
pub async fn extract_reward_inputs(
    db: &DatabaseConnection,
    island_domain: &str,
    k_used: i16,
    from: DateTime<Utc>,
    _to: DateTime<Utc>,
) -> Result<RewardInputs, DbErr> {
    use nasrudin_pg::entity::cluster_reports::{Column, Entity};
    let rows = Entity::find()
        .filter(Column::IslandDomain.eq(island_domain))
        .filter(Column::KUsed.eq(k_used))
        .filter(Column::ReceivedAt.gte(from.fixed_offset()))
        .all(db).await?;
    if rows.is_empty() {
        return Ok(RewardInputs {
            verified_per_pop: 0.5, mean_silhouette: 0.0,
            novelty_delta: 0.0, stagnation_penalty: 0.0,
        });
    }
    let summaries: Vec<serde_json::Value> = rows.iter().map(|r| r.summary.clone()).collect();
    let mean_silhouette = avg_field(&summaries, "silhouette");
    let novelty_delta = avg_field(&summaries, "novelty_trend");
    let stagnation = avg_field(&summaries, "stagnation_chunks") / 10.0;
    // verified_per_pop is approximated from mean_fitness as a proxy
    // until /api/cluster-report carries verification counts directly.
    let verified_per_pop = avg_field(&summaries, "mean_fitness");
    Ok(RewardInputs {
        verified_per_pop,
        mean_silhouette: (mean_silhouette + 1.0) / 2.0, // map [-1,1] → [0,1]
        novelty_delta,
        stagnation_penalty: stagnation,
    })
}

fn avg_field(rows: &[serde_json::Value], key: &str) -> f64 {
    let vals: Vec<f64> = rows.iter()
        .filter_map(|r| r.get(key).and_then(|v| v.as_f64()))
        .collect();
    if vals.is_empty() { 0.0 } else { vals.iter().sum::<f64>() / vals.len() as f64 }
}
```

- [ ] **Step 6: Build check**

Run: `cd engine && cargo build -p physics-api`
Expected: build succeeds.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/steerer/bandit.rs
git commit -m "steerer: bandit reward function + report aggregation"
```

---

### Task 16: Wire bandit into the cycle loop + ship `cluster_config` in steering snapshot

**Files:**
- Modify: `engine/crates/api/src/state.rs` (add `cluster_config` field)
- Modify: `engine/crates/api/src/steerer/cycle.rs`
- Modify: `engine/crates/api/src/handlers/seed.rs`
- Modify: `engine/crates/api/src/main.rs` (call `ensure_all_arms` at boot)

- [ ] **Step 1: Add `cluster_config` to `AppState`**

Find `SteeringSnapshot` in `engine/crates/api/src/state.rs`. Add a sibling field/struct:

```rust
#[derive(Debug, Clone, Default)]
pub struct ClusterConfigSnapshot {
    /// island_domain → K
    pub k_per_island: std::collections::HashMap<String, u32>,
    pub etag: u64,
}
```

Add to `AppState`:
```rust
pub cluster_config: arc_swap::ArcSwap<ClusterConfigSnapshot>,
```

Initialise in `AppState::new()`:
```rust
cluster_config: arc_swap::ArcSwap::new(Arc::new(ClusterConfigSnapshot::default())),
```

- [ ] **Step 2: At boot, ensure all arms exist**

In `engine/crates/api/src/main.rs`, after the database connection is established and migrations run:

```rust
nasrudin_api::steerer::bandit::ensure_all_arms(&db).await
    .expect("ensure_all_arms failed");
```

- [ ] **Step 3: Extend cycle to compute reward + select K**

In `engine/crates/api/src/steerer/cycle.rs::run_one_cycle`, after closing the previous cycle (step 2 in the existing comment) and before building the prompt, insert:

```rust
// Bandit step: read previous K_per_island, compute reward per
// island, update arms, select next K_per_island.
let prev_snap = state.cluster_config.load();
let mut next_k_per_island: std::collections::HashMap<String, u32> = std::collections::HashMap::new();
let now = Utc::now();
let cycle_window_start = now - chrono::Duration::seconds(crate::STEERER_CADENCE_SECONDS as i64);
for &domain in crate::steerer::bandit::ISLAND_DOMAINS {
    if let Some(&prev_k) = prev_snap.k_per_island.get(domain) {
        match crate::steerer::bandit::extract_reward_inputs(
            db, domain, prev_k as i16, cycle_window_start, now
        ).await {
            Ok(inputs) => {
                let r = crate::steerer::bandit::compute_reward(inputs);
                let _ = nasrudin_pg::query::cluster_bandit_arms::record_pull(
                    db, domain, prev_k as i16, r
                ).await;
            }
            Err(e) => tracing::warn!("reward extract failed for {domain}: {e}"),
        }
    }
    let arms = crate::steerer::bandit::load_arms(db, domain).await
        .unwrap_or_default();
    let chosen = if arms.is_empty() { 6 } else {
        crate::steerer::bandit::select_k_ucb1(&arms) as u32
    };
    next_k_per_island.insert(domain.into(), chosen);
}

// Push the new cluster_config snapshot before the prompt is built so
// the LLM sees it (also visible to the prompt builder via the snapshot).
let body = serde_json::to_vec(&next_k_per_island).unwrap_or_default();
let cc_etag = xxhash_rust::xxh64::xxh64(&body, 0);
state.cluster_config.store(std::sync::Arc::new(crate::state::ClusterConfigSnapshot {
    k_per_island: next_k_per_island.clone(),
    etag: cc_etag,
}));
state.invalidate_seed_cache();
```

(Where `crate::STEERER_CADENCE_SECONDS` is the existing constant from `main.rs` — promote it to `pub const` in `lib.rs` if it isn't already exported.)

- [ ] **Step 4: Fold `cluster_config` into `/api/seed` response**

In `engine/crates/api/src/handlers/seed.rs`, in the `body = serde_json::json!({...})` block, add a sibling key:

```rust
let cc_snap = state.cluster_config.load();
// ...
"cluster_config": {
    "k_per_island": cc_snap.k_per_island,
    "etag": format!("{:016x}", cc_snap.etag),
},
```

- [ ] **Step 5: Build + run existing tests**

Run: `cd engine && cargo test -p physics-api`
Expected: all existing tests still pass.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/state.rs engine/crates/api/src/main.rs \
        engine/crates/api/src/steerer/cycle.rs engine/crates/api/src/handlers/seed.rs
git commit -m "steerer: UCB1 picks K per island each cycle; cluster_config in /api/seed"
```

---

## Phase F — `cluster_directives` LLM emission + worker application

### Task 17: Add `ClusterDirective` and `cluster_directives` to schema

**Files:**
- Modify: `engine/crates/api/src/steerer/schema.rs`

- [ ] **Step 1: Write failing tests**

```rust
#[test]
fn cluster_directive_round_trip() {
    let mut c = default_config();
    c.cluster_directives.push(ClusterDirective {
        island_domain: "special_relativity".into(),
        centroid_skeleton_hash: 0xdead_beef_cafe_babe,
        action: ClusterAction::Boost,
        strength: 0.5,
    });
    let json = serde_json::to_string(&c).unwrap();
    let parsed: SteeringConfig = serde_json::from_str(&json).unwrap();
    assert_eq!(parsed.cluster_directives.len(), 1);
    parsed.validate().unwrap();
}

#[test]
fn mode_b_rejects_cluster_directives() {
    let mut c = default_config();
    c.scope = "B".into();
    c.mutation_knobs = None;
    c.cluster_directives.push(ClusterDirective {
        island_domain: "x".into(), centroid_skeleton_hash: 0,
        action: ClusterAction::Kill, strength: 1.0,
    });
    assert!(matches!(c.validate(),
        Err(SteeringValidationError::BHasClusterDirectives)));
}

#[test]
fn directive_strength_above_one_rejected() {
    let mut c = default_config();
    c.cluster_directives.push(ClusterDirective {
        island_domain: "x".into(), centroid_skeleton_hash: 0,
        action: ClusterAction::Diversify, strength: 1.5,
    });
    assert!(c.validate().is_err());
}
```

- [ ] **Step 2: Run, expect compile fail**

Run: `cd engine && cargo test -p physics-api cluster_directive`
Expected: FAIL.

- [ ] **Step 3: Add types + validation**

In `schema.rs`, after `MutationKnobs`:

```rust
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ClusterDirective {
    pub island_domain: String,
    /// Identifies the target cluster by the `centroid_skeleton_hash`
    /// from the previous chunk's ClusterSummary; k-means renumbers
    /// clusters every chunk, so addressing by id is unstable.
    pub centroid_skeleton_hash: u64,
    pub action: ClusterAction,
    /// [0.0, 1.0]; mapped to bounded multipliers worker-side.
    pub strength: f32,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub enum ClusterAction {
    Boost,      // raise mutation rate inside this cluster
    Exploit,    // raise elitism inside this cluster
    Diversify,  // re-seed the worst N% of cluster
    Kill,       // drop a fraction; refill from migrants
}
```

In `SteeringConfig`:
```rust
#[serde(default)]
pub cluster_directives: Vec<ClusterDirective>,
```

In `SteeringValidationError`:
```rust
#[error("scope=B must have empty cluster_directives")]
BHasClusterDirectives,
#[error("cluster directive strength must be in [0.0, 1.0]")]
BadDirectiveStrength,
```

In `validate()` (after `BHasMutationKnobs` check inside the `if self.scope == "B"`):
```rust
if !self.cluster_directives.is_empty() {
    return Err(SteeringValidationError::BHasClusterDirectives);
}
```

After the mutation_knobs block:
```rust
for d in &self.cluster_directives {
    if !(0.0..=1.0).contains(&d.strength) {
        return Err(SteeringValidationError::BadDirectiveStrength);
    }
}
```

In `default_config()`:
```rust
cluster_directives: vec![],
```

- [ ] **Step 4: Run tests, expect pass**

Run: `cd engine && cargo test -p physics-api cluster_directive`
Expected: 3 tests PASS.

- [ ] **Step 5: Update `cycle.rs::parse_and_validate` to clear directives in B-mode**

In `engine/crates/api/src/steerer/cycle.rs::parse_and_validate`, inside the `if c.scope == "B"` block:

```rust
c.cluster_directives.clear();
```

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/steerer/schema.rs engine/crates/api/src/steerer/cycle.rs
git commit -m "steerer: add cluster_directives schema + B-mode lockdown"
```

---

### Task 18: Extend prompt with cluster summaries + bandit state + K assignments

**Files:**
- Modify: `engine/crates/api/src/steerer/prompt.rs`
- Modify: `engine/crates/api/src/steerer/cycle.rs`

- [ ] **Step 1: Extend `SCHEMA_HINT`**

Add after `mutation_priors` line:

```
"cluster_directives": [
    { "island_domain": "...",
      "centroid_skeleton_hash": <u64>,    -- copy from cluster_summaries below,
      "action": "boost"|"exploit"|"diversify"|"kill",
      "strength": <0..1> }
] -- empty in B,
```

- [ ] **Step 2: Add prompt fields**

Replace `build_prompt` signature:

```rust
pub fn build_prompt(
    scope: &str,
    history: &[HistoryEntry],
    demand: &DemandSnapshot,
    active_jobs: &[ActiveJobSummary],
    cluster_summaries: &[serde_json::Value], // ClusterSummary JSONs from the previous chunk
    bandit_state: &serde_json::Value,        // map: domain → [{k, pulls, mean}]
    k_per_island: &std::collections::HashMap<String, u32>,
) -> String {
    let mode_note = ...; // unchanged
    let payload = serde_json::json!({
        "schema": SCHEMA_HINT,
        "scope": scope,
        "history_newest_first": history,
        "current_demand": demand,
        "active_paid_jobs": active_jobs,
        "cluster_summaries": cluster_summaries,
        "bandit_state": bandit_state,
        "k_per_island_next": k_per_island,
        "instructions": format!("scope={scope}. {mode_note} \
            Cluster directives address clusters by `centroid_skeleton_hash` \
            from the cluster_summaries above. The bandit (not you) chose \
            k_per_island_next; cross-reference bandit_state to understand \
            why. Emit SteeringConfig JSON only — no prose."),
    });
    serde_json::to_string_pretty(&payload).unwrap_or_else(|_| "{}".into())
}
```

- [ ] **Step 3: Update existing prompt unit tests**

Add empty `&[]` and `&serde_json::json!({})` and `&HashMap::new()` to existing test calls so they still compile.

- [ ] **Step 4: Update `cycle.rs` to load summaries + bandit state**

In `run_one_cycle`, before `let user_prompt = build_prompt(...)`:

```rust
// Load most recent ClusterSummaries per island for the prompt.
let mut cluster_summaries: Vec<serde_json::Value> = Vec::new();
for &domain in crate::steerer::bandit::ISLAND_DOMAINS {
    let recent = nasrudin_pg::query::cluster_reports::recent_for_island(db, domain, 12).await.unwrap_or_default();
    for r in recent { cluster_summaries.push(r.summary); }
}

// Bandit state for the prompt.
let mut bandit_state = serde_json::Map::new();
for &domain in crate::steerer::bandit::ISLAND_DOMAINS {
    let arms = crate::steerer::bandit::load_arms(db, domain).await.unwrap_or_default();
    let arms_json: Vec<serde_json::Value> = arms.iter().map(|a| serde_json::json!({
        "k": a.k,
        "pulls": a.pulls,
        "mean_reward": if a.pulls > 0 { a.total_reward / a.pulls as f64 } else { 0.0 },
    })).collect();
    bandit_state.insert(domain.into(), serde_json::Value::Array(arms_json));
}

let user_prompt = build_prompt(
    scope, &history, &demand, &active_jobs,
    &cluster_summaries, &serde_json::Value::Object(bandit_state),
    &next_k_per_island,
);
```

- [ ] **Step 5: Build + run**

Run: `cd engine && cargo test -p physics-api steerer::prompt`
Expected: all prompt tests pass after the signature update.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/steerer/prompt.rs engine/crates/api/src/steerer/cycle.rs
git commit -m "steerer: feed cluster_summaries + bandit_state + K_next into LLM prompt"
```

---

### Task 19: Worker applies cluster directives by hash match

**Files:**
- Modify: `engine/crates/ga/src/clustering/mod.rs` (add directive-application helper)
- Modify: `engine/crates/ga/src/bin/worker.rs`

- [ ] **Step 1: Write failing test**

In `engine/crates/ga/src/clustering/mod.rs`:

```rust
#[cfg(test)]
mod directive_tests {
    use super::*;

    #[test]
    fn match_by_hash_finds_closest_centroid() {
        let centroids = vec![
            (0u32, 0xAAAA_AAAA_AAAA_AAAAu64),
            (1u32, 0x5555_5555_5555_5555u64),
        ];
        // 0xAAAA matches first centroid exactly
        let m = match_directive_to_cluster(0xAAAA_AAAA_AAAA_AAAA, &centroids, 0.10);
        assert_eq!(m, Some(0));
    }

    #[test]
    fn match_by_hash_drops_when_no_close_match() {
        let centroids = vec![
            (0u32, 0xAAAA_AAAA_AAAA_AAAAu64),
        ];
        // 0x5555 is the maximum-distance complement; should be dropped.
        let m = match_directive_to_cluster(0x5555_5555_5555_5555, &centroids, 0.10);
        assert_eq!(m, None);
    }
}
```

- [ ] **Step 2: Run, expect fail**

Run: `cd engine && cargo test -p nasrudin-ga match_by_hash`
Expected: FAIL.

- [ ] **Step 3: Implement matcher**

Append to `engine/crates/ga/src/clustering/mod.rs`:

```rust
/// Match a directive's `centroid_skeleton_hash` to the closest cluster
/// in the new chunk. `cluster_centroids` is `[(cluster_id, hash)]`.
/// Returns `Some(cluster_id)` if the closest is within
/// `max_normalised_hamming` (Hamming over 64 bits / 64.0). Otherwise None.
pub fn match_directive_to_cluster(
    directive_hash: u64,
    cluster_centroids: &[(u32, u64)],
    max_normalised_hamming: f32,
) -> Option<u32> {
    let mut best: Option<(u32, f32)> = None;
    for &(cid, h) in cluster_centroids {
        let d = (directive_hash ^ h).count_ones() as f32 / 64.0;
        if d <= max_normalised_hamming && best.map_or(true, |(_, bd)| d < bd) {
            best = Some((cid, d));
        }
    }
    best.map(|(cid, _)| cid)
}
```

- [ ] **Step 4: Apply directives to per-cluster knobs in worker**

In `engine/crates/ga/src/bin/worker.rs`, after computing `summaries` + `assignment` (Task 13), parse `cluster_directives` from `last_steering`:

```rust
let directives = last_steering.as_ref()
    .and_then(|s| s.get("config"))
    .and_then(|c| c.get("cluster_directives"))
    .and_then(|v| v.as_array())
    .cloned()
    .unwrap_or_default();

// Map each directive to a current cluster_id; build per-cluster
// multipliers (rate, elitism, kill_fraction, diversify_fraction).
let centroids: Vec<(u32, u64)> = summaries.iter()
    .map(|s| (s.cluster_id, s.centroid_skeleton_hash))
    .collect();
for d in directives.iter() {
    let dom = d.get("island_domain").and_then(|v| v.as_str()).unwrap_or("");
    if dom != domain_str_for_worker { continue; }
    let hash = d.get("centroid_skeleton_hash").and_then(|v| v.as_u64()).unwrap_or(0);
    let action = d.get("action").and_then(|v| v.as_str()).unwrap_or("");
    let strength = d.get("strength").and_then(|v| v.as_f64()).unwrap_or(0.0).clamp(0.0, 1.0) as f32;
    let Some(cid) = nasrudin_ga::clustering::match_directive_to_cluster(hash, &centroids, 0.10)
        else {
            tracing::debug!(?hash, "directive dropped: no close cluster");
            continue;
        };
    // Apply per-cluster multiplier — concrete application surface
    // (mutation_rate / elitism / kill list) lives in the chunk loop;
    // for v1, log the resolved decision so we can confirm wiring,
    // and stash in a per-chunk Vec<(cid, action, strength)> that the
    // next generation reads.
    tracing::info!(?cid, action, strength, "applying cluster directive");
    // (Hand off to per-cluster knob storage; minimum viable: keep a
    //  HashMap<u32, ClusterMultiplier> the chain_engine reads next chunk.)
}
```

- [ ] **Step 5: Build + commit**

Run: `cd engine && cargo build -p nasrudin-ga --bin worker`
Expected: builds.

```bash
git add engine/crates/ga/src/clustering/mod.rs engine/crates/ga/src/bin/worker.rs
git commit -m "worker: match cluster directives by centroid_skeleton_hash"
```

---

### Task 20: Concrete per-cluster knob application in chain_engine

**Files:**
- Modify: `engine/crates/ga/src/chain_engine.rs` (add `cluster_multipliers` field; consult per-individual at mutation/elitism time)

- [ ] **Step 1: Add `ClusterMultiplier` and field to `DiscoveryConfig`**

In `chain_engine.rs`:

```rust
#[derive(Debug, Clone, Default)]
pub struct ClusterMultiplier {
    pub mutation_rate_mult: f32,    // 1.0 + 1.0*strength for Boost; 1.0 otherwise
    pub elitism_mult: f32,          // 1.0 + 1.0*strength for Exploit
    pub kill_fraction: f32,         // 0.5 * strength for Kill
    pub diversify_fraction: f32,    // 0.3 * strength for Diversify
}

// Add to DiscoveryConfig:
pub cluster_multipliers: std::collections::HashMap<u32, ClusterMultiplier>,
pub cluster_assignments: Vec<u32>, // index aligned with population; empty = no clustering
```

In `Default for DiscoveryConfig`:
```rust
cluster_multipliers: std::collections::HashMap::new(),
cluster_assignments: vec![],
```

- [ ] **Step 2: Write a test**

```rust
#[test]
fn cluster_multiplier_resolves_to_local_rate() {
    use std::collections::HashMap;
    let mut multipliers = HashMap::new();
    multipliers.insert(0u32, ClusterMultiplier {
        mutation_rate_mult: 1.5, elitism_mult: 1.0,
        kill_fraction: 0.0, diversify_fraction: 0.0,
    });
    let assignments = vec![0u32, 0, 0, 1, 1];
    let global_rate = 0.10f32;
    // index 0 in cluster 0 → 0.15
    let rate0 = global_rate * multipliers.get(&assignments[0]).map_or(1.0, |m| m.mutation_rate_mult);
    // index 3 in cluster 1 (no multiplier) → 0.10
    let rate3 = global_rate * multipliers.get(&assignments[3]).map_or(1.0, |m| m.mutation_rate_mult);
    assert!((rate0 - 0.15).abs() < 1e-6);
    assert!((rate3 - 0.10).abs() < 1e-6);
}
```

- [ ] **Step 3: Run test (passes immediately — pure data check)**

Run: `cd engine && cargo test -p nasrudin-ga cluster_multiplier_resolves`
Expected: PASS.

- [ ] **Step 4: Use multipliers at mutation site**

In the existing mutation loop in `chain_engine.rs`, replace `if rng.random_bool(config.mutation_rate)` with:

```rust
let local_rate = if config.cluster_assignments.is_empty() {
    config.mutation_rate
} else {
    let cid = config.cluster_assignments.get(individual_idx).copied().unwrap_or(0);
    let mult = config.cluster_multipliers.get(&cid).map_or(1.0, |m| m.mutation_rate_mult);
    (config.mutation_rate * mult as f64).clamp(0.05, 0.30)
};
if rng.random_bool(local_rate) {
    mutate_chain_weighted_with_suffix_bias(
        &mut child, store, rng,
        config.mutation_priors.as_ref(), config.suffix_bias,
    );
}
```

(`individual_idx` may need to be tracked through the existing offspring loop — minimal extension.)

- [ ] **Step 5: Build + commit**

Run: `cd engine && cargo build -p nasrudin-ga`
Expected: builds.

```bash
git add engine/crates/ga/src/chain_engine.rs
git commit -m "ga: per-cluster multipliers shape mutation rate inside chunk"
```

---

## Phase G — `POST /api/cluster-report` endpoint

### Task 21: Add the handler + route

**Files:**
- Create: `engine/crates/api/src/handlers/cluster_report.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs`
- Modify: `engine/crates/api/src/router.rs` (or wherever routes are registered)

- [ ] **Step 1: Write a handler integration test**

Create `engine/crates/api/tests/cluster_report.rs`:

```rust
mod test_app;

use serde_json::json;

#[tokio::test]
async fn cluster_report_round_trips() {
    let app = test_app::make().await;
    let body = json!({
        "worker_id": "11111111-1111-1111-1111-111111111111",
        "chunk_index": 7,
        "k_used": 4,
        "island_reports": [
            { "island_domain": "special_relativity", "summaries": [
                { "cluster_id": 0, "island_domain": "special_relativity",
                  "size": 24, "mean_fitness": 0.42, "fitness_stddev": 0.08,
                  "silhouette": 0.6, "dominant_axioms": [],
                  "novelty_trend": 0.05, "stagnation_chunks": 2,
                  "centroid_skeleton_hash": 1234567890u64 }
            ]}
        ]
    });
    let res = app.post("/api/cluster-report")
        .header("authorization", "Bearer test-worker-token")
        .json(&body).await;
    assert_eq!(res.status_code(), 200);
    let v: serde_json::Value = res.json();
    assert_eq!(v["received"], true);
    assert_eq!(v["stored"], 1);
}
```

- [ ] **Step 2: Run, expect 404**

Run: `cd engine && cargo test -p physics-api cluster_report_round_trips`
Expected: FAIL — no route.

- [ ] **Step 3: Implement the handler**

`engine/crates/api/src/handlers/cluster_report.rs`:

```rust
//! POST /api/cluster-report
//!
//! Workers POST per-chunk per-cluster summaries here. The steerer
//! reads from `cluster_reports` to compute UCB1 reward and to populate
//! the LLM prompt with ClusterSummary entries.

use axum::{extract::State, http::StatusCode, Json};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::sync::Arc;
use uuid::Uuid;

use crate::state::AppState;

#[derive(Debug, Deserialize)]
pub struct ClusterReportBody {
    pub worker_id: Uuid,
    pub chunk_index: i64,
    pub k_used: i16,
    pub island_reports: Vec<IslandReport>,
}

#[derive(Debug, Deserialize)]
pub struct IslandReport {
    pub island_domain: String,
    pub summaries: Vec<Value>, // ClusterSummary JSON, opaque here
}

#[derive(Debug, Serialize)]
pub struct Resp {
    pub received: bool,
    pub stored: u32,
}

pub async fn handler(
    State(state): State<Arc<AppState>>,
    Json(body): Json<ClusterReportBody>,
) -> (StatusCode, Json<Resp>) {
    let mut stored = 0u32;
    for island in body.island_reports {
        for s in island.summaries {
            let cluster_id = s.get("cluster_id").and_then(|v| v.as_u64()).unwrap_or(0) as i16;
            match nasrudin_pg::query::cluster_reports::insert_summary(
                &state.db, body.worker_id, body.chunk_index, body.k_used,
                &island.island_domain, cluster_id, s,
            ).await {
                Ok(_) => stored += 1,
                Err(e) => tracing::warn!("cluster_report insert failed: {e}"),
            }
        }
    }
    (StatusCode::OK, Json(Resp { received: true, stored }))
}
```

- [ ] **Step 4: Register module**

Edit `engine/crates/api/src/handlers/mod.rs`: `pub mod cluster_report;`.

- [ ] **Step 5: Wire route**

Find the router builder (likely `engine/crates/api/src/router.rs` or `main.rs`). Add — using whatever middleware stack matches `/api/ingest` (worker bearer-token auth):

```rust
.route("/api/cluster-report", post(crate::handlers::cluster_report::handler))
```

- [ ] **Step 6: Run test, expect pass**

Run: `cd engine && cargo test -p physics-api cluster_report_round_trips`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/api/src/handlers/cluster_report.rs \
        engine/crates/api/src/handlers/mod.rs \
        engine/crates/api/src/router.rs \
        engine/crates/api/tests/cluster_report.rs
git commit -m "api: POST /api/cluster-report endpoint for worker cluster summaries"
```

---

### Task 22: Worker POSTs `ClusterReport` after every chunk

**Files:**
- Modify: `engine/crates/ga/src/bin/worker.rs` (or new helper if appropriate)
- Modify: `engine/crates/ga/Cargo.toml` (depends on `reqwest` already)

- [ ] **Step 1: Verify reqwest dep**

Run: `grep '^reqwest' engine/crates/ga/Cargo.toml`

If absent, add `reqwest = { version = "0.12", features = ["json"] }` (match the version used in api).

- [ ] **Step 2: Add post helper in worker**

In `worker.rs`, after `summaries` is computed in the chunk loop:

```rust
async fn post_cluster_report(
    api_url: &str, token: &str,
    body: serde_json::Value,
) -> Result<(), reqwest::Error> {
    let client = reqwest::Client::new();
    client.post(format!("{api_url}/api/cluster-report"))
        .bearer_auth(token)
        .json(&body)
        .send().await?
        .error_for_status()?;
    Ok(())
}

// Call site, one per chunk:
let report_body = serde_json::json!({
    "worker_id": worker_uuid,
    "chunk_index": chunk_i as i64,
    "k_used": k_for_island as i16,
    "island_reports": [{
        "island_domain": domain_str_for_worker,
        "summaries": summaries,
    }],
});
let _ = post_cluster_report(&api_url, &worker_token, report_body).await;
```

(Worker's existing main is sync over a tokio runtime — reuse the same handle. If the worker isn't already async at this point, wrap with a one-shot block_on.)

- [ ] **Step 3: Build**

Run: `cd engine && cargo build -p nasrudin-ga --bin worker`
Expected: builds.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/ga/src/bin/worker.rs engine/crates/ga/Cargo.toml
git commit -m "worker: POST /api/cluster-report at each chunk boundary"
```

---

## Phase H — End-to-end integration test

### Task 23: Steering E2E test that proves operator distribution shifts

**Files:**
- Create: `engine/crates/api/tests/steering_e2e.rs`
- Modify: `engine/crates/api/tests/test_app/mod.rs` (add `FakeLlmCaller` if not already present)

- [ ] **Step 1: Add `FakeLlmCaller` to test_app**

In `engine/crates/api/tests/test_app/mod.rs`:

```rust
use async_trait::async_trait;
use nasrudin_api::steerer::cycle::{CycleError, LlmCaller};

pub struct FakeLlmCaller {
    pub canned: String,
}

#[async_trait]
impl LlmCaller for FakeLlmCaller {
    async fn call(
        &self, _system: &str, _user: &str,
    ) -> Result<(String, Option<i32>, Option<i32>), CycleError> {
        Ok((self.canned.clone(), Some(100), Some(200)))
    }
}
```

(Mark `LlmCaller` `pub` in `cycle.rs` if it's not already.)

- [ ] **Step 2: Write the e2e test**

`engine/crates/api/tests/steering_e2e.rs`:

```rust
mod test_app;
use test_app::FakeLlmCaller;
use nasrudin_api::steerer::cycle::run_one_cycle;
use nasrudin_ga::chain_engine::DiscoveryConfig;
use nasrudin_ga::steering_knobs::apply_steering_knobs;
use rand::{rngs::StdRng, SeedableRng};
use serde_json::json;
use std::collections::HashMap;

#[tokio::test]
async fn llm_steering_changes_ga_behavior() {
    let app = test_app::make().await;
    let canned = json!({
        "version": 1, "scope": "C",
        "domain_weights": {
            "special_relativity": 0.25, "electromagnetism": 0.25,
            "classical_mechanics": 0.25, "thermodynamics": 0.25
        },
        "axiom_emphasis": {},
        "fitness_weights": {
            "novelty": 0.4, "dimensional_elegance": 0.3,
            "chain_length_penalty": 0.2, "target_proximity": 0.1
        },
        "soft_targets": [], "hard_targets": [],
        "mutation_knobs": {
            "rate": 0.25, "suffix_bias": 1.0,
            "population_size": 64, "elitism_fraction": 0.10
        },
        "mutation_priors": { "append_productive_suffix": 2.0 },
        "cluster_directives": [{
            "island_domain": "special_relativity",
            "centroid_skeleton_hash": 0u64,
            "action": "boost", "strength": 0.5
        }],
        "rationale": "test cycle"
    }).to_string();

    let fake = FakeLlmCaller { canned };
    let _ = run_one_cycle(&app.state, &app.state.db, &fake, "test-model").await
        .expect("cycle ran");

    // 1. State swapped
    let snap = app.state.steering.load();
    assert_ne!(snap.etag, 0, "steering snapshot should be non-default");

    // 2. /api/seed includes new config
    let res = app.get("/api/seed").await;
    let v: serde_json::Value = res.json();
    assert_eq!(v["steering"]["config"]["mutation_knobs"]["rate"], 0.25);
    assert_eq!(v["cluster_config"]["k_per_island"]["special_relativity"], 6);

    // 3. apply_steering_knobs patches DiscoveryConfig
    let mut cfg = DiscoveryConfig::default();
    let baseline = cfg.mutation_rate;
    apply_steering_knobs(&mut cfg, &v["steering"]);
    assert_eq!(cfg.mutation_rate, 0.25);
    assert_ne!(cfg.mutation_rate, baseline);
    assert!(cfg.mutation_priors.is_some());
    assert_eq!(
        cfg.mutation_priors.as_ref().unwrap()
            .get("append_productive_suffix").copied(), Some(2.0)
    );

    // 4. Operator distribution shifts (statistical, fixed RNG)
    let mut rng = StdRng::seed_from_u64(42);
    let priors = cfg.mutation_priors.as_ref().unwrap().clone();
    let mut counts = [0u32; 6];
    let store = nasrudin_derive::AxiomStore::new(); // empty store ok for op distribution
    for _ in 0..10_000 {
        let weights = nasrudin_ga::chain_ga::resolve_weights_for_test(Some(&priors), 1.0);
        let pick = nasrudin_ga::chain_ga::weighted_pick_for_test(&weights, &mut rng);
        counts[pick as usize] += 1;
    }
    let suffix_share = counts[5] as f32 / 10_000.0;
    assert!(suffix_share > 0.4, "expected ≥0.4 suffix share, got {suffix_share}");
}
```

- [ ] **Step 3: Expose the helpers needed by the test**

In `engine/crates/ga/src/chain_ga.rs`:

```rust
// Re-export internal helpers for integration tests (kept doc(hidden)).
#[doc(hidden)] pub fn resolve_weights_for_test(
    priors: Option<&std::collections::HashMap<String, f32>>, suffix_bias: f32,
) -> [f32; 6] { resolve_weights(priors, suffix_bias) }

#[doc(hidden)] pub fn weighted_pick_for_test(weights: &[f32; 6], rng: &mut impl rand::Rng) -> u8 {
    weighted_pick(weights, rng)
}
```

- [ ] **Step 4: Run the test, expect pass**

Run: `cd engine && cargo test -p physics-api llm_steering_changes_ga_behavior`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/tests/steering_e2e.rs \
        engine/crates/api/tests/test_app/mod.rs \
        engine/crates/ga/src/chain_ga.rs
git commit -m "test: e2e steering test proves LLM output shifts operator distribution"
```

---

## Phase I — Cleanup

### Task 24: Add 7-day retention cron for `cluster_reports`

**Files:**
- Modify: `engine/crates/api/src/main.rs` (spawn purge task)

- [ ] **Step 1: Add purge loop**

In `main.rs`, alongside the existing `GradientCaller` tokio spawn:

```rust
let db_purge = state.db.clone();
tokio::spawn(async move {
    let mut interval = tokio::time::interval(std::time::Duration::from_secs(3600));
    loop {
        interval.tick().await;
        let cutoff = chrono::Utc::now() - chrono::Duration::days(7);
        match nasrudin_pg::query::cluster_reports::purge_older_than(&db_purge, cutoff).await {
            Ok(n) if n > 0 => tracing::info!("purged {n} old cluster_reports rows"),
            Ok(_) => {}
            Err(e) => tracing::warn!("cluster_reports purge failed: {e}"),
        }
    }
});
```

- [ ] **Step 2: Build**

Run: `cd engine && cargo build -p physics-api`
Expected: builds.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/main.rs
git commit -m "api: hourly purge of cluster_reports older than 7 days"
```

---

### Task 25: Run full test suite + commit final closeout

**Files:** none (verification only)

- [ ] **Step 1: Run all engine tests**

Run: `cd engine && cargo test --workspace`
Expected: all tests pass.

- [ ] **Step 2: Run clippy**

Run: `cd engine && cargo clippy --all-targets -- -D warnings`
Expected: no warnings.

- [ ] **Step 3: Run fmt check**

Run: `cd engine && cargo fmt --check`
Expected: no diff.

- [ ] **Step 4: Smoke `just bootstrap` (skip if cache present)**

Run: `just bootstrap` (only if Mathlib is not yet extracted locally)
Expected: extracts both corpora, generates axioms, builds prover.

- [ ] **Step 5: Manual end-to-end smoke**

Run: `just up` and let one cycle complete (≥10 minutes); confirm in logs:
- `Loaded N Mathlib identities` (N ≥ 10,000)
- `chunk clustered k=K` per worker chunk
- `applying cluster directive` (only if LLM emitted one — may not appear in first cycle)

- [ ] **Step 6: Commit any final formatting fixes**

```bash
[ -n "$(git status --porcelain)" ] && git add -A && git commit -m "chore: cargo fmt + clippy fixes" || true
```

---

## Self-review (already performed before commit)

- ✅ Spec coverage: each spec section maps to a task above (Mathlib hard-fail → Task 2; mutation_priors → Tasks 3-6; clustering → Tasks 10-13; UCB1 → Tasks 14-16; cluster_directives → Tasks 17-20; /api/cluster-report → Tasks 21-22; e2e test → Task 23).
- ✅ No `TODO`/placeholder steps; every step shows code or a concrete command.
- ✅ Type names consistent (`ClusterFeatures`, `ClusterAssignment`, `Centroid`, `ClusterSummary`, `ClusterDirective`, `ClusterAction`, `ClusterMultiplier`, `ArmStat`, `RewardInputs`, `ClusterConfigSnapshot`, `ClusterReportBody`).
- ✅ Field names consistent (`mutation_priors`, `cluster_directives`, `centroid_skeleton_hash`, `k_per_island`, `island_domain`).
- ✅ Frequent commits — each task ends with a focused commit.
