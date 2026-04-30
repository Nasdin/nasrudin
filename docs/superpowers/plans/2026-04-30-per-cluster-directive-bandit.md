# Per-Cluster Directive Multiplier Bandit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the static formula that maps `cluster_directive(action, strength)` to GA multipliers with a per-(island, action, strength_bucket) UCB1 bandit; ship it together with the deferred per-cluster knob application surface so the LLM-driven cluster steering loop self-tunes end-to-end.

**Architecture:** Bandit and application ship together. New PG table `cluster_directive_arms` (600 rows) holds per-arm pulls/total_reward. API steerer snapshots the table each cycle and folds it into `/api/seed`. Workers select multiplier_choice via UCB1 from the snapshot, log the pull, and POST reward feedback at chunk N+1 once the cluster's mean-fitness delta is observable. `DiscoveryConfig.cluster_multipliers` and `cluster_assignments` are added so the GA inner loop adjusts mutation rate / elitism / kill / diversify per individual.

**Tech Stack:** Rust workspace, sea-orm, axum, tokio, PostgreSQL. Uses the existing K-bandit infrastructure (`engine/crates/api/src/steerer/bandit.rs`) as a structural template.

**Spec:** `docs/superpowers/specs/2026-04-30-per-cluster-directive-bandit-design.md`

---

## File Structure

| File | Responsibility |
|------|----------------|
| `engine/crates/pg/src/migrator/m20260430_000019_cluster_directive_arms.rs` | Migration: `cluster_directive_arms` table |
| `engine/crates/pg/src/entity/cluster_directive_arms.rs` | Sea-ORM entity for the arm table |
| `engine/crates/pg/src/query/cluster_directive_arms.rs` | `ensure_arm`, `list_for_slot`, `record_pull`, `snapshot_all` |
| `engine/crates/api/src/steerer/directive_bandit.rs` | Constants, multiplier-choice tables, UCB1 selection, reward computation, ensure_all_arms |
| `engine/crates/api/src/state.rs` | Add `directive_arms: Arc<arc_swap::ArcSwap<DirectiveArmsSnapshot>>` field |
| `engine/crates/api/src/handlers/directive_feedback.rs` | `POST /api/directive-feedback` handler |
| `engine/crates/api/src/handlers/seed.rs:235-280` | Fold `directive_arms` into seed JSON |
| `engine/crates/api/src/steerer/cycle.rs` | Snapshot arms after K-bandit step, ArcSwap-publish |
| `engine/crates/api/src/main.rs` | Register endpoint + `ensure_all_arms_directive` at boot |
| `engine/crates/ga/src/chain_engine.rs` | `ClusterMultiplier` struct + `cluster_multipliers` + `cluster_assignments` fields + per-individual rate resolution at the mutation site |
| `engine/crates/ga/src/clustering/mod.rs` | `bucketize_strength`, `select_multiplier`, `WorkerDirectiveEntry`, `lookup_multiplier_value` |
| `engine/crates/ga/src/bin/worker.rs` | Apply multipliers at chunk N, log entry, attribute reward at chunk N+1, POST feedback batch |
| `engine/crates/api/tests/directive_bandit_e2e.rs` | End-to-end test: skewed seed → UCB1 picks the obvious arm → feedback round-trips |

---

## Phase A — Storage layer

### Task 1: Migration for `cluster_directive_arms`

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260430_000019_cluster_directive_arms.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Create the migration file**

```rust
//! `cluster_directive_arms` — UCB1 arm state for per-cluster directive
//! multipliers. PK is the 4-tuple (island_domain, action, strength_bucket,
//! multiplier_choice). 6 islands × 4 actions × 5 buckets × 5 choices = 600
//! rows materialised at API boot.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterDirectiveArms::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::IslandDomain)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::Action)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::StrengthBucket)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::MultiplierChoice)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::Pulls)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::TotalReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::LastReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::UpdatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .primary_key(
                        Index::create()
                            .col(ClusterDirectiveArms::IslandDomain)
                            .col(ClusterDirectiveArms::Action)
                            .col(ClusterDirectiveArms::StrengthBucket)
                            .col(ClusterDirectiveArms::MultiplierChoice),
                    )
                    .check(Expr::col(ClusterDirectiveArms::Action).is_in([
                        "boost",
                        "exploit",
                        "diversify",
                        "kill",
                    ]))
                    .check(Expr::col(ClusterDirectiveArms::StrengthBucket).between(0, 4))
                    .check(Expr::col(ClusterDirectiveArms::MultiplierChoice).between(0, 4))
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_directive_arms_slot")
                    .table(ClusterDirectiveArms::Table)
                    .col(ClusterDirectiveArms::IslandDomain)
                    .col(ClusterDirectiveArms::Action)
                    .col(ClusterDirectiveArms::StrengthBucket)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(
                Index::drop()
                    .name("idx_directive_arms_slot")
                    .to_owned(),
            )
            .await
            .ok();
        manager
            .drop_table(
                Table::drop()
                    .table(ClusterDirectiveArms::Table)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterDirectiveArms {
    Table,
    IslandDomain,
    Action,
    StrengthBucket,
    MultiplierChoice,
    Pulls,
    TotalReward,
    LastReward,
    UpdatedAt,
}
```

- [ ] **Step 2: Register in `mod.rs`**

Edit `engine/crates/pg/src/migrator/mod.rs`. Add `mod m20260430_000019_cluster_directive_arms;` near the other `mod` lines, and append `Box::new(m20260430_000019_cluster_directive_arms::Migration),` at the end of the `migrations()` vec (after `m20260430_000018_cluster_bandit_arms`).

- [ ] **Step 3: Apply migration**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin && set -a && . ./.env && set +a && cd engine && cargo run --bin migrate --quiet`
Expected: log line `Migration 'm20260430_000019_cluster_directive_arms' has been applied`.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260430_000019_cluster_directive_arms.rs engine/crates/pg/src/migrator/mod.rs
git commit -m "pg: migration for cluster_directive_arms (per-cluster bandit)"
```

---

### Task 2: Sea-ORM entity for `cluster_directive_arms`

**Files:**
- Create: `engine/crates/pg/src/entity/cluster_directive_arms.rs`
- Modify: `engine/crates/pg/src/entity/mod.rs`

- [ ] **Step 1: Create the entity**

```rust
//! UCB1 arm state per (island_domain, action, strength_bucket,
//! multiplier_choice). See migration
//! `m20260430_000019_cluster_directive_arms`.

use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "cluster_directive_arms")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub island_domain: String,
    #[sea_orm(primary_key, auto_increment = false)]
    pub action: String,
    #[sea_orm(primary_key, auto_increment = false)]
    pub strength_bucket: i16,
    #[sea_orm(primary_key, auto_increment = false)]
    pub multiplier_choice: i16,
    pub pulls: i64,
    pub total_reward: f64,
    pub last_reward: f64,
    pub updated_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 2: Register module**

Edit `engine/crates/pg/src/entity/mod.rs`. Add `pub mod cluster_directive_arms;` alphabetically alongside `cluster_reports` / `cluster_bandit_arms`.

- [ ] **Step 3: Verify build**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo build -p nasrudin-pg`
Expected: clean build, no warnings about the new module.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/entity/cluster_directive_arms.rs engine/crates/pg/src/entity/mod.rs
git commit -m "pg: entity for cluster_directive_arms"
```

---

### Task 3: Query helpers for `cluster_directive_arms`

**Files:**
- Create: `engine/crates/pg/src/query/cluster_directive_arms.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`

- [ ] **Step 1: Create the query module**

```rust
//! Read/update UCB1 arm state per (island_domain, action,
//! strength_bucket, multiplier_choice).
//!
//! `ensure_arm` materialises a row at zero stats; `list_for_slot`
//! returns the 5 arms for a (island, action, bucket) trio (used by
//! UCB1 selection); `record_pull` is called when the worker reports
//! reward; `snapshot_all` reads every row for the steerer's per-cycle
//! ArcSwap publication.

use crate::entity::cluster_directive_arms::*;
use chrono::Utc;
use sea_orm::*;

pub async fn ensure_arm(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
) -> Result<(), DbErr> {
    let exists = Entity::find_by_id((
        island_domain.to_string(),
        action.to_string(),
        strength_bucket,
        multiplier_choice,
    ))
    .one(db)
    .await?;
    if exists.is_none() {
        let am = ActiveModel {
            island_domain: Set(island_domain.into()),
            action: Set(action.into()),
            strength_bucket: Set(strength_bucket),
            multiplier_choice: Set(multiplier_choice),
            pulls: Set(0),
            total_reward: Set(0.0),
            last_reward: Set(0.0),
            updated_at: Set(Utc::now().fixed_offset()),
        };
        Entity::insert(am).exec(db).await?;
    }
    Ok(())
}

/// Return the 5 multiplier_choice arms for one (island, action,
/// strength_bucket) slot, ordered by multiplier_choice ASC.
pub async fn list_for_slot(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .filter(Column::IslandDomain.eq(island_domain))
        .filter(Column::Action.eq(action))
        .filter(Column::StrengthBucket.eq(strength_bucket))
        .order_by_asc(Column::MultiplierChoice)
        .all(db)
        .await
}

/// Read every row. Used by the steerer's per-cycle snapshot path —
/// the table is bounded at ~600 rows so a full scan is cheap.
pub async fn snapshot_all(db: &DatabaseConnection) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .order_by_asc(Column::IslandDomain)
        .order_by_asc(Column::Action)
        .order_by_asc(Column::StrengthBucket)
        .order_by_asc(Column::MultiplierChoice)
        .all(db)
        .await
}

/// Increment pulls + total_reward, set last_reward. Caller is
/// responsible for the [0,1] clamp.
pub async fn record_pull(
    db: &DatabaseConnection,
    island_domain: &str,
    action: &str,
    strength_bucket: i16,
    multiplier_choice: i16,
    reward: f64,
) -> Result<(), DbErr> {
    let arm = Entity::find_by_id((
        island_domain.to_string(),
        action.to_string(),
        strength_bucket,
        multiplier_choice,
    ))
    .one(db)
    .await?;
    let (prev_pulls, prev_total) = match &arm {
        Some(m) => (m.pulls, m.total_reward),
        None => (0, 0.0),
    };
    let mut am: ActiveModel = match arm {
        Some(m) => m.into(),
        None => ActiveModel {
            island_domain: Set(island_domain.into()),
            action: Set(action.into()),
            strength_bucket: Set(strength_bucket),
            multiplier_choice: Set(multiplier_choice),
            pulls: Set(0),
            total_reward: Set(0.0),
            last_reward: Set(0.0),
            updated_at: Set(Utc::now().fixed_offset()),
        },
    };
    am.pulls = Set(prev_pulls + 1);
    am.total_reward = Set(prev_total + reward);
    am.last_reward = Set(reward);
    am.updated_at = Set(Utc::now().fixed_offset());
    am.save(db).await?;
    Ok(())
}
```

- [ ] **Step 2: Register module**

Edit `engine/crates/pg/src/query/mod.rs`. Add `pub mod cluster_directive_arms;` alphabetically.

- [ ] **Step 3: Build pg crate**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo build -p nasrudin-pg`
Expected: clean build.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/query/cluster_directive_arms.rs engine/crates/pg/src/query/mod.rs
git commit -m "pg: query helpers for cluster_directive_arms"
```

---

## Phase B — Bandit module + multiplier tables

### Task 4: `directive_bandit` constants + lookup tables

**Files:**
- Create: `engine/crates/api/src/steerer/directive_bandit.rs`
- Modify: `engine/crates/api/src/steerer/mod.rs`

- [ ] **Step 1: Write the failing tests**

Bottom of the new file:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::steerer::schema::ClusterAction;

    #[test]
    fn lookup_returns_table_value() {
        assert!((lookup_multiplier_value(ClusterAction::Boost, 0) - 1.00).abs() < 1e-6);
        assert!((lookup_multiplier_value(ClusterAction::Boost, 4) - 2.00).abs() < 1e-6);
        assert!((lookup_multiplier_value(ClusterAction::Diversify, 0) - 0.00).abs() < 1e-6);
        assert!((lookup_multiplier_value(ClusterAction::Diversify, 4) - 0.50).abs() < 1e-6);
    }

    #[test]
    fn lookup_clamps_out_of_range() {
        // multiplier_choice >= 5 saturates at index 4
        assert!(
            (lookup_multiplier_value(ClusterAction::Boost, 99) - 2.00).abs() < 1e-6
        );
    }

    #[test]
    fn bucketize_strength_boundaries() {
        assert_eq!(bucketize_strength(0.0), 0);
        assert_eq!(bucketize_strength(0.199), 0);
        assert_eq!(bucketize_strength(0.2), 1);
        assert_eq!(bucketize_strength(0.4), 2);
        assert_eq!(bucketize_strength(0.6), 3);
        assert_eq!(bucketize_strength(0.8), 4);
        assert_eq!(bucketize_strength(1.0), 4);
    }

    #[test]
    fn bucketize_strength_clamps() {
        assert_eq!(bucketize_strength(-0.1), 0);
        assert_eq!(bucketize_strength(1.5), 4);
    }
}
```

- [ ] **Step 2: Run tests, expect compile fail**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p physics-api --lib directive_bandit`
Expected: FAIL — module/functions missing.

- [ ] **Step 3: Implement constants + lookup**

Top of `engine/crates/api/src/steerer/directive_bandit.rs`:

```rust
//! UCB1 multi-armed bandit over per-cluster directive multipliers.
//!
//! Each (island_domain, action, strength_bucket) slot holds 5 arms
//! (one per multiplier_choice). The bandit picks the multiplier that
//! the cluster's mean-fitness delta one chunk later rewards. Worker
//! attributes the reward via `centroid_skeleton_hash` matching;
//! unmatched directives produce no reward and don't update arms.
//!
//! Cold-start fallback: until each slot has ≥COLD_START_PULL_THRESHOLD
//! cumulative pulls, the worker uses a static strength→choice mapping
//! instead of UCB1, so the first few cycles produce the same
//! behaviour the static-formula baseline did.

use crate::steerer::schema::ClusterAction;

pub const STRENGTH_BUCKETS: u8 = 5;
pub const MULTIPLIER_CHOICES: u8 = 5;
pub const COLD_START_PULL_THRESHOLD: i64 = 15; // 3 pulls × 5 arms
pub const REWARD_BIAS: f32 = 0.5;
pub const HASH_MATCH_THRESHOLD: f32 = 0.10;

pub const BOOST_MULTIPLIERS: [f32; 5] = [1.00, 1.25, 1.50, 1.75, 2.00];
pub const EXPLOIT_MULTIPLIERS: [f32; 5] = [1.00, 1.25, 1.50, 1.75, 2.00];
pub const DIVERSIFY_FRACTIONS: [f32; 5] = [0.00, 0.10, 0.20, 0.30, 0.50];
pub const KILL_FRACTIONS: [f32; 5] = [0.00, 0.10, 0.20, 0.30, 0.50];

pub const ACTIONS: &[ClusterAction] = &[
    ClusterAction::Boost,
    ClusterAction::Exploit,
    ClusterAction::Diversify,
    ClusterAction::Kill,
];

pub fn action_str(action: ClusterAction) -> &'static str {
    match action {
        ClusterAction::Boost => "boost",
        ClusterAction::Exploit => "exploit",
        ClusterAction::Diversify => "diversify",
        ClusterAction::Kill => "kill",
    }
}

pub fn parse_action(s: &str) -> Option<ClusterAction> {
    match s {
        "boost" => Some(ClusterAction::Boost),
        "exploit" => Some(ClusterAction::Exploit),
        "diversify" => Some(ClusterAction::Diversify),
        "kill" => Some(ClusterAction::Kill),
        _ => None,
    }
}

/// Map a continuous strength in [0, 1] to one of 5 buckets.
/// Strength is clamped first so out-of-range LLM emissions don't
/// blow past the table.
pub fn bucketize_strength(strength: f32) -> u8 {
    let s = strength.clamp(0.0, 1.0);
    ((s * 5.0).floor() as u8).min(4)
}

/// Resolve a multiplier_choice index to its concrete multiplier value
/// for the given action. Out-of-range choice saturates at index 4.
pub fn lookup_multiplier_value(action: ClusterAction, choice: u8) -> f32 {
    let table: &[f32; 5] = match action {
        ClusterAction::Boost => &BOOST_MULTIPLIERS,
        ClusterAction::Exploit => &EXPLOIT_MULTIPLIERS,
        ClusterAction::Diversify => &DIVERSIFY_FRACTIONS,
        ClusterAction::Kill => &KILL_FRACTIONS,
    };
    table[(choice as usize).min(4)]
}
```

- [ ] **Step 4: Register module**

Edit `engine/crates/api/src/steerer/mod.rs`. Add `pub mod directive_bandit;` alongside `pub mod bandit;`.

- [ ] **Step 5: Run tests, expect pass**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p physics-api --lib directive_bandit`
Expected: 4 tests PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/steerer/directive_bandit.rs engine/crates/api/src/steerer/mod.rs
git commit -m "steerer: directive_bandit constants + bucketize/lookup helpers"
```

---

### Task 5: `DirectiveArmStat` + UCB1 selection

**Files:**
- Modify: `engine/crates/api/src/steerer/directive_bandit.rs`

- [ ] **Step 1: Add failing tests**

Add to the existing `tests` module:

```rust
#[test]
fn select_multiplier_cold_start_picks_unpulled() {
    let arms = vec![
        DirectiveArmStat { multiplier_choice: 0, pulls: 4, total_reward: 2.0 },
        DirectiveArmStat { multiplier_choice: 1, pulls: 0, total_reward: 0.0 },
        DirectiveArmStat { multiplier_choice: 2, pulls: 3, total_reward: 1.5 },
    ];
    assert_eq!(select_multiplier(&arms), 1);
}

#[test]
fn select_multiplier_picks_highest_score() {
    let arms = vec![
        DirectiveArmStat { multiplier_choice: 0, pulls: 100, total_reward: 90.0 },
        DirectiveArmStat { multiplier_choice: 1, pulls: 100, total_reward: 50.0 },
    ];
    assert_eq!(select_multiplier(&arms), 0);
}

#[test]
fn select_multiplier_explores_low_pull_arm() {
    let arms = vec![
        DirectiveArmStat { multiplier_choice: 0, pulls: 1000, total_reward: 800.0 },
        DirectiveArmStat { multiplier_choice: 1, pulls: 5, total_reward: 3.5 },
    ];
    assert_eq!(select_multiplier(&arms), 1);
}

#[test]
fn select_multiplier_empty_returns_default() {
    assert_eq!(select_multiplier(&[]), 0);
}

#[test]
fn compute_reward_centers_on_half() {
    // Zero delta → reward 0.5 (the affine bias).
    let r = compute_reward(0.0);
    assert!((r - 0.5).abs() < 1e-6);
}

#[test]
fn compute_reward_clamps() {
    assert_eq!(compute_reward(5.0), 1.0);
    assert_eq!(compute_reward(-5.0), 0.0);
}
```

- [ ] **Step 2: Run tests, expect compile fail**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p physics-api --lib directive_bandit::tests::select`
Expected: FAIL.

- [ ] **Step 3: Implement `DirectiveArmStat` + `select_multiplier` + `compute_reward`**

Append to `directive_bandit.rs` (above the existing `tests` module):

```rust
#[derive(Debug, Clone)]
pub struct DirectiveArmStat {
    pub multiplier_choice: u8,
    pub pulls: i64,
    pub total_reward: f64,
}

/// UCB1 selection over a slot's 5 arms. Cold-start (pulls==0) wins
/// before exploitation; otherwise classic UCB1 with `N` = sum of pulls
/// across the slot (local exploration term, not global).
pub fn select_multiplier(arms: &[DirectiveArmStat]) -> u8 {
    if arms.is_empty() {
        return 0;
    }
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

/// Affine reward map: delta in roughly [-1, 1] → reward in [0, 1].
/// The +0.5 bias keeps a single-chunk regression from saturating an
/// arm to zero.
pub fn compute_reward(fitness_delta: f32) -> f64 {
    (fitness_delta + REWARD_BIAS).clamp(0.0, 1.0) as f64
}

/// Static fallback used until a slot has ≥COLD_START_PULL_THRESHOLD
/// pulls. Linearly maps strength ∈ [0, 1] across the 5-entry table.
pub fn strength_to_static_choice(strength: f32) -> u8 {
    bucketize_strength(strength)
}
```

- [ ] **Step 4: Run tests, expect pass**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p physics-api --lib directive_bandit`
Expected: 10 tests PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/steerer/directive_bandit.rs
git commit -m "steerer: UCB1 select_multiplier + reward computation"
```

---

### Task 6: `ensure_all_arms_directive` boot init

**Files:**
- Modify: `engine/crates/api/src/steerer/directive_bandit.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Append the boot helper**

Append to `directive_bandit.rs`:

```rust
use sea_orm::DatabaseConnection;

pub async fn ensure_all_arms(db: &DatabaseConnection) -> Result<(), sea_orm::DbErr> {
    for &domain in crate::steerer::bandit::ISLAND_DOMAINS {
        for &action in ACTIONS {
            for bucket in 0..STRENGTH_BUCKETS as i16 {
                for choice in 0..MULTIPLIER_CHOICES as i16 {
                    nasrudin_pg::query::cluster_directive_arms::ensure_arm(
                        db,
                        domain,
                        action_str(action),
                        bucket,
                        choice,
                    )
                    .await?;
                }
            }
        }
    }
    Ok(())
}
```

- [ ] **Step 2: Wire into boot**

Edit `engine/crates/api/src/main.rs`. Find the existing `ensure_all_arms` call (the K-bandit one) inside `if let Some(ref pg) = state.pg` and add immediately after it:

```rust
if let Err(e) = physics_api::steerer::directive_bandit::ensure_all_arms(pg).await {
    tracing::warn!(error=%e, "directive_bandit ensure_all_arms failed; \
        per-cluster multipliers will fall back to static formula until next boot");
} else {
    tracing::info!("Cluster directive bandit arms ensured");
}
```

- [ ] **Step 3: Apply migrations + verify boot path compiles**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo build -p physics-api`
Expected: clean build.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/steerer/directive_bandit.rs engine/crates/api/src/main.rs
git commit -m "steerer: ensure_all_arms_directive at API boot (600 rows)"
```

---

## Phase C — Snapshot + `/api/seed` integration

### Task 7: `DirectiveArmsSnapshot` + AppState field

**Files:**
- Modify: `engine/crates/api/src/state.rs`
- Modify: `engine/crates/api/src/main.rs` (initialise field at boot)
- Modify: `engine/crates/api/tests/test_app/mod.rs` (initialise in test harness)

- [ ] **Step 1: Define snapshot struct**

In `engine/crates/api/src/state.rs`, after the `ClusterConfigSnapshot` definition:

```rust
/// Per-(island, action, strength_bucket) bandit-arm snapshot. Workers
/// read this from `/api/seed` to UCB1-select multiplier_choice when
/// the LLM emits a `cluster_directive`. Refreshed by the steerer
/// cycle alongside `steering` / `cluster_config`.
#[derive(Debug, Clone, Default)]
pub struct DirectiveArmsSnapshot {
    /// Each entry: `(island_domain, action_str, strength_bucket,
    /// multiplier_choice, pulls, total_reward)`. Ordered by the
    /// composite key for deterministic etag computation. Bounded
    /// at ~600 rows so a `Vec` is fine.
    pub arms: Vec<DirectiveArmRow>,
    pub etag: u64,
}

#[derive(Debug, Clone)]
pub struct DirectiveArmRow {
    pub island_domain: String,
    pub action: String,
    pub strength_bucket: i16,
    pub multiplier_choice: i16,
    pub pulls: i64,
    pub total_reward: f64,
}
```

- [ ] **Step 2: Add the field to `AppState`**

In `engine/crates/api/src/state.rs`, under `pub cluster_config: …`:

```rust
/// Snapshot of the directive-bandit arm table; refreshed each
/// steerer cycle. Workers fetch via `/api/seed` and call
/// `select_multiplier` to pick the multiplier_choice for each
/// cluster_directive that lands.
pub directive_arms: Arc<arc_swap::ArcSwap<DirectiveArmsSnapshot>>,
```

- [ ] **Step 3: Initialise in `main.rs`**

In `engine/crates/api/src/main.rs`, in the `Arc::new(AppState { … })` literal (next to `cluster_config:`):

```rust
directive_arms: Arc::new(arc_swap::ArcSwap::from_pointee(
    physics_api::state::DirectiveArmsSnapshot::default(),
)),
```

- [ ] **Step 4: Initialise in `test_app/mod.rs`**

In the test harness's `Arc::new(AppState { … })` block (next to `cluster_config:`):

```rust
directive_arms: Arc::new(arc_swap::ArcSwap::from_pointee(
    physics_api::state::DirectiveArmsSnapshot::default(),
)),
```

- [ ] **Step 5: Build**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo build -p physics-api --tests`
Expected: clean build.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/state.rs engine/crates/api/src/main.rs engine/crates/api/tests/test_app/mod.rs
git commit -m "state: DirectiveArmsSnapshot + AppState.directive_arms"
```

---

### Task 8: Steerer cycle snapshots arms + ArcSwap-publishes

**Files:**
- Modify: `engine/crates/api/src/steerer/cycle.rs`

- [ ] **Step 1: Insert the snapshot step**

In `engine/crates/api/src/steerer/cycle.rs::run_one_cycle`, after the existing block that pushes `cluster_config` to ArcSwap (right before "// 4. Build prompt."), add:

```rust
// Snapshot the directive-bandit arm table for the next chunk of
// workers. Bounded at ~600 rows so a full read each cycle is
// cheap; the alternative (worker-local arms) loses cluster-wide
// learning. ArcSwap-published so /api/seed sees it without lock.
let arm_rows = nasrudin_pg::query::cluster_directive_arms::snapshot_all(db)
    .await
    .unwrap_or_default();
let directive_rows: Vec<crate::state::DirectiveArmRow> = arm_rows
    .into_iter()
    .map(|m| crate::state::DirectiveArmRow {
        island_domain: m.island_domain,
        action: m.action,
        strength_bucket: m.strength_bucket,
        multiplier_choice: m.multiplier_choice,
        pulls: m.pulls,
        total_reward: m.total_reward,
    })
    .collect();
let directive_etag = {
    let mut hasher_input = Vec::with_capacity(directive_rows.len() * 32);
    for r in &directive_rows {
        hasher_input.extend_from_slice(r.island_domain.as_bytes());
        hasher_input.extend_from_slice(r.action.as_bytes());
        hasher_input.extend_from_slice(&r.strength_bucket.to_le_bytes());
        hasher_input.extend_from_slice(&r.multiplier_choice.to_le_bytes());
        hasher_input.extend_from_slice(&r.pulls.to_le_bytes());
        hasher_input.extend_from_slice(&r.total_reward.to_le_bytes());
    }
    xxhash_rust::xxh64::xxh64(&hasher_input, 0)
};
state
    .directive_arms
    .store(Arc::new(crate::state::DirectiveArmsSnapshot {
        arms: directive_rows,
        etag: directive_etag,
    }));
state.invalidate_seed_cache();
```

- [ ] **Step 2: Build**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo build -p physics-api`
Expected: clean build.

- [ ] **Step 3: Run existing steerer tests to confirm nothing broke**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p physics-api --lib steerer::`
Expected: all existing tests still pass (the snapshot path doesn't run inside unit tests; only the e2e test in Task 16 exercises it end-to-end).

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/steerer/cycle.rs
git commit -m "steerer: cycle snapshots directive_arms to ArcSwap each cycle"
```

---

### Task 9: Fold `directive_arms` into `/api/seed` JSON

**Files:**
- Modify: `engine/crates/api/src/handlers/seed.rs`

- [ ] **Step 1: Inspect the existing seed JSON build**

Read the existing `body = serde_json::json!({...})` in `engine/crates/api/src/handlers/seed.rs` so the next edit lands cleanly. The block currently produces fields `axioms`, `seed_theorems`, `steering`, `cluster_config`.

- [ ] **Step 2: Compact the snapshot into per-slot rollups**

Add helper at the top of `seed.rs` (or in a private function in the same file):

```rust
use crate::state::DirectiveArmsSnapshot;

/// Convert the flat per-arm snapshot into a per-slot rollup with the
/// 5 multiplier_choice arms inlined. Cuts JSON size from O(rows×30B)
/// to O(slots×120B) — ~120 slots × 120B = 14 KB plain, ~5 KB gzip.
fn directive_arms_compact(snap: &DirectiveArmsSnapshot) -> Vec<serde_json::Value> {
    use std::collections::BTreeMap;
    type SlotKey = (String, String, i16);
    let mut by_slot: BTreeMap<SlotKey, Vec<serde_json::Value>> = BTreeMap::new();
    for r in &snap.arms {
        let key = (r.island_domain.clone(), r.action.clone(), r.strength_bucket);
        let mean = if r.pulls > 0 {
            r.total_reward / r.pulls as f64
        } else {
            0.0
        };
        by_slot.entry(key).or_default().push(serde_json::json!({
            "multiplier_choice": r.multiplier_choice,
            "pulls": r.pulls,
            "mean_reward": mean,
        }));
    }
    by_slot
        .into_iter()
        .map(|((domain, action, bucket), arms)| {
            serde_json::json!({
                "island_domain": domain,
                "action": action,
                "strength_bucket": bucket,
                "arms": arms,
            })
        })
        .collect()
}
```

- [ ] **Step 3: Add the field to the seed JSON**

Edit the existing `let body = serde_json::json!({ ... })` in the seed handler. After the `cluster_config` field add:

```rust
"directive_arms": {
    "snapshot": directive_arms_compact(&state.directive_arms.load()),
    "etag": format!("{:016x}", state.directive_arms.load().etag),
},
```

- [ ] **Step 4: Build**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo build -p physics-api`
Expected: clean build.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/handlers/seed.rs
git commit -m "seed: fold directive_arms snapshot into /api/seed response"
```

---

## Phase D — `POST /api/directive-feedback` endpoint

### Task 10: Endpoint handler

**Files:**
- Create: `engine/crates/api/src/handlers/directive_feedback.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs`
- Modify: `engine/crates/api/src/main.rs` (route registration)

- [ ] **Step 1: Create the handler**

`engine/crates/api/src/handlers/directive_feedback.rs`:

```rust
//! POST /api/directive-feedback
//!
//! Workers POST per-cluster reward observations, batched per chunk.
//! Each entry pulls one (island, action, strength_bucket,
//! multiplier_choice) arm with the observed reward. Reward is the
//! cluster's mean-fitness delta one chunk later, affine-mapped into
//! [0, 1]. Auth reuses the worker bearer token middleware (same as
//! /api/ingest, /api/cluster-report).

use axum::{extract::State, http::StatusCode, Json};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::state::AppState;

#[derive(Debug, Deserialize)]
pub struct DirectiveFeedbackBody {
    pub feedback: Vec<DirectiveFeedbackEntry>,
}

#[derive(Debug, Deserialize)]
pub struct DirectiveFeedbackEntry {
    pub island_domain: String,
    pub action: String, // "boost"|"exploit"|"diversify"|"kill"
    pub strength_bucket: i16,
    pub multiplier_choice: i16,
    pub reward: f64,
}

#[derive(Debug, Serialize)]
pub struct Resp {
    pub received: bool,
    pub applied: u32,
}

pub async fn handler(
    State(state): State<Arc<AppState>>,
    Json(body): Json<DirectiveFeedbackBody>,
) -> (StatusCode, Json<Resp>) {
    let Some(pg) = state.pg.as_ref() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(Resp { received: false, applied: 0 }),
        );
    };
    let mut applied = 0u32;
    for e in body.feedback {
        // Hard-validate action + buckets so a malformed body can't
        // poison an arbitrary row.
        if !matches!(
            e.action.as_str(),
            "boost" | "exploit" | "diversify" | "kill"
        ) {
            tracing::warn!(action = %e.action, "rejected feedback entry: bad action");
            continue;
        }
        if !(0..5).contains(&e.strength_bucket) || !(0..5).contains(&e.multiplier_choice) {
            tracing::warn!(
                strength_bucket = e.strength_bucket,
                multiplier_choice = e.multiplier_choice,
                "rejected feedback entry: bucket/choice out of range"
            );
            continue;
        }
        // Clamp reward to [0, 1] defensively even though the worker is
        // expected to do this — the bandit math assumes bounded rewards.
        let reward = e.reward.clamp(0.0, 1.0);
        match nasrudin_pg::query::cluster_directive_arms::record_pull(
            pg,
            &e.island_domain,
            &e.action,
            e.strength_bucket,
            e.multiplier_choice,
            reward,
        )
        .await
        {
            Ok(_) => applied += 1,
            Err(err) => tracing::warn!(error=%err, "directive_feedback record_pull failed"),
        }
    }
    (StatusCode::OK, Json(Resp { received: true, applied }))
}
```

- [ ] **Step 2: Register handler module**

Edit `engine/crates/api/src/handlers/mod.rs`. Add `pub mod directive_feedback;` alongside `pub mod cluster_report;`.

- [ ] **Step 3: Register route in `main.rs`**

In `engine/crates/api/src/main.rs`, find the existing `/api/cluster-report` route registration (in the `platform_worker` Router builder) and add immediately after it:

```rust
.route(
    "/api/directive-feedback",
    axum::routing::post(handlers::directive_feedback::handler),
)
```

- [ ] **Step 4: Build**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo build -p physics-api`
Expected: clean build.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/handlers/directive_feedback.rs engine/crates/api/src/handlers/mod.rs engine/crates/api/src/main.rs
git commit -m "api: POST /api/directive-feedback endpoint for worker reward batches"
```

---

## Phase E — `ClusterMultiplier` + GA inner-loop application

### Task 11: Add `ClusterMultiplier` + `cluster_multipliers` + `cluster_assignments` to `DiscoveryConfig`

**Files:**
- Modify: `engine/crates/ga/src/chain_engine.rs`

- [ ] **Step 1: Write the failing test**

Append to the existing test module in `engine/crates/ga/src/chain_engine.rs` (at the bottom, inside `#[cfg(test)] mod tests`):

```rust
#[test]
fn cluster_multiplier_lookup_resolves_per_individual_rate() {
    use std::collections::HashMap;
    let mut multipliers = HashMap::new();
    multipliers.insert(0u32, ClusterMultiplier {
        mutation_rate_mult: 1.5,
        elitism_mult: 1.0,
        kill_fraction: 0.0,
        diversify_fraction: 0.0,
    });
    let assignments = vec![0u32, 0, 0, 1, 1];
    let global_rate = 0.10f64;
    let local_rate_for = |idx: usize| {
        let cid = assignments[idx];
        let m = multipliers
            .get(&cid)
            .map(|x| x.mutation_rate_mult as f64)
            .unwrap_or(1.0);
        (global_rate * m).clamp(0.05, 0.30)
    };
    assert!((local_rate_for(0) - 0.15).abs() < 1e-9);
    assert!((local_rate_for(3) - 0.10).abs() < 1e-9);
}
```

- [ ] **Step 2: Run test, expect compile fail**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p nasrudin-ga --lib cluster_multiplier_lookup_resolves_per_individual_rate`
Expected: FAIL — `ClusterMultiplier` not defined.

- [ ] **Step 3: Add `ClusterMultiplier` and the two new fields**

In `engine/crates/ga/src/chain_engine.rs`, after the `DiscoveryConfig` struct closing brace and *before* `impl Default for DiscoveryConfig`:

```rust
/// Per-cluster knob multiplier. Default is identity (1.0× rate, 1.0×
/// elitism, no kill, no diversify). The worker fills these in when a
/// matched LLM `cluster_directive` lands; the GA mutation site applies
/// the multiplier to the per-individual rate / elitism check.
#[derive(Debug, Clone)]
pub struct ClusterMultiplier {
    pub mutation_rate_mult: f32,
    pub elitism_mult: f32,
    pub kill_fraction: f32,
    pub diversify_fraction: f32,
}

impl Default for ClusterMultiplier {
    fn default() -> Self {
        Self {
            mutation_rate_mult: 1.0,
            elitism_mult: 1.0,
            kill_fraction: 0.0,
            diversify_fraction: 0.0,
        }
    }
}
```

In the `DiscoveryConfig` struct, after `pub elitism_fraction: f32,`:

```rust
/// Per-cluster knob overrides. Empty → all individuals use the
/// global rate / elitism unchanged. Populated by the worker after
/// matching LLM `cluster_directives` to the chunk's clusters.
pub cluster_multipliers: std::collections::HashMap<u32, ClusterMultiplier>,
/// Per-individual cluster_id, aligned with the offspring index.
/// Empty → cluster-aware path is skipped and the GA runs in legacy
/// uniform mode.
pub cluster_assignments: Vec<u32>,
```

In `impl Default for DiscoveryConfig`, after `elitism_fraction: 0.0,`:

```rust
cluster_multipliers: std::collections::HashMap::new(),
cluster_assignments: vec![],
```

- [ ] **Step 4: Add the same fields to the test fixtures and the worker `DiscoveryConfig` literals**

Edit each `DiscoveryConfig { … }` literal that doesn't use `..Default::default()`:

In `engine/crates/ga/src/chain_engine.rs` test fixtures (the two `DiscoveryConfig` literals at the bottom of the file used in `discovery_dry_run_populates_report` and `discovery_finds_at_least_some_executable_chains`), add after `elitism_fraction: 0.0,`:

```rust
cluster_multipliers: std::collections::HashMap::new(),
cluster_assignments: vec![],
```

In `engine/crates/ga/src/bin/worker.rs`, find the two `DiscoveryConfig { … }` literals (the main one near line 424 and the research-mode one near line 1017). After `collect_final_population: …,` add:

```rust
cluster_multipliers: std::collections::HashMap::new(),
cluster_assignments: vec![],
```

- [ ] **Step 5: Run test, expect pass**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p nasrudin-ga --lib cluster_multiplier_lookup_resolves_per_individual_rate`
Expected: PASS.

- [ ] **Step 6: Run full ga lib test suite**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p nasrudin-ga --lib`
Expected: all GA tests still pass.

- [ ] **Step 7: Commit**

```bash
git add engine/crates/ga/src/chain_engine.rs engine/crates/ga/src/bin/worker.rs
git commit -m "ga: ClusterMultiplier + cluster_multipliers/cluster_assignments fields"
```

---

### Task 12: Per-individual rate resolution at the GA mutation site

**Files:**
- Modify: `engine/crates/ga/src/chain_engine.rs`

- [ ] **Step 1: Write the failing test**

Add at the bottom of the existing `tests` module:

```rust
#[test]
fn local_rate_with_no_assignments_uses_global() {
    let cfg = DiscoveryConfig::default();
    let r = local_mutation_rate(&cfg, 0);
    assert!((r - cfg.mutation_rate).abs() < 1e-9);
}

#[test]
fn local_rate_with_cluster_multiplier_clamps() {
    let mut cfg = DiscoveryConfig::default();
    cfg.mutation_rate = 0.20;
    cfg.cluster_assignments = vec![0u32, 0, 1, 1];
    cfg.cluster_multipliers.insert(0, ClusterMultiplier {
        mutation_rate_mult: 2.0,
        ..Default::default()
    });
    cfg.cluster_multipliers.insert(1, ClusterMultiplier {
        mutation_rate_mult: 0.0,
        ..Default::default()
    });
    // 0.20 × 2.0 = 0.40 → clamped to 0.30
    assert!((local_mutation_rate(&cfg, 0) - 0.30).abs() < 1e-9);
    // 0.20 × 0.0 = 0.0 → clamped to 0.05
    assert!((local_mutation_rate(&cfg, 2) - 0.05).abs() < 1e-9);
}

#[test]
fn local_rate_unknown_cluster_falls_back_to_global() {
    let mut cfg = DiscoveryConfig::default();
    cfg.mutation_rate = 0.10;
    cfg.cluster_assignments = vec![5u32];
    let r = local_mutation_rate(&cfg, 0);
    assert!((r - 0.10).abs() < 1e-9);
}

#[test]
fn local_elitism_count_with_multiplier() {
    let mut cfg = DiscoveryConfig::default();
    cfg.population_size = 100;
    cfg.elitism_fraction = 0.05; // 5 elites globally
    cfg.cluster_assignments = vec![0u32; 100];
    cfg.cluster_multipliers.insert(0, ClusterMultiplier {
        elitism_mult: 2.0,
        ..Default::default()
    });
    // 5 × 2.0 = 10 elites for cluster 0
    assert_eq!(elite_count_with_cluster_multiplier(&cfg, 0), 10);
}
```

- [ ] **Step 2: Run tests, expect compile fail**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p nasrudin-ga --lib local_rate`
Expected: FAIL — helpers missing.

- [ ] **Step 3: Implement the resolvers**

Add immediately above `pub fn run_discovery(`:

```rust
/// Resolve the per-individual mutation rate. Falls back to global
/// when no cluster assignment is in scope. Clamps to the existing
/// GA bounds [0.05, 0.30] so a directive can't accidentally turn the
/// GA into pure random search or freeze it.
pub fn local_mutation_rate(cfg: &DiscoveryConfig, individual_idx: usize) -> f64 {
    if cfg.cluster_assignments.is_empty() {
        return cfg.mutation_rate;
    }
    let cid = match cfg.cluster_assignments.get(individual_idx) {
        Some(c) => *c,
        None => return cfg.mutation_rate,
    };
    let mult = cfg
        .cluster_multipliers
        .get(&cid)
        .map(|m| m.mutation_rate_mult as f64)
        .unwrap_or(1.0);
    (cfg.mutation_rate * mult).clamp(0.05, 0.30)
}

/// Compute the elitism count for a specific cluster. Used when the
/// GA performs its global elitism step but wants to honour a cluster
/// directive that exploits one cluster harder than another.
pub fn elite_count_with_cluster_multiplier(cfg: &DiscoveryConfig, cluster_id: u32) -> usize {
    let mult = cfg
        .cluster_multipliers
        .get(&cluster_id)
        .map(|m| m.elitism_mult as f64)
        .unwrap_or(1.0);
    let base = (cfg.elitism_fraction.clamp(0.0, 0.2) as f64
        * cfg.population_size as f64)
        .floor();
    (base * mult).round().max(0.0).min(cfg.population_size as f64) as usize
}
```

- [ ] **Step 4: Apply to mutation site in `run_discovery`**

In the body of `run_discovery`, find the existing pair of mutation calls in the offspring loop:

```rust
if rng.random_bool(config.mutation_rate) {
    crate::chain_ga::mutate_chain_weighted_with_suffix_bias(
        &mut c1, store, rng,
        config.mutation_priors.as_ref(), config.suffix_bias,
    );
}
if rng.random_bool(config.mutation_rate) {
    crate::chain_ga::mutate_chain_weighted_with_suffix_bias(
        &mut c2, store, rng,
        config.mutation_priors.as_ref(), config.suffix_bias,
    );
}
```

Replace with:

```rust
let c1_rate = local_mutation_rate(config, offspring.len());
let c2_rate = local_mutation_rate(config, offspring.len() + 1);
if rng.random_bool(c1_rate) {
    crate::chain_ga::mutate_chain_weighted_with_suffix_bias(
        &mut c1, store, rng,
        config.mutation_priors.as_ref(), config.suffix_bias,
    );
}
if rng.random_bool(c2_rate) {
    crate::chain_ga::mutate_chain_weighted_with_suffix_bias(
        &mut c2, store, rng,
        config.mutation_priors.as_ref(), config.suffix_bias,
    );
}
```

- [ ] **Step 5: Run tests, expect pass**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p nasrudin-ga --lib`
Expected: all 65+ ga tests still pass; the 4 new tests pass.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/ga/src/chain_engine.rs
git commit -m "ga: per-cluster mutation rate + elitism count helpers and call site"
```

---

## Phase F — Worker side: apply, log, attribute, report

### Task 13: `WorkerDirectiveEntry` + helpers in `clustering` module

**Files:**
- Modify: `engine/crates/ga/src/clustering/mod.rs`

- [ ] **Step 1: Write failing test**

Add a new test module at the bottom of `engine/crates/ga/src/clustering/mod.rs` (or extend the existing `directive_tests` module):

```rust
#[cfg(test)]
mod directive_log_tests {
    use super::*;

    #[test]
    fn worker_directive_entry_round_trips_basic_fields() {
        let e = WorkerDirectiveEntry {
            centroid_hash_at_apply: 0xdead_beef_cafe_babe,
            action: "boost".into(),
            strength_bucket: 2,
            multiplier_choice: 3,
            mean_fitness_at_apply: 0.42,
        };
        let json = serde_json::to_string(&e).unwrap();
        let parsed: WorkerDirectiveEntry = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.action, "boost");
        assert_eq!(parsed.strength_bucket, 2);
    }
}
```

- [ ] **Step 2: Run test, expect compile fail**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p nasrudin-ga --lib worker_directive_entry`
Expected: FAIL — type missing.

- [ ] **Step 3: Add `WorkerDirectiveEntry`**

Append to `engine/crates/ga/src/clustering/mod.rs`:

```rust
use serde::{Deserialize, Serialize};

/// Per-directive bookkeeping kept worker-local across a single chunk
/// boundary. At chunk N we apply the directive and record this entry;
/// at chunk N+1, after re-clustering, we match by
/// `centroid_hash_at_apply` and emit reward feedback if a current
/// cluster is within Hamming threshold.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkerDirectiveEntry {
    pub centroid_hash_at_apply: u64,
    pub action: String, // "boost"|"exploit"|"diversify"|"kill"
    pub strength_bucket: u8,
    pub multiplier_choice: u8,
    pub mean_fitness_at_apply: f32,
}
```

- [ ] **Step 4: Run test, expect pass**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo test -p nasrudin-ga --lib worker_directive_entry`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/ga/src/clustering/mod.rs
git commit -m "ga: WorkerDirectiveEntry for cross-chunk reward attribution"
```

---

### Task 14: Worker applies directives via bandit + logs entries

**Files:**
- Modify: `engine/crates/ga/src/bin/worker.rs`

- [ ] **Step 1: Add the helper that picks multiplier_choice from a seed payload**

Append to `engine/crates/ga/src/bin/worker.rs` (alongside the other helper fns near `post_cluster_report`):

```rust
/// Look up the 5 arms for a (island, action, strength_bucket) slot
/// from a seed payload's compact `directive_arms` snapshot. Returns
/// an empty Vec if the slot isn't present (cold boot before the
/// steerer cycle has run).
fn directive_arms_for_slot(
    seed_steering_envelope: &serde_json::Value,
    island_domain: &str,
    action: &str,
    strength_bucket: u8,
) -> Vec<(u8, i64, f64)> {
    let Some(snapshot) = seed_steering_envelope
        .get("directive_arms")
        .and_then(|v| v.get("snapshot"))
        .and_then(|v| v.as_array())
    else {
        return vec![];
    };
    for slot in snapshot {
        if slot.get("island_domain").and_then(|v| v.as_str()) == Some(island_domain)
            && slot.get("action").and_then(|v| v.as_str()) == Some(action)
            && slot.get("strength_bucket").and_then(|v| v.as_i64())
                == Some(strength_bucket as i64)
        {
            let arms = slot
                .get("arms")
                .and_then(|v| v.as_array())
                .cloned()
                .unwrap_or_default();
            return arms
                .into_iter()
                .filter_map(|a| {
                    let choice = a.get("multiplier_choice").and_then(|v| v.as_u64())? as u8;
                    let pulls = a.get("pulls").and_then(|v| v.as_i64())?;
                    let mean = a.get("mean_reward").and_then(|v| v.as_f64())?;
                    let total = mean * pulls as f64;
                    Some((choice, pulls, total))
                })
                .collect();
        }
    }
    vec![]
}

/// Pick a multiplier_choice for one (island, action, strength_bucket)
/// slot. Cold-start: use the static linear mapping until ≥15
/// cumulative pulls across the slot's 5 arms. Otherwise UCB1.
fn pick_multiplier_choice(
    arms: &[(u8, i64, f64)],
    strength: f32,
) -> u8 {
    const COLD_START: i64 = 15;
    let total: i64 = arms.iter().map(|(_, p, _)| *p).sum();
    if arms.is_empty() || total < COLD_START {
        return (strength.clamp(0.0, 1.0) * 5.0).floor().min(4.0) as u8;
    }
    let any_unpulled = arms.iter().find(|(_, p, _)| *p == 0).map(|(c, _, _)| *c);
    if let Some(c) = any_unpulled {
        return c;
    }
    let ln_n = (total as f64).ln();
    let mut best_choice = arms[0].0;
    let mut best_score = f64::NEG_INFINITY;
    for &(c, p, t) in arms {
        let mean = if p > 0 { t / p as f64 } else { 0.0 };
        let exploration = (2.0 * ln_n / p as f64).sqrt();
        let score = mean + exploration;
        if score > best_score {
            best_score = score;
            best_choice = c;
        }
    }
    best_choice
}

fn lookup_action_multiplier(action: &str, choice: u8) -> f32 {
    let i = (choice as usize).min(4);
    match action {
        "boost" => [1.00, 1.25, 1.50, 1.75, 2.00][i],
        "exploit" => [1.00, 1.25, 1.50, 1.75, 2.00][i],
        "diversify" => [0.00, 0.10, 0.20, 0.30, 0.50][i],
        "kill" => [0.00, 0.10, 0.20, 0.30, 0.50][i],
        _ => 1.0,
    }
}
```

- [ ] **Step 2: Apply matched directives + log them**

Find the existing block in `engine/crates/ga/src/bin/worker.rs` that matches `cluster_directives` to current cluster ids (the "applying cluster directive" tracing::info call from the prior plan's Task 19). Replace it with the cluster-aware multiplier-application path:

```rust
// Collect into a per-chunk log so chunk N+1 can attribute reward.
let mut worker_directive_log: Vec<nasrudin_ga::clustering::WorkerDirectiveEntry> =
    Vec::new();
let centroids: Vec<(u32, u64)> = summaries
    .iter()
    .map(|s| (s.cluster_id, s.centroid_skeleton_hash))
    .collect();

if let Some(steering_val) = last_steering.as_ref() {
    let directives = steering_val
        .get("config")
        .and_then(|c| c.get("cluster_directives"))
        .and_then(|v| v.as_array())
        .cloned()
        .unwrap_or_default();
    for d in directives.iter() {
        let dom = d.get("island_domain").and_then(|v| v.as_str()).unwrap_or("");
        if dom != canonical_domain {
            continue;
        }
        let hash = d.get("centroid_skeleton_hash").and_then(|v| v.as_u64()).unwrap_or(0);
        let action = d
            .get("action")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        let strength = d.get("strength").and_then(|v| v.as_f64()).unwrap_or(0.0)
            as f32;
        let strength_bucket =
            (strength.clamp(0.0, 1.0) * 5.0).floor().min(4.0) as u8;
        let Some(cid) = nasrudin_ga::clustering::match_directive_to_cluster(
            hash, &centroids, 0.10,
        ) else {
            continue;
        };
        let arms = directive_arms_for_slot(
            steering_val,
            canonical_domain,
            &action,
            strength_bucket,
        );
        let multiplier_choice = pick_multiplier_choice(&arms, strength);
        let mult_value = lookup_action_multiplier(&action, multiplier_choice);
        let m = chunk_config
            .cluster_multipliers
            .entry(cid)
            .or_default();
        match action.as_str() {
            "boost" => m.mutation_rate_mult = mult_value,
            "exploit" => m.elitism_mult = mult_value,
            "diversify" => m.diversify_fraction = mult_value,
            "kill" => m.kill_fraction = mult_value,
            _ => continue,
        }
        let mean_fitness_at_apply = summaries
            .iter()
            .find(|s| s.cluster_id == cid)
            .map(|s| s.mean_fitness)
            .unwrap_or(0.0);
        worker_directive_log.push(
            nasrudin_ga::clustering::WorkerDirectiveEntry {
                centroid_hash_at_apply: hash,
                action: action.clone(),
                strength_bucket,
                multiplier_choice,
                mean_fitness_at_apply,
            },
        );
        tracing::info!(
            cluster_id = cid,
            action = %action,
            strength_bucket,
            multiplier_choice,
            mult_value,
            "applied cluster directive"
        );
    }
}
```

- [ ] **Step 3: Persist `worker_directive_log` across chunks**

The log is computed at chunk N's tail (after summaries) but consumed at chunk N+1's tail. Add a binding outside the chunk loop, near the existing `last_steering` binding:

```rust
let mut prev_directive_log: Vec<nasrudin_ga::clustering::WorkerDirectiveEntry> =
    Vec::new();
```

At the end of each chunk iteration, *replace* `prev_directive_log` with the freshly-built `worker_directive_log` so chunk N+1 reads chunk N's:

```rust
prev_directive_log = std::mem::take(&mut worker_directive_log);
```

- [ ] **Step 4: Build**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo build -p nasrudin-ga --bin worker`
Expected: clean build (lints/cspell warnings ignorable).

- [ ] **Step 5: Commit**

```bash
git add engine/crates/ga/src/bin/worker.rs
git commit -m "worker: apply cluster_directives via bandit; log entries for chunk N+1 attribution"
```

---

### Task 15: Reward attribution + POST `/api/directive-feedback`

**Files:**
- Modify: `engine/crates/ga/src/bin/worker.rs`

- [ ] **Step 1: Add the feedback POST helper**

Append to `engine/crates/ga/src/bin/worker.rs` (alongside `post_cluster_report`):

```rust
/// POST a batch of (arm_key, reward) tuples to /api/directive-feedback.
/// Soft-fails — feedback drops are best-effort, missing pulls just
/// slow the bandit's convergence.
async fn post_directive_feedback(
    cfg: &ApiSubmitConfig,
    feedback: &[serde_json::Value],
) -> anyhow::Result<()> {
    if feedback.is_empty() {
        return Ok(());
    }
    let body = serde_json::json!({ "feedback": feedback });
    let client = reqwest::Client::new();
    let resp = client
        .post(format!("{}/api/directive-feedback", cfg.api_url))
        .bearer_auth(&cfg.worker_key)
        .json(&body)
        .send()
        .await?;
    resp.error_for_status()?;
    Ok(())
}
```

- [ ] **Step 2: Add the attribution step at chunk N+1**

Inside the chunk loop, after `summaries` is built and before the directive-application block (Task 14 step 2), add the chunk-N+1 attribution path:

```rust
// Reward attribution for the previous chunk's directives. Match
// each prev_directive_log entry's centroid hash against the
// current chunk's cluster centroids; if matched, emit a feedback
// entry with the fitness delta as reward.
if !prev_directive_log.is_empty() && api_cfg.is_some() {
    let mut feedback_batch: Vec<serde_json::Value> = Vec::new();
    let centroids_now: Vec<(u32, u64)> = summaries
        .iter()
        .map(|s| (s.cluster_id, s.centroid_skeleton_hash))
        .collect();
    for entry in prev_directive_log.iter() {
        let Some(cid_now) = nasrudin_ga::clustering::match_directive_to_cluster(
            entry.centroid_hash_at_apply,
            &centroids_now,
            0.10,
        ) else {
            continue; // hash drifted; reward unobservable
        };
        let new_mean = summaries
            .iter()
            .find(|s| s.cluster_id == cid_now)
            .map(|s| s.mean_fitness)
            .unwrap_or(entry.mean_fitness_at_apply);
        let delta = new_mean - entry.mean_fitness_at_apply;
        let reward = (delta + 0.5).clamp(0.0, 1.0) as f64;
        feedback_batch.push(serde_json::json!({
            "island_domain": canonical_domain,
            "action": entry.action,
            "strength_bucket": entry.strength_bucket,
            "multiplier_choice": entry.multiplier_choice,
            "reward": reward,
        }));
    }
    if let Some(cfg_for_fb) = api_cfg.as_ref() {
        if let Err(e) = post_directive_feedback(cfg_for_fb, &feedback_batch).await {
            tracing::debug!(error=%e, "directive_feedback post failed (non-blocking)");
        } else if !feedback_batch.is_empty() {
            tracing::info!(
                n = feedback_batch.len(),
                "posted directive_feedback batch"
            );
        }
    }
}
```

- [ ] **Step 3: Build**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin/engine && cargo build -p nasrudin-ga --bin worker`
Expected: clean build.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/ga/src/bin/worker.rs
git commit -m "worker: attribute reward at chunk N+1 and POST /api/directive-feedback batch"
```

---

## Phase G — End-to-end test

### Task 16: `directive_bandit_e2e.rs` integration test

**Files:**
- Create: `engine/crates/api/tests/directive_bandit_e2e.rs`

- [ ] **Step 1: Create the test file**

```rust
//! End-to-end test for the per-cluster directive multiplier bandit.
//!
//! Seeds the directive_arms table with a deliberate skew so one
//! multiplier_choice wins UCB1 unambiguously. Then runs a steerer
//! cycle (with a FakeLlmCaller emitting one cluster_directive),
//! reads /api/seed, and asserts the snapshot carries the seeded skew.
//! Finally posts a directive_feedback batch and asserts record_pull
//! flipped the rows.

mod test_app;

use async_trait::async_trait;
use serde_json::json;

use physics_api::steerer::cycle::{run_one_cycle, CycleError, LlmCaller};

struct FakeLlmCaller {
    canned: String,
}

#[async_trait]
impl LlmCaller for FakeLlmCaller {
    async fn call(
        &self,
        _system: &str,
        _user: &str,
    ) -> Result<(String, Option<i32>, Option<i32>), CycleError> {
        Ok((self.canned.clone(), Some(50), Some(80)))
    }
}

#[tokio::test]
async fn directive_arms_snapshot_carries_seeded_skew() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };

    // Seed a single arm with high mean reward so UCB1 must pick it.
    physics_api::steerer::directive_bandit::ensure_all_arms(&app.pg)
        .await
        .expect("ensure arms");
    for choice in 0..5 {
        let reward = if choice == 3 { 0.9 } else { 0.1 };
        for _ in 0..10 {
            nasrudin_pg::query::cluster_directive_arms::record_pull(
                &app.pg,
                "special_relativity",
                "boost",
                2,
                choice,
                reward,
            )
            .await
            .unwrap();
        }
    }

    // Run a cycle to publish the snapshot to ArcSwap and seed cache.
    let canned = json!({
        "version": 1,
        "scope": "C",
        "domain_weights": {
            "special_relativity": 0.25,
            "electromagnetism": 0.25,
            "classical_mechanics": 0.25,
            "thermodynamics": 0.25
        },
        "axiom_emphasis": {},
        "fitness_weights": {
            "novelty": 0.4,
            "dimensional_elegance": 0.3,
            "chain_length_penalty": 0.2,
            "target_proximity": 0.1
        },
        "soft_targets": [],
        "hard_targets": [],
        "mutation_knobs": {
            "rate": 0.20,
            "suffix_bias": 0.5,
            "population_size": 64,
            "elitism_fraction": 0.05
        },
        "mutation_priors": {},
        "cluster_directives": [{
            "island_domain": "special_relativity",
            "centroid_skeleton_hash": 0u64,
            "action": "boost",
            "strength": 0.5
        }],
        "rationale": "directive bandit e2e"
    })
    .to_string();
    let fake = FakeLlmCaller { canned };
    run_one_cycle(&app.state(), &app.pg, &fake, "test-model")
        .await
        .expect("cycle ran");

    // Read /api/seed and assert the directive_arms slot has the seeded skew.
    let resp = test_app::get(&app, "/api/seed").await;
    assert_eq!(resp.status, axum::http::StatusCode::OK);
    let v: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    let snapshot = v["directive_arms"]["snapshot"]
        .as_array()
        .expect("directive_arms.snapshot is an array");
    let slot = snapshot
        .iter()
        .find(|s| {
            s["island_domain"] == "special_relativity"
                && s["action"] == "boost"
                && s["strength_bucket"] == 2
        })
        .expect("seeded slot present");
    let arm_3 = slot["arms"]
        .as_array()
        .unwrap()
        .iter()
        .find(|a| a["multiplier_choice"] == 3)
        .unwrap();
    assert_eq!(arm_3["pulls"], 10);
    assert!((arm_3["mean_reward"].as_f64().unwrap() - 0.9).abs() < 1e-6);

    // Locally exercise the worker's UCB1: arm 3 should win.
    let arms_local: Vec<(u8, i64, f64)> = slot["arms"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| {
            let c = a["multiplier_choice"].as_u64().unwrap() as u8;
            let p = a["pulls"].as_i64().unwrap();
            let mean = a["mean_reward"].as_f64().unwrap();
            (c, p, mean * p as f64)
        })
        .collect();
    let pick = ucb1_pick(&arms_local);
    assert_eq!(pick, 3, "UCB1 should pick the seeded high-reward arm");
}

/// Mirror of the worker's pick_multiplier_choice for the e2e check.
/// Lives in the test so we don't pull in the worker binary.
fn ucb1_pick(arms: &[(u8, i64, f64)]) -> u8 {
    let total: i64 = arms.iter().map(|(_, p, _)| *p).sum();
    if total < 15 {
        return 0;
    }
    if let Some((c, _, _)) = arms.iter().find(|(_, p, _)| *p == 0) {
        return *c;
    }
    let ln_n = (total as f64).ln();
    let mut best = arms[0].0;
    let mut best_score = f64::NEG_INFINITY;
    for &(c, p, t) in arms {
        let mean = if p > 0 { t / p as f64 } else { 0.0 };
        let exploration = (2.0 * ln_n / p as f64).sqrt();
        let score = mean + exploration;
        if score > best_score {
            best_score = score;
            best = c;
        }
    }
    best
}

#[tokio::test]
async fn directive_feedback_records_pulls() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };
    physics_api::steerer::directive_bandit::ensure_all_arms(&app.pg)
        .await
        .expect("ensure arms");

    // Mount the endpoint locally on the existing test router.
    let router = app.router.clone().route(
        "/api/directive-feedback",
        axum::routing::post(physics_api::handlers::directive_feedback::handler)
            .with_state(app.state()),
    );

    use axum::body::{to_bytes, Body};
    use axum::http::Request;
    use tower::util::ServiceExt;

    let body = json!({
        "feedback": [
            {
                "island_domain": "special_relativity",
                "action": "boost",
                "strength_bucket": 1,
                "multiplier_choice": 2,
                "reward": 0.7
            },
            {
                "island_domain": "thermodynamics",
                "action": "exploit",
                "strength_bucket": 4,
                "multiplier_choice": 0,
                "reward": 0.3
            }
        ]
    });
    let req = Request::builder()
        .method("POST")
        .uri("/api/directive-feedback")
        .header(axum::http::header::CONTENT_TYPE, "application/json")
        .body(Body::from(serde_json::to_vec(&body).unwrap()))
        .unwrap();
    let resp = router.oneshot(req).await.unwrap();
    assert_eq!(resp.status(), axum::http::StatusCode::OK);
    let body_bytes = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body_bytes).unwrap();
    assert_eq!(v["received"], true);
    assert_eq!(v["applied"], 2);

    // Verify the rows actually moved.
    let arms = nasrudin_pg::query::cluster_directive_arms::list_for_slot(
        &app.pg,
        "special_relativity",
        "boost",
        1,
    )
    .await
    .unwrap();
    let chosen = arms
        .iter()
        .find(|a| a.multiplier_choice == 2)
        .expect("seeded slot exists");
    assert_eq!(chosen.pulls, 1);
    assert!((chosen.last_reward - 0.7).abs() < 1e-6);
}

#[tokio::test]
async fn directive_feedback_rejects_bad_action_and_buckets() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };
    physics_api::steerer::directive_bandit::ensure_all_arms(&app.pg)
        .await
        .expect("ensure arms");
    let router = app.router.clone().route(
        "/api/directive-feedback",
        axum::routing::post(physics_api::handlers::directive_feedback::handler)
            .with_state(app.state()),
    );
    use axum::body::{to_bytes, Body};
    use axum::http::Request;
    use tower::util::ServiceExt;

    // Two malformed entries should be silently dropped (handler logs
    // and continues), so applied should be 0.
    let body = json!({
        "feedback": [
            { "island_domain": "x", "action": "explode", "strength_bucket": 0,
              "multiplier_choice": 0, "reward": 0.5 },
            { "island_domain": "x", "action": "boost", "strength_bucket": 99,
              "multiplier_choice": 0, "reward": 0.5 }
        ]
    });
    let req = Request::builder()
        .method("POST")
        .uri("/api/directive-feedback")
        .header(axum::http::header::CONTENT_TYPE, "application/json")
        .body(Body::from(serde_json::to_vec(&body).unwrap()))
        .unwrap();
    let resp = router.oneshot(req).await.unwrap();
    assert_eq!(resp.status(), axum::http::StatusCode::OK);
    let body_bytes = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    let v: serde_json::Value = serde_json::from_slice(&body_bytes).unwrap();
    assert_eq!(v["received"], true);
    assert_eq!(v["applied"], 0);
}
```

- [ ] **Step 2: Run the test**

Run: `cd /Volumes/CORSAIR/code/personal/nasrudin && set -a && . ./.env && set +a && cd engine && TEST_DATABASE_URL=$DATABASE_URL cargo test -p physics-api --test directive_bandit_e2e`
Expected: 3 tests PASS.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/tests/directive_bandit_e2e.rs
git commit -m "test: e2e directive bandit — seeded skew → snapshot → UCB1 pick + feedback round-trip"
```

---

## Phase H — Closeout

### Task 17: Final test sweep + commit

**Files:** none (verification only)

- [ ] **Step 1: Run all targeted test suites**

Run, in order:

```bash
cd /Volumes/CORSAIR/code/personal/nasrudin/engine
cargo test -p nasrudin-pg --lib
cargo test -p nasrudin-ga --lib
cargo test -p physics-api --lib steerer::
cargo test -p physics-api --lib directive_bandit
```

Expected: all green. Note: `cargo test --workspace` may still surface pre-existing admin/* compile errors that predate this work; those are not in scope.

- [ ] **Step 2: Run the e2e suite (requires PG up)**

```bash
cd /Volumes/CORSAIR/code/personal/nasrudin && set -a && . ./.env && set +a && cd engine \
  && TEST_DATABASE_URL=$DATABASE_URL cargo test -p physics-api --test steering_e2e \
  && TEST_DATABASE_URL=$DATABASE_URL cargo test -p physics-api --test directive_bandit_e2e
```

Expected: all e2e tests pass.

- [ ] **Step 3: Format + clippy on the changed crates**

```bash
cd /Volumes/CORSAIR/code/personal/nasrudin/engine
cargo fmt --check -p nasrudin-pg -p nasrudin-ga -p physics-api || cargo fmt -p nasrudin-pg -p nasrudin-ga -p physics-api
cargo clippy -p nasrudin-pg -p nasrudin-ga -p physics-api --all-targets -- -D warnings
```

Expected: zero warnings on the touched crates.

- [ ] **Step 4: Commit any formatting fixes**

```bash
[ -n "$(git status --porcelain)" ] && git add -A && git commit -m "chore: cargo fmt on touched crates" || true
```

---

## Self-Review

**Spec coverage** — every spec section maps to a task:

- Strength bucketing → Task 4
- Multiplier-choice tables → Task 4
- `cluster_directive_arms` table → Task 1
- UCB1 selection → Task 5
- Reward attribution → Task 5 (`compute_reward`) + Task 15 (worker attribution)
- `POST /api/directive-feedback` → Task 10
- `directive_arms` snapshot in `/api/seed` → Tasks 7, 8, 9
- Worker-side application → Task 14
- Bootstrap fallback (cold-start static formula) → Task 14 step 1 (`pick_multiplier_choice` early-return)
- Configuration constants → Task 4
- Per-cluster knob application surface (the deferred "Scope dependency") — `ClusterMultiplier` + `cluster_multipliers`/`cluster_assignments` → Task 11; per-individual rate at the mutation site → Task 12
- Migration & rollout → Tasks 1, 2, 3, 6 (boot init), 7 (test_app init)
- Failure modes → Task 10 (handler validates), Task 14 (cold-start fallback), Task 15 (drop unmatched), Task 12 (bounds clamp)
- Test coverage (unit) → Task 4 (bucketize + lookup), Task 5 (UCB1 + reward), Task 11 (multiplier resolve), Task 12 (local rate), Task 13 (entry round-trip)
- Test coverage (integration) → Task 16

**Placeholder scan** — no TBD/TODO/handle-edge-cases. Every code step shows the actual code.

**Type consistency** — `ClusterMultiplier` fields (`mutation_rate_mult`, `elitism_mult`, `kill_fraction`, `diversify_fraction`) consistent across Task 11, Task 14, Task 12. `WorkerDirectiveEntry` field names (`centroid_hash_at_apply`, `action`, `strength_bucket`, `multiplier_choice`, `mean_fitness_at_apply`) consistent in Tasks 13, 14, 15. `DirectiveArmRow` field names match between `state.rs` (Task 7), the cycle snapshot (Task 8), and the seed JSON helper (Task 9).
