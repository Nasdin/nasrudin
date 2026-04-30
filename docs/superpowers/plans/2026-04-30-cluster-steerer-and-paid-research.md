# Cluster Steerer + Paid Researcher Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship the LLM-driven cluster steerer + the $19/mo Researcher tier (paid GA slices targeting user-supplied conjectures), per `docs/superpowers/specs/2026-04-30-cluster-steerer-and-paid-research-design.md`.

**Architecture:** Periodic Kimi 2.6 call (DO Gradient) reads aggregate user demand + last 10 cycles' outcomes, emits a `SteeringConfig` (mode C: full GA control; mode B when paid jobs are running: mutation knobs locked). Workers fetch config via `/api/steering` (folded into existing `/api/seed` ETag flow). Paid Researcher jobs ride on the existing `conjecture_jobs` spine extended with a 96-lake-slot-hour quota; workers atomically claim jobs via `/api/jobs/claim` with lease/heartbeat, run dedicated GA islands, stream progress via SSE. Soft floor 10% of cluster capacity is reserved for the explorer fleet.

**Tech Stack:** Rust + Axum (API), SeaORM + PostgreSQL (paid-job state, steering history), RocksDB (theorem store, kept untouched), `nasrudin_llm` Registry (new `gradient` provider), ArcSwap for hot-reload, SSE for progress, xxhash64 for ETag.

**Phases:**
- 1 — Schema + Gradient provider plumbing (foundation)
- 2 — Steering core (cycle loop, prompt, validation, persist)
- 3 — Steering distribution (`/api/steering`, ArcSwap, worker hot-reload, mutation-knob plumbing)
- 4 — Paid job lifecycle (quota math, claim, heartbeat, reaper)
- 5 — User-facing paid flow (create, list, SSE, cancel/refund)
- 6 — Worker integration (claim poll, slice runner, target injection)
- 7 — Observability + admin
- 8 — Soak + cutover

---

## Phase 1 — Schema + Gradient provider plumbing

### Task 1.1: Migration — `cluster_steering` table

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260501_000001_cluster_steering.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs` (register migration)

- [ ] **Step 1: Write the migration**

```rust
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, m: &SchemaManager) -> Result<(), DbErr> {
        m.create_table(
            Table::create()
                .table(ClusterSteering::Table)
                .col(ColumnDef::new(ClusterSteering::Id).uuid().not_null().primary_key()
                    .extra("DEFAULT gen_random_uuid()"))
                .col(ColumnDef::new(ClusterSteering::StartedAt).timestamp_with_time_zone().not_null()
                    .extra("DEFAULT NOW()"))
                .col(ColumnDef::new(ClusterSteering::EndedAt).timestamp_with_time_zone().null())
                .col(ColumnDef::new(ClusterSteering::Scope).text().not_null())
                .col(ColumnDef::new(ClusterSteering::ConfigJson).json_binary().not_null())
                .col(ColumnDef::new(ClusterSteering::OutcomeJson).json_binary().null())
                .col(ColumnDef::new(ClusterSteering::ValidationFailed).boolean().not_null()
                    .default(false))
                .col(ColumnDef::new(ClusterSteering::ModelId).text().not_null())
                .col(ColumnDef::new(ClusterSteering::PromptTokens).integer().null())
                .col(ColumnDef::new(ClusterSteering::CompletionTokens).integer().null())
                .check(Expr::col(ClusterSteering::Scope).is_in(["B", "C"]))
                .to_owned(),
        ).await?;
        m.create_index(Index::create()
            .name("cluster_steering_started_at_idx")
            .table(ClusterSteering::Table)
            .col(ClusterSteering::StartedAt)
            .to_owned()).await
    }

    async fn down(&self, m: &SchemaManager) -> Result<(), DbErr> {
        m.drop_table(Table::drop().table(ClusterSteering::Table).to_owned()).await
    }
}

#[derive(DeriveIden)]
enum ClusterSteering {
    Table,
    Id, StartedAt, EndedAt, Scope, ConfigJson, OutcomeJson,
    ValidationFailed, ModelId, PromptTokens, CompletionTokens,
}
```

- [ ] **Step 2: Register in `mod.rs`**

Append to `Migrator::migrations()`:
```rust
Box::new(m20260501_000001_cluster_steering::Migration),
```
Add `mod m20260501_000001_cluster_steering;` at top.

- [ ] **Step 3: Run + verify**

Run: `cargo run --bin nasrudin-migrate -- up` (or whatever the project's migrate runner is — see `engine/crates/pg/src/bin/`).
Expected: migration applies, `\d cluster_steering` in psql shows the table.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/migrator/
git commit -m "Add cluster_steering migration for steerer history"
```

---

### Task 1.2: Migration — `conjecture_jobs` quota columns

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260501_000002_paid_job_quota.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`
- Modify: `engine/crates/pg/src/entity/conjecture_jobs.rs`

- [ ] **Step 1: Write the migration**

```rust
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, m: &SchemaManager) -> Result<(), DbErr> {
        m.alter_table(Table::alter().table(ConjectureJobs::Table)
            .add_column(ColumnDef::new(ConjectureJobs::LakeSlotHoursQuota).integer()
                .not_null().default(96))
            .add_column(ColumnDef::new(ConjectureJobs::LakeSlotHoursConsumed).float()
                .not_null().default(0.0))
            .add_column(ColumnDef::new(ConjectureJobs::SlicePriority).integer()
                .not_null().default(5))
            .add_column(ColumnDef::new(ConjectureJobs::Tier).text()
                .not_null().default("researcher"))
            .to_owned()).await?;
        m.create_index(Index::create()
            .name("conjecture_jobs_queue_idx")
            .table(ConjectureJobs::Table)
            .col(ConjectureJobs::State)
            .col(ConjectureJobs::SlicePriority)
            .col(ConjectureJobs::CreatedAt)
            .to_owned()).await
    }
    async fn down(&self, m: &SchemaManager) -> Result<(), DbErr> {
        m.drop_index(Index::drop().name("conjecture_jobs_queue_idx").to_owned()).await?;
        m.alter_table(Table::alter().table(ConjectureJobs::Table)
            .drop_column(ConjectureJobs::Tier)
            .drop_column(ConjectureJobs::SlicePriority)
            .drop_column(ConjectureJobs::LakeSlotHoursConsumed)
            .drop_column(ConjectureJobs::LakeSlotHoursQuota)
            .to_owned()).await
    }
}

#[derive(DeriveIden)]
enum ConjectureJobs {
    Table, State, CreatedAt,
    LakeSlotHoursQuota, LakeSlotHoursConsumed, SlicePriority, Tier,
}
```

- [ ] **Step 2: Register in `mod.rs`**

- [ ] **Step 3: Add SeaORM columns to entity**

Edit `engine/crates/pg/src/entity/conjecture_jobs.rs` `Model` struct:
```rust
pub lake_slot_hours_quota: i32,
pub lake_slot_hours_consumed: f32,
pub slice_priority: i32,
pub tier: String,
```

- [ ] **Step 4: Run migration + verify entity compiles**

Run: `cargo run --bin nasrudin-migrate -- up` then `cargo check -p nasrudin-pg`
Expected: schema updated, entity compiles.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/
git commit -m "Add paid-job quota columns to conjecture_jobs"
```

---

### Task 1.3: Migration — `users.research_credits`

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260501_000003_research_credits.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`
- Modify: `engine/crates/pg/src/entity/users.rs`

- [ ] **Step 1: Write the migration**

```rust
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, m: &SchemaManager) -> Result<(), DbErr> {
        m.alter_table(Table::alter().table(Users::Table)
            .add_column(ColumnDef::new(Users::ResearchCredits).integer().not_null().default(0))
            .to_owned()).await
    }
    async fn down(&self, m: &SchemaManager) -> Result<(), DbErr> {
        m.alter_table(Table::alter().table(Users::Table)
            .drop_column(Users::ResearchCredits).to_owned()).await
    }
}

#[derive(DeriveIden)]
enum Users { Table, ResearchCredits }
```

- [ ] **Step 2: Register in `mod.rs`**

- [ ] **Step 3: Add to entity**

In `engine/crates/pg/src/entity/users.rs`, add to `Model`:
```rust
pub research_credits: i32,
```

- [ ] **Step 4: Run + verify**

Run: `cargo run --bin nasrudin-migrate -- up` then `cargo check -p nasrudin-pg`
Expected: passes.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/
git commit -m "Add users.research_credits for paid Researcher tier"
```

---

### Task 1.4: SeaORM entity for `cluster_steering`

**Files:**
- Create: `engine/crates/pg/src/entity/cluster_steering.rs`
- Modify: `engine/crates/pg/src/entity/mod.rs`

- [ ] **Step 1: Write the entity**

```rust
use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "cluster_steering")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub started_at: DateTimeWithTimeZone,
    pub ended_at: Option<DateTimeWithTimeZone>,
    pub scope: String,
    #[sea_orm(column_type = "JsonBinary")]
    pub config_json: Json,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub outcome_json: Option<Json>,
    pub validation_failed: bool,
    pub model_id: String,
    pub prompt_tokens: Option<i32>,
    pub completion_tokens: Option<i32>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 2: Re-export in `entity/mod.rs`**

```rust
pub mod cluster_steering;
```

- [ ] **Step 3: Verify**

Run: `cargo check -p nasrudin-pg`
Expected: compiles.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/entity/
git commit -m "Add SeaORM entity for cluster_steering"
```

---

### Task 1.5: PG query helpers for `cluster_steering`

**Files:**
- Create: `engine/crates/pg/src/query/cluster_steering.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`

- [ ] **Step 1: Write the failing test**

Create `engine/crates/pg/tests/cluster_steering_queries.rs`:
```rust
use nasrudin_pg::query::cluster_steering::*;

#[tokio::test]
async fn list_recent_returns_newest_first() {
    let db = nasrudin_pg::test_helpers::setup_test_db().await;
    insert_new_cycle(&db, "C", serde_json::json!({"v": 1}), "kimi-k2-instruct").await.unwrap();
    insert_new_cycle(&db, "B", serde_json::json!({"v": 2}), "kimi-k2-instruct").await.unwrap();
    let rows = list_recent(&db, 10).await.unwrap();
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].config_json["v"], 2);
}
```

- [ ] **Step 2: Run the failing test**

Run: `cargo test -p nasrudin-pg --test cluster_steering_queries`
Expected: FAIL — `list_recent`, `insert_new_cycle` not defined.

- [ ] **Step 3: Implement**

Create `engine/crates/pg/src/query/cluster_steering.rs`:
```rust
use sea_orm::*;
use uuid::Uuid;
use crate::entity::cluster_steering::{ActiveModel, Column, Entity, Model};

pub async fn insert_new_cycle(
    db: &DatabaseConnection,
    scope: &str,
    config_json: serde_json::Value,
    model_id: &str,
) -> Result<Model, DbErr> {
    let am = ActiveModel {
        id: Set(Uuid::new_v4()),
        scope: Set(scope.into()),
        config_json: Set(config_json),
        model_id: Set(model_id.into()),
        validation_failed: Set(false),
        ..Default::default()
    };
    am.insert(db).await
}

pub async fn close_cycle(
    db: &DatabaseConnection,
    id: Uuid,
    outcome_json: serde_json::Value,
    prompt_tokens: Option<i32>,
    completion_tokens: Option<i32>,
) -> Result<(), DbErr> {
    Entity::update_many()
        .filter(Column::Id.eq(id))
        .col_expr(Column::EndedAt, Expr::current_timestamp().into())
        .col_expr(Column::OutcomeJson, Expr::value(outcome_json))
        .col_expr(Column::PromptTokens, Expr::value(prompt_tokens))
        .col_expr(Column::CompletionTokens, Expr::value(completion_tokens))
        .exec(db).await?;
    Ok(())
}

pub async fn list_recent(db: &DatabaseConnection, n: u64) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .order_by_desc(Column::StartedAt)
        .limit(n)
        .all(db).await
}

pub async fn open_cycle(db: &DatabaseConnection) -> Result<Option<Model>, DbErr> {
    Entity::find()
        .filter(Column::EndedAt.is_null())
        .order_by_desc(Column::StartedAt)
        .one(db).await
}

pub async fn prune_to_last_n(db: &DatabaseConnection, keep: u64) -> Result<u64, DbErr> {
    let cutoff = Entity::find()
        .order_by_desc(Column::StartedAt)
        .offset(keep)
        .limit(1)
        .one(db).await?;
    let Some(cutoff) = cutoff else { return Ok(0); };
    let res = Entity::delete_many()
        .filter(Column::StartedAt.lt(cutoff.started_at))
        .exec(db).await?;
    Ok(res.rows_affected)
}
```

Add `pub mod cluster_steering;` to `query/mod.rs`.

- [ ] **Step 4: Run test**

Run: `cargo test -p nasrudin-pg --test cluster_steering_queries`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/query/
git commit -m "Add cluster_steering query helpers"
```

---

### Task 1.6: New `nasrudin_llm::gradient` provider

**Files:**
- Create: `engine/crates/llm/src/gradient.rs`
- Modify: `engine/crates/llm/src/lib.rs`
- Modify: `engine/crates/llm/src/registry.rs`
- Test: `engine/crates/llm/tests/gradient_smoke.rs`

- [ ] **Step 1: Write the failing test**

`engine/crates/llm/tests/gradient_smoke.rs`:
```rust
use nasrudin_llm::{gradient::GradientProvider, CompletionRequest, LlmProvider, ResponseFormat};
use wiremock::{matchers::*, Mock, MockServer, ResponseTemplate};

#[tokio::test]
async fn gradient_provider_returns_text_from_choices() {
    let srv = MockServer::start().await;
    Mock::given(method("POST"))
        .and(path("/v1/chat/completions"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "choices": [{ "message": { "content": "{\"hi\":1}" } }],
            "usage": { "prompt_tokens": 10, "completion_tokens": 4 }
        })))
        .mount(&srv).await;
    let p = GradientProvider::new(srv.uri(), "test-key".into());
    let req = CompletionRequest {
        model: "kimi-k2-instruct".into(),
        system_prompt: "sys".into(),
        user_prompt: "hi".into(),
        max_tokens: 256, temperature: 0.0,
        stop_sequences: vec![],
        response_format: ResponseFormat::Text,
    };
    let resp = p.complete(&req, "ignored-key").await.unwrap();
    assert_eq!(resp.text, "{\"hi\":1}");
    assert_eq!(resp.prompt_tokens, Some(10));
}
```

- [ ] **Step 2: Run failing test**

Run: `cargo test -p nasrudin-llm --test gradient_smoke`
Expected: FAIL — `gradient` module missing.

- [ ] **Step 3: Implement provider**

Create `engine/crates/llm/src/gradient.rs` mirroring `engine/crates/llm/src/openai.rs`. The Gradient REST API is OpenAI-compatible at `POST /v1/chat/completions`; the only differences are base URL and the auth env source.

```rust
//! DigitalOcean Gradient inference provider (OpenAI-shape REST).
//!
//! Distinct from openai.rs in three ways:
//!  1. Server-owned API key (env GRADIENT_API_KEY), not user-stored.
//!  2. Base URL https://inference.do-ai.run/v1/ (overridable for tests).
//!  3. Used by the cluster steerer, not the per-user conjecture flow.

use async_trait::async_trait;
use futures::stream::BoxStream;
use serde::{Deserialize, Serialize};

use crate::{CompletionRequest, CompletionResponse, LlmError, LlmProvider, LlmStreamChunk, ResponseFormat};

const DEFAULT_BASE: &str = "https://inference.do-ai.run/v1";

pub struct GradientProvider {
    base: String,
    server_key: String,  // resolved at construction; not the user-key arg
    http: reqwest::Client,
}

impl GradientProvider {
    pub fn new(base: impl Into<String>, server_key: impl Into<String>) -> Self {
        Self { base: base.into(), server_key: server_key.into(), http: reqwest::Client::new() }
    }
    pub fn from_env() -> Result<Self, LlmError> {
        let key = std::env::var("GRADIENT_API_KEY")
            .map_err(|_| LlmError::Other("GRADIENT_API_KEY unset".into()))?;
        let base = std::env::var("GRADIENT_BASE_URL").unwrap_or_else(|_| DEFAULT_BASE.into());
        Ok(Self::new(base, key))
    }
    pub async fn list_models(&self) -> Result<Vec<String>, LlmError> {
        #[derive(Deserialize)] struct M { id: String }
        #[derive(Deserialize)] struct R { data: Vec<M> }
        let r: R = self.http.get(format!("{}/models", self.base))
            .bearer_auth(&self.server_key)
            .send().await.map_err(|e| LlmError::Network(e.to_string()))?
            .error_for_status().map_err(|e| LlmError::Other(e.to_string()))?
            .json().await.map_err(|e| LlmError::Other(e.to_string()))?;
        Ok(r.data.into_iter().map(|m| m.id).collect())
    }
}

#[async_trait]
impl LlmProvider for GradientProvider {
    async fn complete(&self, req: &CompletionRequest, _user_key: &str) -> Result<CompletionResponse, LlmError> {
        #[derive(Serialize)] struct Msg { role: &'static str, content: String }
        #[derive(Serialize)] struct Body<'a> {
            model: &'a str,
            messages: Vec<Msg>,
            max_tokens: u32,
            temperature: f32,
            #[serde(skip_serializing_if = "Option::is_none")]
            response_format: Option<serde_json::Value>,
        }
        let response_format = match &req.response_format {
            ResponseFormat::Text => None,
            ResponseFormat::Json { .. } => Some(serde_json::json!({ "type": "json_object" })),
        };
        let body = Body {
            model: &req.model,
            messages: vec![
                Msg { role: "system", content: req.system_prompt.clone() },
                Msg { role: "user", content: req.user_prompt.clone() },
            ],
            max_tokens: req.max_tokens,
            temperature: req.temperature,
            response_format,
        };
        #[derive(Deserialize)] struct C { message: M }
        #[derive(Deserialize)] struct M { content: String }
        #[derive(Deserialize)] struct U { prompt_tokens: Option<i32>, completion_tokens: Option<i32> }
        #[derive(Deserialize)] struct R { choices: Vec<C>, usage: Option<U> }
        let r: R = self.http.post(format!("{}/chat/completions", self.base))
            .bearer_auth(&self.server_key)
            .json(&body).send().await.map_err(|e| LlmError::Network(e.to_string()))?
            .error_for_status().map_err(|e| LlmError::Other(e.to_string()))?
            .json().await.map_err(|e| LlmError::Other(e.to_string()))?;
        let text = r.choices.into_iter().next()
            .map(|c| c.message.content).unwrap_or_default();
        Ok(CompletionResponse {
            text,
            prompt_tokens: r.usage.as_ref().and_then(|u| u.prompt_tokens),
            completion_tokens: r.usage.as_ref().and_then(|u| u.completion_tokens),
        })
    }

    async fn stream(&self, _req: &CompletionRequest, _key: &str)
        -> Result<BoxStream<'static, Result<LlmStreamChunk, LlmError>>, LlmError>
    {
        Err(LlmError::Other("gradient streaming not implemented".into()))
    }
}
```

In `engine/crates/llm/src/lib.rs`: add `pub mod gradient;`.
In `engine/crates/llm/src/registry.rs`: add `"gradient"` to the `known_providers()` list.

- [ ] **Step 4: Run test**

Run: `cargo test -p nasrudin-llm --test gradient_smoke`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/llm/
git commit -m "Add nasrudin_llm::gradient provider for DO Gradient"
```

---

## Phase 2 — Steering core

### Task 2.1: `SteeringConfig` types + validator

**Files:**
- Create: `engine/crates/api/src/steerer/mod.rs`
- Create: `engine/crates/api/src/steerer/schema.rs`
- Modify: `engine/crates/api/src/lib.rs` (add `pub mod steerer;`)
- Test: `engine/crates/api/src/steerer/schema.rs` (inline `#[cfg(test)]`)

- [ ] **Step 1: Write the failing tests**

In `schema.rs`:
```rust
#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn default_passes_validation() { default_config().validate().unwrap(); }
    #[test] fn domain_weights_must_sum_to_one() {
        let mut c = default_config();
        c.domain_weights.insert("special_relativity".into(), 0.3);
        assert!(c.validate().is_err());
    }
    #[test] fn mode_b_rejects_mutation_knobs() {
        let mut c = default_config();
        c.scope = "B".into();
        c.mutation_knobs = Some(MutationKnobs::default());
        assert!(c.validate().is_err());
    }
    #[test] fn mode_b_rejects_hard_targets() {
        let mut c = default_config();
        c.scope = "B".into();
        c.hard_targets.push(HardTarget { latex: "x=y".into(), domain: "sr".into(), weight: 0.5 });
        assert!(c.validate().is_err());
    }
    #[test] fn fitness_weights_must_sum_to_one() {
        let mut c = default_config();
        c.fitness_weights.novelty = 2.0;
        assert!(c.validate().is_err());
    }
}
```

- [ ] **Step 2: Run failing tests**

Run: `cargo test -p physics-api steerer::schema`
Expected: FAIL — types not defined.

- [ ] **Step 3: Implement**

```rust
//! SteeringConfig schema, validation, and default.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SteeringConfig {
    pub version: u32,
    pub scope: String,                     // "B" or "C"
    pub domain_weights: HashMap<String, f32>,
    pub axiom_emphasis: HashMap<String, f32>,
    pub fitness_weights: FitnessWeights,
    pub soft_targets: Vec<SoftTarget>,
    pub hard_targets: Vec<HardTarget>,     // empty in B
    pub mutation_knobs: Option<MutationKnobs>,  // None in B
    pub rationale: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct FitnessWeights {
    pub novelty: f32,
    pub dimensional_elegance: f32,
    pub chain_length_penalty: f32,
    pub target_proximity: f32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SoftTarget { pub latex: String, pub domain: String, pub weight: f32 }
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HardTarget { pub latex: String, pub domain: String, pub weight: f32 }

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MutationKnobs {
    pub rate: f32,                  // 0.05..0.30
    pub suffix_bias: f32,           // 0.0..1.0
    pub population_size: u32,       // 32..512
    pub elitism_fraction: f32,      // 0.0..0.2
}
impl Default for MutationKnobs {
    fn default() -> Self {
        Self { rate: 0.10, suffix_bias: 0.4, population_size: 128, elitism_fraction: 0.05 }
    }
}

#[derive(Debug, Error)]
pub enum SteeringValidationError {
    #[error("scope must be B or C, got {0}")] BadScope(String),
    #[error("domain_weights must sum to 1.0 (±0.01), got {0}")] DomainSum(f32),
    #[error("fitness_weights must sum to 1.0 (±0.01), got {0}")] FitnessSum(f32),
    #[error("axiom_emphasis values must be in [0.0, 2.0]")] BadEmphasis,
    #[error("scope=B must have empty hard_targets")] BHasHardTargets,
    #[error("scope=B must have null mutation_knobs")] BHasMutationKnobs,
    #[error("mutation_knobs.{field} out of range")] KnobRange { field: &'static str },
    #[error("rationale exceeds 500 chars")] RationaleTooLong,
}

impl SteeringConfig {
    pub fn validate(&self) -> Result<(), SteeringValidationError> {
        if self.scope != "B" && self.scope != "C" {
            return Err(SteeringValidationError::BadScope(self.scope.clone()));
        }
        let dsum: f32 = self.domain_weights.values().sum();
        if (dsum - 1.0).abs() > 0.01 { return Err(SteeringValidationError::DomainSum(dsum)); }
        let fsum = self.fitness_weights.novelty + self.fitness_weights.dimensional_elegance
            + self.fitness_weights.chain_length_penalty + self.fitness_weights.target_proximity;
        if (fsum - 1.0).abs() > 0.01 { return Err(SteeringValidationError::FitnessSum(fsum)); }
        if self.axiom_emphasis.values().any(|v| !(0.0..=2.0).contains(v)) {
            return Err(SteeringValidationError::BadEmphasis);
        }
        if self.scope == "B" {
            if !self.hard_targets.is_empty() { return Err(SteeringValidationError::BHasHardTargets); }
            if self.mutation_knobs.is_some() { return Err(SteeringValidationError::BHasMutationKnobs); }
        }
        if let Some(k) = &self.mutation_knobs {
            if !(0.05..=0.30).contains(&k.rate)
                { return Err(SteeringValidationError::KnobRange { field: "rate" }); }
            if !(0.0..=1.0).contains(&k.suffix_bias)
                { return Err(SteeringValidationError::KnobRange { field: "suffix_bias" }); }
            if !(32..=512).contains(&k.population_size)
                { return Err(SteeringValidationError::KnobRange { field: "population_size" }); }
            if !(0.0..=0.2).contains(&k.elitism_fraction)
                { return Err(SteeringValidationError::KnobRange { field: "elitism_fraction" }); }
        }
        if self.rationale.len() > 500 { return Err(SteeringValidationError::RationaleTooLong); }
        Ok(())
    }
}

pub fn default_config() -> SteeringConfig {
    let mut domain_weights = HashMap::new();
    domain_weights.insert("special_relativity".into(), 0.25);
    domain_weights.insert("electromagnetism".into(), 0.25);
    domain_weights.insert("classical_mechanics".into(), 0.25);
    domain_weights.insert("thermodynamics".into(), 0.25);
    SteeringConfig {
        version: 1,
        scope: "C".into(),
        domain_weights,
        axiom_emphasis: HashMap::new(),
        fitness_weights: FitnessWeights {
            novelty: 0.4, dimensional_elegance: 0.3,
            chain_length_penalty: 0.2, target_proximity: 0.1,
        },
        soft_targets: vec![],
        hard_targets: vec![],
        mutation_knobs: Some(MutationKnobs::default()),
        rationale: "default cold-start config".into(),
    }
}
```

`engine/crates/api/src/steerer/mod.rs`:
```rust
pub mod schema;
```

- [ ] **Step 4: Run tests**

Run: `cargo test -p physics-api steerer::schema`
Expected: PASS (5 tests).

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/steerer/ engine/crates/api/src/lib.rs
git commit -m "Add SteeringConfig schema + validator"
```

---

### Task 2.2: Demand aggregator

**Files:**
- Create: `engine/crates/api/src/steerer/demand.rs`
- Modify: `engine/crates/api/src/steerer/mod.rs`

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    #[tokio::test]
    async fn aggregator_dedups_and_sorts_by_count() {
        let db = nasrudin_pg::test_helpers::setup_test_db().await;
        // seed 3 search-log rows: "entropy" x2, "carnot" x1
        nasrudin_pg::query::search::record(&db, "entropy", None).await.unwrap();
        nasrudin_pg::query::search::record(&db, "entropy", None).await.unwrap();
        nasrudin_pg::query::search::record(&db, "carnot", None).await.unwrap();
        let d = aggregate_demand(&db, std::time::Duration::from_secs(3600)).await.unwrap();
        assert_eq!(d.top_searches[0].0, "entropy");
        assert_eq!(d.top_searches[0].1, 2);
        assert!(d.top_searches.iter().any(|(s, _)| s == "carnot"));
    }
}
```

- [ ] **Step 2: Run failing test**

Run: `cargo test -p physics-api steerer::demand`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
//! Aggregate user demand signals over a sliding window for the steerer prompt.

use sea_orm::DatabaseConnection;
use serde::{Deserialize, Serialize};
use std::time::Duration;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DemandSnapshot {
    pub window_seconds: u64,
    pub top_searches: Vec<(String, u32)>,
    pub top_saved_searches: Vec<(String, u32)>,
    pub top_concept_queries: Vec<(String, u32)>,
}

pub async fn aggregate_demand(
    db: &DatabaseConnection,
    window: Duration,
) -> Result<DemandSnapshot, sea_orm::DbErr> {
    let top_searches = nasrudin_pg::query::search::top_n_in_window(db, 10, window).await?;
    let top_saved = nasrudin_pg::query::saved_searches::top_n_in_window(db, 10, window).await
        .unwrap_or_default();
    let top_concept = nasrudin_pg::query::targeted_search_usage::top_n_in_window(db, 10, window).await
        .unwrap_or_default();
    Ok(DemandSnapshot {
        window_seconds: window.as_secs(),
        top_searches,
        top_saved_searches: top_saved,
        top_concept_queries: top_concept,
    })
}
```

If `top_n_in_window` doesn't exist on those query modules, add it as a thin SQL helper in the same step:
```rust
// In engine/crates/pg/src/query/search.rs:
pub async fn top_n_in_window(
    db: &DatabaseConnection, n: u64, window: std::time::Duration,
) -> Result<Vec<(String, u32)>, DbErr> {
    use sea_orm::*;
    let cutoff = chrono::Utc::now() - chrono::Duration::from_std(window).unwrap();
    let rows = entity::search_log::Entity::find()
        .filter(entity::search_log::Column::CreatedAt.gt(cutoff))
        .all(db).await?;
    let mut counts: std::collections::HashMap<String, u32> = Default::default();
    for r in rows { *counts.entry(r.query_text).or_insert(0) += 1; }
    let mut v: Vec<_> = counts.into_iter().map(|(k,v)| (k, v)).collect();
    v.sort_by(|a, b| b.1.cmp(&a.1));
    v.truncate(n as usize);
    Ok(v)
}
```

Repeat the same shape for `saved_searches` and `targeted_search_usage`. Reuse the latex/query column name that each entity actually uses (check `engine/crates/pg/src/entity/saved_searches.rs` and the `targeted_search_usage` entity for the exact column).

Add `pub mod demand;` to `engine/crates/api/src/steerer/mod.rs`.

- [ ] **Step 4: Run test**

Run: `cargo test -p physics-api steerer::demand`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/steerer/ engine/crates/pg/src/query/
git commit -m "Add demand aggregator for steerer prompt"
```

---

### Task 2.3: Prompt builder

**Files:**
- Create: `engine/crates/api/src/steerer/prompt.rs`

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::steerer::demand::DemandSnapshot;
    #[test]
    fn prompt_includes_history_demand_and_scope() {
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot { window_seconds: 600,
                top_searches: vec![("entropy".into(), 4)],
                top_saved_searches: vec![], top_concept_queries: vec![] },
            &[],
        );
        assert!(p.contains("scope=C"));
        assert!(p.contains("entropy"));
    }
    #[test]
    fn mode_b_signals_pinned_targets() {
        let p = build_prompt(
            "B",
            &[],
            &DemandSnapshot::default(),
            &[ActiveJobSummary {
                domain: "thermodynamics".into(),
                conjecture_summary: "δQ = T dS".into(),
            }],
        );
        assert!(p.contains("scope=B"));
        assert!(p.contains("δQ = T dS"));
    }
}
```

- [ ] **Step 2: Run failing test**

Run: `cargo test -p physics-api steerer::prompt`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
//! Build the user prompt string for one steerer cycle.

use crate::steerer::demand::DemandSnapshot;
use serde::{Deserialize, Serialize};

pub const SYSTEM_PROMPT: &str = r#"You are the cluster steerer for Nasrudin, a distributed
theorem-discovery platform. Each cycle, you read aggregate user demand signals and the
outcomes of your last 10 cycles, then emit a SteeringConfig JSON that biases the GA
exploration of thousands of workers. Output ONLY valid JSON matching the schema. Honor
mode (B vs C): in B, omit hard_targets and set mutation_knobs to null. Be concise in
rationale (≤500 chars)."#;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActiveJobSummary {
    pub domain: String,
    pub conjecture_summary: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistoryEntry {
    pub config: serde_json::Value,
    pub outcome: Option<serde_json::Value>,
    pub scope: String,
    pub started_at: String,
}

pub fn build_prompt(
    scope: &str,
    history: &[HistoryEntry],
    demand: &DemandSnapshot,
    active_jobs: &[ActiveJobSummary],
) -> String {
    let payload = serde_json::json!({
        "scope": scope,
        "history": history,
        "current_demand": demand,
        "active_jobs": active_jobs,
        "instructions": format!(
            "scope={s}. {extra} Emit SteeringConfig JSON only.",
            s = scope,
            extra = if scope == "B" {
                "Mutation knobs are LOCKED for this cycle (paid jobs running). Set mutation_knobs=null and hard_targets=[]. Use soft_targets to bias the explorer fleet toward prerequisite lemmas in the active-job domains."
            } else {
                "Full authority. You may emit hard_targets and mutation_knobs."
            }
        )
    });
    serde_json::to_string_pretty(&payload).unwrap()
}
```

Note that `DemandSnapshot::default()` is needed for the test — derive `Default` on it in `demand.rs`.

- [ ] **Step 4: Run test**

Run: `cargo test -p physics-api steerer::prompt`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/steerer/
git commit -m "Add steerer prompt builder"
```

---

### Task 2.4: Cycle loop (close + new + persist)

**Files:**
- Create: `engine/crates/api/src/steerer/cycle.rs`
- Modify: `engine/crates/api/src/steerer/mod.rs`

The cycle loop is the heart of the steerer. It runs in a tokio task, ticks every `STEERER_CADENCE_SECONDS`, and:
1. Closes the previous open cycle (if any) by computing outcome counters.
2. Determines mode by querying active conjecture jobs.
3. Builds prompt from history + demand + active jobs.
4. Calls Gradient.
5. Validates response.
6. Persists new cycle row.

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::steerer::schema::{default_config, SteeringConfig};
    
    struct FakeGradient { reply: String }
    #[async_trait::async_trait]
    impl LlmCaller for FakeGradient {
        async fn call(&self, _prompt: String) -> Result<(String, Option<i32>, Option<i32>), CycleError> {
            Ok((self.reply.clone(), Some(100), Some(50)))
        }
    }

    #[tokio::test]
    async fn cycle_persists_valid_config_and_falls_back_on_invalid() {
        let db = nasrudin_pg::test_helpers::setup_test_db().await;
        let valid = serde_json::to_string(&default_config()).unwrap();
        let cycle_one = run_one_cycle(&db, &FakeGradient { reply: valid }, "kimi-k2-instruct").await;
        cycle_one.unwrap();
        let bad = "{ not valid json".to_string();
        let cycle_two = run_one_cycle(&db, &FakeGradient { reply: bad }, "kimi-k2-instruct").await;
        cycle_two.unwrap();
        let rows = nasrudin_pg::query::cluster_steering::list_recent(&db, 10).await.unwrap();
        assert_eq!(rows.len(), 2);
        // Last row is the failed one — should reuse cycle_one's config and be flagged
        assert!(rows[0].validation_failed);
        assert_eq!(rows[0].config_json, rows[1].config_json);
    }
}
```

- [ ] **Step 2: Run failing test**

Run: `cargo test -p physics-api steerer::cycle`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
//! One cycle of the cluster steerer.

use sea_orm::DatabaseConnection;
use thiserror::Error;
use uuid::Uuid;

use crate::steerer::{
    demand::{aggregate_demand, DemandSnapshot},
    prompt::{build_prompt, ActiveJobSummary, HistoryEntry, SYSTEM_PROMPT},
    schema::{default_config, SteeringConfig, SteeringValidationError},
};

#[derive(Debug, Error)]
pub enum CycleError {
    #[error("db: {0}")] Db(#[from] sea_orm::DbErr),
    #[error("llm: {0}")] Llm(String),
    #[error("validation: {0}")] Validation(#[from] SteeringValidationError),
    #[error("parse: {0}")] Parse(String),
}

#[async_trait::async_trait]
pub trait LlmCaller {
    async fn call(&self, prompt: String) -> Result<(String, Option<i32>, Option<i32>), CycleError>;
}

const HISTORY_N: u64 = 10;
const DEMAND_WINDOW: std::time::Duration = std::time::Duration::from_secs(3600);

pub async fn run_one_cycle(
    db: &DatabaseConnection,
    caller: &dyn LlmCaller,
    model_id: &str,
) -> Result<Uuid, CycleError> {
    let scope = if active_paid_jobs(db).await? > 0 { "B" } else { "C" };
    let history = load_history(db, HISTORY_N).await?;
    let demand = aggregate_demand(db, DEMAND_WINDOW).await?;
    let active_jobs = active_job_summaries(db).await?;
    let prompt = build_prompt(scope, &history, &demand, &active_jobs);
    let user_prompt = format!("{}\n\n---\n{}", SYSTEM_PROMPT, prompt);
    let (text, ptok, ctok) = caller.call(user_prompt).await?;
    let config = match parse_and_validate(&text, scope) {
        Ok(c) => c,
        Err(e) => {
            tracing::warn!(error=%e, "steerer validation failed, falling back to last-known-good");
            let lkg = last_known_good(db).await?.unwrap_or_else(|| {
                let mut c = default_config();
                c.scope = scope.into();
                c
            });
            return persist_cycle(db, &lkg, scope, model_id, ptok, ctok, true).await;
        }
    };
    persist_cycle(db, &config, scope, model_id, ptok, ctok, false).await
}

fn parse_and_validate(text: &str, expected_scope: &str) -> Result<SteeringConfig, CycleError> {
    let mut c: SteeringConfig = serde_json::from_str(text).map_err(|e| CycleError::Parse(e.to_string()))?;
    if c.scope != expected_scope { c.scope = expected_scope.into(); }
    c.validate()?;
    Ok(c)
}

async fn persist_cycle(
    db: &DatabaseConnection,
    config: &SteeringConfig,
    scope: &str,
    model_id: &str,
    ptok: Option<i32>,
    ctok: Option<i32>,
    validation_failed: bool,
) -> Result<Uuid, CycleError> {
    let row = nasrudin_pg::query::cluster_steering::insert_new_cycle(
        db, scope, serde_json::to_value(config).unwrap(), model_id,
    ).await?;
    if validation_failed {
        sea_orm::EntityTrait::update_many::<nasrudin_pg::entity::cluster_steering::Entity>()
            .filter(sea_orm::Condition::all().add(
                <nasrudin_pg::entity::cluster_steering::Column as sea_orm::ColumnTrait>::eq(
                    &nasrudin_pg::entity::cluster_steering::Column::Id, row.id)))
            .col_expr(
                nasrudin_pg::entity::cluster_steering::Column::ValidationFailed,
                sea_orm::sea_query::Expr::value(true),
            )
            .col_expr(
                nasrudin_pg::entity::cluster_steering::Column::PromptTokens,
                sea_orm::sea_query::Expr::value(ptok),
            )
            .col_expr(
                nasrudin_pg::entity::cluster_steering::Column::CompletionTokens,
                sea_orm::sea_query::Expr::value(ctok),
            )
            .exec(db).await?;
    }
    Ok(row.id)
}

async fn active_paid_jobs(db: &DatabaseConnection) -> Result<u64, sea_orm::DbErr> {
    use sea_orm::*;
    nasrudin_pg::entity::conjecture_jobs::Entity::find()
        .filter(nasrudin_pg::entity::conjecture_jobs::Column::State.is_in(["claimed", "running"]))
        .filter(nasrudin_pg::entity::conjecture_jobs::Column::LeaseExpiresAt.gt(chrono::Utc::now()))
        .count(db).await
}

async fn active_job_summaries(db: &DatabaseConnection) -> Result<Vec<ActiveJobSummary>, sea_orm::DbErr> {
    use sea_orm::*;
    let rows = nasrudin_pg::entity::conjecture_jobs::Entity::find()
        .filter(nasrudin_pg::entity::conjecture_jobs::Column::State.is_in(["claimed", "running"]))
        .all(db).await?;
    Ok(rows.into_iter().map(|r| ActiveJobSummary {
        domain: r.domain_hint.unwrap_or_else(|| "unknown".into()),
        conjecture_summary: r.hunch.chars().take(120).collect(),
    }).collect())
}

async fn load_history(db: &DatabaseConnection, n: u64) -> Result<Vec<HistoryEntry>, sea_orm::DbErr> {
    let rows = nasrudin_pg::query::cluster_steering::list_recent(db, n).await?;
    Ok(rows.into_iter().map(|r| HistoryEntry {
        config: r.config_json,
        outcome: r.outcome_json,
        scope: r.scope,
        started_at: r.started_at.to_rfc3339(),
    }).collect())
}

async fn last_known_good(db: &DatabaseConnection) -> Result<Option<SteeringConfig>, sea_orm::DbErr> {
    use sea_orm::*;
    let rows = nasrudin_pg::entity::cluster_steering::Entity::find()
        .filter(nasrudin_pg::entity::cluster_steering::Column::ValidationFailed.eq(false))
        .order_by_desc(nasrudin_pg::entity::cluster_steering::Column::StartedAt)
        .limit(1).all(db).await?;
    Ok(rows.into_iter().next().and_then(|r| serde_json::from_value(r.config_json).ok()))
}
```

Add `pub mod cycle;` to `steerer/mod.rs`.

- [ ] **Step 4: Run tests**

Run: `cargo test -p physics-api steerer::cycle`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/steerer/
git commit -m "Add steerer cycle loop with last-known-good fallback"
```

---

### Task 2.5: Outcome capture during cycle

**Files:**
- Create: `engine/crates/api/src/steerer/outcome.rs`
- Modify: `engine/crates/api/src/steerer/mod.rs`
- Modify: `engine/crates/api/src/steerer/cycle.rs` (call `compute_outcome` at cycle close)

The outcome is computed when a cycle closes — i.e., one tick before the new cycle starts. It walks the previous cycle's window: theorems verified during it, domain distribution actual, cascade rejects, lake failure rate, user engagement, fresh demand signals.

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    #[tokio::test]
    async fn outcome_counts_theorems_in_window() {
        let db = nasrudin_pg::test_helpers::setup_test_db().await;
        let now = chrono::Utc::now();
        let started = now - chrono::Duration::minutes(10);
        // ... seed 3 theorems with verified_at between started and now ...
        let o = compute_outcome(&db, started, now).await.unwrap();
        assert!(o.theorems_verified_in_window >= 3);
    }
}
```

- [ ] **Step 2: Run failing test**

Run: `cargo test -p physics-api steerer::outcome`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
//! Compute the outcome JSON that closes a cycle.

use chrono::{DateTime, Utc};
use sea_orm::DatabaseConnection;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct OutcomeJson {
    pub theorems_verified_in_window: u64,
    pub domain_distribution_actual: HashMap<String, f32>,
    pub target_hit_rate: f32,
    pub population_diversity_delta: f32,
    pub cascade_rejects: u64,
    pub lake_failure_rate: f32,
    pub user_engagement: UserEngagement,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct UserEngagement {
    pub views: u64,
    pub downloads: u64,
    pub manual_verifies: u64,
    pub median_dwell_ms: u64,
}

pub async fn compute_outcome(
    db: &DatabaseConnection,
    window_start: DateTime<Utc>,
    window_end: DateTime<Utc>,
) -> Result<OutcomeJson, sea_orm::DbErr> {
    let theorems_verified_in_window = nasrudin_pg::query::theorems::count_verified_between(db, window_start, window_end).await?;
    let domain_counts = nasrudin_pg::query::theorems::count_by_domain_between(db, window_start, window_end).await?;
    let total: u64 = domain_counts.values().sum();
    let domain_distribution_actual = if total > 0 {
        domain_counts.into_iter().map(|(k, v)| (k, v as f32 / total as f32)).collect()
    } else { HashMap::new() };
    let cascade_rejects = nasrudin_pg::query::theorems::count_rejected_with_reason_prefix_between(db, "ancestor_rejected:", window_start, window_end).await?;
    let lake_failure_rate = nasrudin_pg::query::theorems::lake_failure_rate_between(db, window_start, window_end).await?;
    let manual_verifies = nasrudin_pg::query::manual_verifications::count_between(db, window_start, window_end).await.unwrap_or(0);
    Ok(OutcomeJson {
        theorems_verified_in_window,
        domain_distribution_actual,
        target_hit_rate: 0.0,                // computed in Phase 6 once GA reports back
        population_diversity_delta: 0.0,     // ditto
        cascade_rejects,
        lake_failure_rate,
        user_engagement: UserEngagement {
            manual_verifies,
            ..Default::default()             // views/downloads/dwell wired in Task 7.1
        },
    })
}
```

For each `nasrudin_pg::query::theorems::count_*_between` helper that doesn't already exist, add it as a thin SQL helper in `engine/crates/pg/src/query/theorems.rs`. Mirror the shape of existing `count_by_domain` (`engine/crates/api/src/metrics.rs:52`).

In `cycle.rs`, before inserting the new row, fetch the open cycle from `cluster_steering::open_cycle(db)`, compute its outcome via `compute_outcome(db, started_at, now())`, and call `cluster_steering::close_cycle` with the outcome JSON. Tokens of the previous-cycle's call were already persisted on its insert; we only fill in `outcome_json` and `ended_at`.

- [ ] **Step 4: Run tests**

Run: `cargo test -p physics-api steerer::outcome`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/steerer/ engine/crates/pg/src/query/theorems.rs
git commit -m "Add cycle outcome capture"
```

---

### Task 2.6: Spawn steerer task in `main.rs` + boot model check

**Files:**
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/api/src/state.rs`

- [ ] **Step 1: Write integration smoke**

`engine/crates/api/tests/steerer_boot_smoke.rs`:
```rust
#[tokio::test]
async fn steerer_boots_with_model_check() {
    // Start a wiremock server returning {"data":[{"id":"kimi-k2-instruct"}]} on /v1/models.
    // Set GRADIENT_BASE_URL + GRADIENT_API_KEY + STEERER_MODEL=kimi-k2-instruct.
    // Boot the API. Assert no panic, assert one tracing event "steerer model verified".
}
```

- [ ] **Step 2: Implement spawn + boot check**

In `engine/crates/api/src/main.rs`, after `LakeBuilder::new` and before mounting routes:

```rust
// ── Steerer ─────────────────────────────────────────────────────
if std::env::var("STEERER_DISABLED").is_err() {
    let model_id = std::env::var("STEERER_MODEL").unwrap_or_else(|_| "kimi-k2-instruct".into());
    let cadence_s: u64 = std::env::var("STEERER_CADENCE_SECONDS")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(600);
    let provider = nasrudin_llm::gradient::GradientProvider::from_env()
        .expect("GRADIENT_API_KEY required to boot the steerer (or set STEERER_DISABLED=1)");
    let available = provider.list_models().await.expect("Gradient /v1/models check failed");
    if !available.iter().any(|m| m == &model_id) {
        panic!("STEERER_MODEL={} not in Gradient catalog. Available: {:?}", model_id, available);
    }
    tracing::info!(model = %model_id, "steerer model verified");
    let pg_clone = pg.clone();
    let model_id_clone = model_id.clone();
    tokio::spawn(async move {
        let mut tick = tokio::time::interval(std::time::Duration::from_secs(cadence_s));
        let caller = crate::steerer::cycle::GradientCaller::new(provider, model_id_clone.clone());
        loop {
            tick.tick().await;
            if let Some(ref pg) = pg_clone {
                if let Err(e) = crate::steerer::cycle::run_one_cycle(pg, &caller, &model_id_clone).await {
                    tracing::error!(error=%e, "steerer cycle failed");
                }
            }
        }
    });
}
```

Add the `GradientCaller` adapter in `cycle.rs`:
```rust
pub struct GradientCaller {
    provider: nasrudin_llm::gradient::GradientProvider,
    model: String,
}
impl GradientCaller {
    pub fn new(provider: nasrudin_llm::gradient::GradientProvider, model: String) -> Self {
        Self { provider, model }
    }
}
#[async_trait::async_trait]
impl LlmCaller for GradientCaller {
    async fn call(&self, prompt: String) -> Result<(String, Option<i32>, Option<i32>), CycleError> {
        let lines: Vec<&str> = prompt.splitn(2, "---\n").collect();
        let (system, user) = if lines.len() == 2 { (lines[0], lines[1]) } else { ("", prompt.as_str()) };
        let req = nasrudin_llm::CompletionRequest {
            model: self.model.clone(),
            system_prompt: system.into(),
            user_prompt: user.into(),
            max_tokens: 2048,
            temperature: 0.4,
            stop_sequences: vec![],
            response_format: nasrudin_llm::ResponseFormat::Json {
                schema: serde_json::json!({}),
            },
        };
        let r = nasrudin_llm::LlmProvider::complete(&self.provider, &req, "").await
            .map_err(|e| CycleError::Llm(e.to_string()))?;
        Ok((r.text, r.prompt_tokens, r.completion_tokens))
    }
}
```

- [ ] **Step 3: Run smoke + boot manually**

Run: `cargo test -p physics-api --test steerer_boot_smoke`
Expected: PASS.

Local smoke: `GRADIENT_API_KEY=... cargo run -p physics-api`. Watch for `steerer model verified` log line.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/
git commit -m "Spawn steerer task on API boot with Gradient model check"
```

---

## Phase 3 — Steering distribution

### Task 3.1: `GET /api/steering` handler

**Files:**
- Create: `engine/crates/api/src/handlers/steering.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs`
- Modify: `engine/crates/api/src/main.rs` (register route)

- [ ] **Step 1: Write the failing integration test**

`engine/crates/api/tests/steering_endpoint.rs`:
```rust
#[tokio::test]
async fn steering_returns_latest_with_etag_and_supports_304() {
    let app = test_helpers::boot_test_api().await;
    let r = app.get("/api/steering").await;
    assert_eq!(r.status(), 200);
    let etag = r.headers()["etag"].to_str().unwrap().to_string();
    let r2 = app.get("/api/steering").header("If-None-Match", &etag).await;
    assert_eq!(r2.status(), 304);
}
```

- [ ] **Step 2: Run failing test**

Run: `cargo test -p physics-api --test steering_endpoint`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
//! GET /api/steering — current SteeringConfig + ETag.

use axum::{
    extract::State, http::{HeaderMap, StatusCode, header},
    response::IntoResponse, Json,
};
use std::sync::Arc;
use crate::state::AppState;

pub async fn steering(State(state): State<Arc<AppState>>, headers: HeaderMap) -> impl IntoResponse {
    let snap = state.steering.load();
    let etag = format!("\"{:016x}\"", snap.etag);
    if let Some(c) = headers.get(header::IF_NONE_MATCH).and_then(|v| v.to_str().ok()) {
        if c == etag {
            return (StatusCode::NOT_MODIFIED,
                [(header::ETAG, etag), (header::CACHE_CONTROL, "public, max-age=30, stale-while-revalidate=300".into())])
                .into_response();
        }
    }
    (StatusCode::OK,
        [(header::CONTENT_TYPE, "application/json".into()),
         (header::ETAG, etag),
         (header::CACHE_CONTROL, "public, max-age=30, stale-while-revalidate=300".into())],
        Json(serde_json::json!({
            "config": snap.config,
            "mode": snap.config["scope"],
            "started_at": snap.started_at,
        }))
    ).into_response()
}
```

In `main.rs`: `.route("/api/steering", get(handlers::steering::steering))`.
In `handlers/mod.rs`: `pub mod steering;`.

- [ ] **Step 4: Run test**

Run: `cargo test -p physics-api --test steering_endpoint`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/
git commit -m "Add GET /api/steering with ETag/304"
```

---

### Task 3.2: Steering ArcSwap in `AppState`

**Files:**
- Modify: `engine/crates/api/src/state.rs`
- Modify: `engine/crates/api/src/steerer/cycle.rs` (push to ArcSwap on cycle persist)

- [ ] **Step 1: Add to `AppState`**

```rust
pub struct SteeringSnapshot {
    pub config: serde_json::Value,
    pub etag: u64,
    pub started_at: chrono::DateTime<chrono::Utc>,
}
// In AppState:
pub steering: Arc<arc_swap::ArcSwap<SteeringSnapshot>>,
```

Initialise on boot to a snapshot built from `default_config()` with `etag = xxhash64(serialised)`.

- [ ] **Step 2: Push from cycle.rs**

After successful `persist_cycle`, also call:
```rust
let body = serde_json::to_vec(&config_json).unwrap();
let etag = xxhash_rust::xxh64::xxh64(&body, 0);
state.steering.store(Arc::new(SteeringSnapshot { config: config_json, etag, started_at: now }));
```
This requires plumbing `state` through `run_one_cycle`. Update its signature: `pub async fn run_one_cycle(state: &Arc<AppState>, caller: ..., model_id: &str)`.

- [ ] **Step 3: Run existing tests**

Run: `cargo test -p physics-api steerer::`
Expected: PASS (after fixing test fixtures to construct AppState).

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/
git commit -m "Wire steerer to ArcSwap for hot-reload"
```

---

### Task 3.3: Fold steering into `/api/seed` response

**Files:**
- Modify: `engine/crates/api/src/handlers/seed.rs`

- [ ] **Step 1: Write the failing test**

```rust
#[tokio::test]
async fn seed_includes_steering_field() {
    let app = test_helpers::boot_test_api().await;
    let r = app.get("/api/seed?domain=special_relativity&top=10").await;
    let body: serde_json::Value = r.json().await;
    assert!(body["steering"].is_object());
    assert!(body["steering"]["config"]["scope"].as_str().is_some());
}
```

- [ ] **Step 2: Run failing test**

Run: `cargo test -p physics-api --test seed_includes_steering`
Expected: FAIL.

- [ ] **Step 3: Modify seed handler**

In `handlers/seed.rs`, after building `axioms` and `seed_theorems`, add:
```rust
let steering_snap = state.steering.load();
let body = serde_json::json!({
    "axioms": axioms,
    "seed_theorems": seed_theorems,
    "steering": {
        "config": steering_snap.config,
        "etag": format!("{:016x}", steering_snap.etag),
        "started_at": steering_snap.started_at,
    },
});
```

The existing seed_cache must be invalidated when steering changes. Easiest: include the steering etag in the cache key, OR clear the cache map when steering rotates. Pick the latter: in `cycle.rs` after `state.steering.store(...)`, also `state.seed_cache.lock().unwrap().clear();`.

- [ ] **Step 4: Run test**

Run: `cargo test -p physics-api --test seed_includes_steering`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/
git commit -m "Fold steering into /api/seed payload"
```

---

### Task 3.4: Worker hot-reload of steering config

**Files:**
- Modify: `engine/crates/ga/src/bin/worker.rs`

- [ ] **Step 1: Add steering ArcSwap to worker state**

```rust
let steering: Arc<ArcSwap<serde_json::Value>> = Arc::new(ArcSwap::from_pointee(
    serde_json::json!({"version":1,"scope":"C","mutation_knobs":{"rate":0.1,"suffix_bias":0.4,"population_size":128,"elitism_fraction":0.05}})
));
```

- [ ] **Step 2: Update on each `/api/seed` poll**

In the existing chunk-boundary poll loop, after the seed JSON parses:
```rust
if let Some(s) = seed_json.get("steering").and_then(|v| v.get("config")) {
    let cur_etag = seed_json["steering"]["etag"].as_str().unwrap_or("");
    if cur_etag != *last_etag {
        steering.store(Arc::new(s.clone()));
        tracing::info!(etag=%cur_etag, "worker steering reloaded");
        *last_etag = cur_etag.to_string();
    }
}
```

- [ ] **Step 3: Manual smoke**

Boot API + worker. Force a steerer cycle to write a new config (admin override or wait 10 min). Watch worker logs for "worker steering reloaded".

- [ ] **Step 4: Commit**

```bash
git add engine/crates/ga/src/bin/worker.rs
git commit -m "Add steering hot-reload to worker"
```

---

### Task 3.5: `chain_engine` reads mutation knobs from steering

**Files:**
- Modify: `engine/crates/ga/src/chain_engine.rs`
- Modify: `engine/crates/ga/src/bin/worker.rs` (pass steering ArcSwap to engine)

- [ ] **Step 1: Add `MutationKnobs` to engine config struct**

```rust
pub struct ChainEngineConfig {
    pub generations: usize,
    pub population_size: usize,
    // …
    pub mutation_rate: f32,
    pub suffix_bias: f32,
    pub elitism_fraction: f32,
}
```

- [ ] **Step 2: Read steering before each generation**

```rust
let steering = self.steering.load();
if let Some(k) = steering.get("mutation_knobs").filter(|v| !v.is_null()) {
    self.cfg.mutation_rate = k["rate"].as_f64().unwrap_or(self.cfg.mutation_rate as f64) as f32;
    self.cfg.suffix_bias = k["suffix_bias"].as_f64().unwrap_or(self.cfg.suffix_bias as f64) as f32;
    self.cfg.elitism_fraction = k["elitism_fraction"].as_f64().unwrap_or(self.cfg.elitism_fraction as f64) as f32;
    let new_pop = k["population_size"].as_u64().unwrap_or(self.cfg.population_size as u64) as usize;
    if new_pop != self.cfg.population_size {
        // Defer resize to the next chunk boundary — log the intent now.
        self.pending_pop_resize = Some(new_pop);
    }
}
```

Population resize at chunk boundary in the worker loop.

- [ ] **Step 3: Smoke test**

Boot API with a forced config that sets `mutation_knobs.rate = 0.25`. Boot worker. After first chunk, log the live `mutation_rate` — assert it's 0.25.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/ga/src/
git commit -m "Wire mutation knobs from steering into chain_engine"
```

---

## Phase 4 — Paid job lifecycle

### Task 4.1: Quota math + explorer-floor calculator

**Files:**
- Create: `engine/crates/api/src/jobs/mod.rs`
- Create: `engine/crates/api/src/jobs/quota.rs`

- [ ] **Step 1: Write failing tests**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn floor_is_at_least_two() { assert_eq!(min_explorer_slots(5), 2); }
    #[test] fn floor_is_ten_percent_above_twenty() { assert_eq!(min_explorer_slots(50), 5); }
    #[test] fn floor_satisfied_simple() {
        assert!(floor_satisfied(50, 40)); // 50 total, 40 paid, 10 free, floor=5
        assert!(!floor_satisfied(50, 46)); // 4 free < 5 floor
    }
    #[test] fn quota_remaining_nonnegative() {
        assert_eq!(quota_remaining_hours(96, 100.0), 0.0);
        assert_eq!(quota_remaining_hours(96, 50.0), 46.0);
    }
}
```

- [ ] **Step 2: Run failing tests**

Run: `cargo test -p physics-api jobs::quota`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
//! Pure quota math + explorer-floor calculations.

pub fn min_explorer_slots(total_lake_slots: u32) -> u32 {
    std::cmp::max(2, (total_lake_slots as f32 * 0.10).floor() as u32)
}

pub fn floor_satisfied(total_lake_slots: u32, slots_on_paid_jobs: u32) -> bool {
    let free = total_lake_slots.saturating_sub(slots_on_paid_jobs);
    free >= min_explorer_slots(total_lake_slots)
}

pub fn quota_remaining_hours(quota: i32, consumed: f32) -> f32 {
    (quota as f32 - consumed).max(0.0)
}
```

`jobs/mod.rs`: `pub mod quota;`.

- [ ] **Step 4: Run tests**

Run: `cargo test -p physics-api jobs::quota`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/jobs/
git commit -m "Add quota math + explorer-floor calculator"
```

---

### Task 4.2: Cluster-capacity tracker

**Files:**
- Create: `engine/crates/api/src/jobs/capacity.rs`
- Modify: `engine/crates/api/src/state.rs`

The API needs to know `total_lake_slots_in_cluster` (sum of latest reported slots from each worker in the last 5 min) and `lake_slots_currently_on_paid_jobs` to evaluate `floor_satisfied`. Workers will report their available slots in the claim payload. The tracker is an in-process `DashMap<WorkerId, (Instant, u32)>` plus an aggregated counter for active claims.

- [ ] **Step 1: Implement tracker**

```rust
use dashmap::DashMap;
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant};

pub struct CapacityTracker {
    workers: DashMap<String, (Instant, u32)>,
    paid_slots: AtomicU32,
}

impl CapacityTracker {
    pub fn new() -> Self { Self { workers: DashMap::new(), paid_slots: AtomicU32::new(0) } }
    pub fn report_worker(&self, worker_id: &str, slots: u32) {
        self.workers.insert(worker_id.into(), (Instant::now(), slots));
    }
    pub fn add_paid_slots(&self, n: u32) { self.paid_slots.fetch_add(n, Ordering::SeqCst); }
    pub fn release_paid_slots(&self, n: u32) { self.paid_slots.fetch_sub(n, Ordering::SeqCst); }
    pub fn total_lake_slots(&self) -> u32 {
        let cutoff = Instant::now() - Duration::from_secs(300);
        self.workers.iter()
            .filter(|e| e.value().0 >= cutoff)
            .map(|e| e.value().1).sum()
    }
    pub fn paid_slots(&self) -> u32 { self.paid_slots.load(Ordering::SeqCst) }
}
```

In `AppState`: `pub capacity: Arc<CapacityTracker>,`. Initialise to `Arc::new(CapacityTracker::new())` at boot.

- [ ] **Step 2: Write smoke test**

```rust
#[test]
fn capacity_tracker_counts_recent_only() {
    let t = CapacityTracker::new();
    t.report_worker("a", 4);
    t.report_worker("b", 8);
    assert_eq!(t.total_lake_slots(), 12);
}
```

- [ ] **Step 3: Run + commit**

Run: `cargo test -p physics-api jobs::capacity`
Expected: PASS.

```bash
git add engine/crates/api/src/jobs/ engine/crates/api/src/state.rs
git commit -m "Add cluster-capacity tracker"
```

---

### Task 4.3: `POST /api/jobs/claim` (atomic queue claim)

**Files:**
- Create: `engine/crates/api/src/handlers/jobs_claim.rs`
- Create: `engine/crates/api/src/jobs/lease.rs`
- Modify: `engine/crates/api/src/main.rs` (register route)

- [ ] **Step 1: Write failing test**

```rust
#[tokio::test]
async fn two_concurrent_claims_one_wins() {
    let app = test_helpers::boot_test_api().await;
    seed_one_queued_job(&app).await;
    let r1 = app.post("/api/jobs/claim").json(&claim_body(4)).bearer(WORKER_KEY_1);
    let r2 = app.post("/api/jobs/claim").json(&claim_body(4)).bearer(WORKER_KEY_2);
    let (r1, r2) = tokio::join!(r1, r2);
    let s1 = r1.status(); let s2 = r2.status();
    // Exactly one of (200, 204) wins, the other is 204.
    assert!((s1 == 200) ^ (s2 == 200));
}
```

- [ ] **Step 2: Run failing test**

Run: `cargo test -p physics-api --test claim_concurrency`
Expected: FAIL.

- [ ] **Step 3: Implement atomic claim SQL**

`engine/crates/pg/src/query/conjecture_jobs.rs` (extend if exists else create):
```rust
pub async fn atomic_claim(
    db: &DatabaseConnection,
    worker_id: &str,
) -> Result<Option<Model>, DbErr> {
    use sea_orm::*;
    let stmt = sea_orm::Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"
        UPDATE conjecture_jobs SET
          claimed_by = $1,
          claimed_at = NOW(),
          lease_expires_at = NOW() + interval '5 minutes',
          state = 'claimed'
        WHERE id = (
          SELECT id FROM conjecture_jobs
          WHERE state = 'queued'
            AND (lake_slot_hours_quota - lake_slot_hours_consumed) > 0
          ORDER BY slice_priority DESC, created_at ASC
          FOR UPDATE SKIP LOCKED
          LIMIT 1
        )
        RETURNING *
        "#,
        [worker_id.into()],
    );
    Entity::find().from_raw_sql(stmt).one(db).await
}

pub async fn release_claim(db: &DatabaseConnection, id: Uuid, new_state: &str) -> Result<(), DbErr> {
    use sea_orm::*;
    Entity::update_many()
        .col_expr(Column::ClaimedBy, Expr::value::<Option<String>>(None))
        .col_expr(Column::ClaimedAt, Expr::value::<Option<chrono::DateTime<chrono::Utc>>>(None))
        .col_expr(Column::LeaseExpiresAt, Expr::value::<Option<chrono::DateTime<chrono::Utc>>>(None))
        .col_expr(Column::State, Expr::value(new_state))
        .filter(Column::Id.eq(id)).exec(db).await?;
    Ok(())
}
```

- [ ] **Step 4: Implement handler**

```rust
//! POST /api/jobs/claim — atomic queue claim with 5-min lease.

use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use std::sync::Arc;
use crate::auth::WorkerAuth;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct ClaimBody {
    pub available_lake_slots: u32,
    pub domains_supported: Vec<String>,
}

pub async fn claim(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Json(body): Json<ClaimBody>,
) -> impl IntoResponse {
    state.capacity.report_worker(&auth.worker_id_string(), body.available_lake_slots);
    if !crate::jobs::quota::floor_satisfied(state.capacity.total_lake_slots(),
            state.capacity.paid_slots() + body.available_lake_slots) {
        return (StatusCode::NO_CONTENT, "explorer floor would be violated").into_response();
    }
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    match nasrudin_pg::query::conjecture_jobs::atomic_claim(pg, &auth.worker_id_string()).await {
        Ok(Some(job)) => {
            state.capacity.add_paid_slots(body.available_lake_slots);
            (StatusCode::OK, Json(serde_json::json!({
                "job_id": job.id,
                "hunch": job.hunch,
                "domain_hint": job.domain_hint,
                "suggestions": job.suggestions,
                "lake_slot_hours_remaining": (job.lake_slot_hours_quota as f32 - job.lake_slot_hours_consumed),
                "lease_expires_at": job.lease_expires_at,
                "heartbeat_url": format!("/api/jobs/{}/heartbeat", job.id),
            }))).into_response()
        }
        Ok(None) => (StatusCode::NO_CONTENT, "no jobs queued").into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response(),
    }
}
```

- [ ] **Step 5: Register route + run test**

In `main.rs`: `.route("/api/jobs/claim", post(handlers::jobs_claim::claim))`.
Run: `cargo test -p physics-api --test claim_concurrency`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/
git commit -m "Add atomic POST /api/jobs/claim"
```

---

### Task 4.4: `POST /api/jobs/{id}/heartbeat`

**Files:**
- Modify: `engine/crates/api/src/handlers/jobs_claim.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Write failing test**

```rust
#[tokio::test]
async fn heartbeat_extends_lease_and_decrements_quota() {
    let app = test_helpers::boot_test_api().await;
    let job = seed_one_queued_job(&app).await;
    let claim = app.post("/api/jobs/claim").json(&claim_body(4)).bearer(WORKER_KEY_1).await;
    let job_id = claim.json::<serde_json::Value>().await["job_id"].as_str().unwrap().to_string();
    let r = app.post(&format!("/api/jobs/{job_id}/heartbeat"))
        .json(&serde_json::json!({
            "candidates_attempted_delta": 5, "candidates_verified_delta": 0,
            "lake_slot_hours_consumed_delta": 0.05,
            "current_best_fitness": 0.62, "current_best_chain_length": 3
        })).bearer(WORKER_KEY_1).await;
    assert_eq!(r.status(), 200);
    let body: serde_json::Value = r.json().await;
    assert_eq!(body["continue"], true);
}
```

- [ ] **Step 2: Run failing test**

Expected: FAIL.

- [ ] **Step 3: Implement handler + sanity cap**

```rust
#[derive(Deserialize)]
pub struct HeartbeatBody {
    pub candidates_attempted_delta: i32,
    pub candidates_verified_delta: i32,
    pub lake_slot_hours_consumed_delta: f32,
    pub current_best_fitness: f32,
    pub current_best_chain_length: i32,
}

pub async fn heartbeat(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
    Json(body): Json<HeartbeatBody>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response() };
    let job = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) => j, Ok(None) => return StatusCode::NOT_FOUND.into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response(),
    };
    if job.claimed_by.as_deref() != Some(&auth.worker_id_string()) {
        return StatusCode::FORBIDDEN.into_response();
    }
    // Cap at 2 * (wallclock_seconds / 3600) * slots_held to defeat lying workers
    let wallclock_s = job.last_heartbeat_at
        .map(|t| (chrono::Utc::now() - t).num_seconds() as f32)
        .unwrap_or(60.0);
    // v1: every paid job gets a fixed 4-slot allocation (matches the 96 slot-hour
    // quota = 4 slots × 24 h). When elastic per-job sizing lands in v2, store the
    // allocated slot count on conjecture_jobs and read it here.
    let slots_held = 4.0;
    let max_delta = 2.0 * (wallclock_s / 3600.0) * slots_held;
    let consumed_delta = body.lake_slot_hours_consumed_delta.min(max_delta).max(0.0);
    let new_consumed = job.lake_slot_hours_consumed + consumed_delta;
    let exhausted = new_consumed >= job.lake_slot_hours_quota as f32;
    nasrudin_pg::query::conjecture_jobs::extend_heartbeat(pg, id, body.candidates_attempted_delta,
        body.candidates_verified_delta, consumed_delta, body.current_best_fitness,
        body.current_best_chain_length).await.ok();
    if exhausted {
        nasrudin_pg::query::conjecture_jobs::release_claim(pg, id, "budget_exhausted").await.ok();
        state.capacity.release_paid_slots(slots_held as u32);
        // SSE emission handled in Task 5.2; for now just respond.
        return Json(serde_json::json!({ "continue": false, "reason": "budget_exhausted" })).into_response();
    }
    Json(serde_json::json!({ "continue": true })).into_response()
}
```

`extend_heartbeat` PG helper:
```rust
pub async fn extend_heartbeat(
    db: &DatabaseConnection, id: Uuid,
    cand_attempted_delta: i32, cand_verified_delta: i32,
    consumed_delta: f32, _best_fit: f32, _best_chain: i32,
) -> Result<(), DbErr> {
    let stmt = sea_orm::Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        r#"UPDATE conjecture_jobs SET
            last_heartbeat_at = NOW(),
            lease_expires_at = NOW() + interval '5 minutes',
            state = 'running',
            candidates_attempted = candidates_attempted + $2,
            candidates_verified = candidates_verified + $3,
            lake_slot_hours_consumed = lake_slot_hours_consumed + $4
           WHERE id = $1"#,
        [id.into(), cand_attempted_delta.into(), cand_verified_delta.into(), consumed_delta.into()],
    );
    db.execute(stmt).await?;
    Ok(())
}
```

Register `.route("/api/jobs/:id/heartbeat", post(handlers::jobs_claim::heartbeat))`.

- [ ] **Step 4: Run test**

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/
git commit -m "Add POST /api/jobs/{id}/heartbeat with quota debit + sanity cap"
```

---

### Task 4.5: `POST /api/jobs/{id}/release`

**Files:**
- Modify: `engine/crates/api/src/handlers/jobs_claim.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Implement**

```rust
pub async fn release(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p,
        None => return StatusCode::SERVICE_UNAVAILABLE.into_response() };
    let job = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) => j, Ok(None) => return StatusCode::NOT_FOUND.into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response(),
    };
    if job.claimed_by.as_deref() != Some(&auth.worker_id_string()) {
        return StatusCode::FORBIDDEN.into_response();
    }
    nasrudin_pg::query::conjecture_jobs::release_claim(pg, id, "queued").await.ok();
    state.capacity.release_paid_slots(4);  // v1: assume 4
    StatusCode::OK.into_response()
}
```

Route: `.route("/api/jobs/:id/release", post(handlers::jobs_claim::release))`.

- [ ] **Step 2: Test + commit**

Smoke: claim → release → next claim succeeds.
```bash
git add engine/crates/api/
git commit -m "Add POST /api/jobs/{id}/release"
```

---

### Task 4.6: Reaper task for expired leases

**Files:**
- Create: `engine/crates/api/src/jobs/reaper.rs`
- Modify: `engine/crates/api/src/main.rs` (spawn task)

- [ ] **Step 1: Write failing test**

```rust
#[tokio::test]
async fn reaper_requeues_expired_lease() {
    let db = nasrudin_pg::test_helpers::setup_test_db().await;
    seed_claimed_job_with_expired_lease(&db).await;
    reap_dead_leases(&db).await.unwrap();
    let job = nasrudin_pg::query::conjecture_jobs::get_by_id(&db, JOB_ID).await.unwrap().unwrap();
    assert_eq!(job.state, "queued");
    assert!(job.claimed_by.is_none());
}
```

- [ ] **Step 2: Run failing test**

Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
//! Reap leases that exceeded their TTL without a heartbeat.

use sea_orm::{DatabaseConnection, Statement};

pub async fn reap_dead_leases(db: &DatabaseConnection) -> Result<u64, sea_orm::DbErr> {
    let r = db.execute(Statement::from_string(
        sea_orm::DatabaseBackend::Postgres,
        r#"UPDATE conjecture_jobs
           SET state='queued', claimed_by=NULL, claimed_at=NULL, lease_expires_at=NULL
           WHERE state IN ('claimed','running') AND lease_expires_at < NOW()"#.into(),
    )).await?;
    Ok(r.rows_affected())
}
```

In `main.rs` after the steerer spawn:
```rust
let pg_for_reaper = pg.clone();
tokio::spawn(async move {
    let mut tick = tokio::time::interval(std::time::Duration::from_secs(60));
    loop {
        tick.tick().await;
        if let Some(ref pg) = pg_for_reaper {
            match crate::jobs::reaper::reap_dead_leases(pg).await {
                Ok(n) if n > 0 => tracing::info!(n, "reaped expired leases"),
                Ok(_) => {}
                Err(e) => tracing::error!(error=%e, "reaper failed"),
            }
        }
    }
});
```

- [ ] **Step 4: Run test + commit**

```bash
git add engine/crates/api/src/
git commit -m "Add reaper task for expired conjecture-job leases"
```

---

## Phase 5 — User-facing paid flow

### Task 5.1: `POST /api/research/jobs` (create + decrement credits)

**Files:**
- Create: `engine/crates/api/src/handlers/research_jobs.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Write failing test**

```rust
#[tokio::test]
async fn create_research_job_decrements_credits() {
    let app = test_helpers::boot_test_api().await;
    seed_user_with_credits(&app, 1).await;
    let r = app.post("/api/research/jobs").json(&serde_json::json!({
        "hunch": "energy = mass times c squared",
        "domain_hint": "special_relativity"
    })).cookie_session().await;
    assert_eq!(r.status(), 201);
    let body: serde_json::Value = r.json().await;
    assert!(body["job_id"].is_string());
    let credits_after = get_user_credits(&app).await;
    assert_eq!(credits_after, 0);
}

#[tokio::test]
async fn create_research_job_rejects_zero_credits() {
    let app = test_helpers::boot_test_api().await;
    seed_user_with_credits(&app, 0).await;
    let r = app.post("/api/research/jobs").json(&...).cookie_session().await;
    assert_eq!(r.status(), 402);  // Payment Required
}
```

- [ ] **Step 2: Run failing tests**

Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use std::sync::Arc;
use uuid::Uuid;
use crate::auth::AuthSess;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct CreateBody {
    pub hunch: String,
    #[serde(default)] pub domain_hint: Option<String>,
}

pub async fn create(
    State(state): State<Arc<AppState>>,
    auth: AuthSess,
    Json(body): Json<CreateBody>,
) -> impl IntoResponse {
    if body.hunch.trim().is_empty() {
        return (StatusCode::BAD_REQUEST, Json(serde_json::json!({"error":"hunch_required"}))).into_response();
    }
    let pg = match &state.pg { Some(p) => p,
        None => return StatusCode::SERVICE_UNAVAILABLE.into_response() };
    // Atomic credits decrement
    let decremented = nasrudin_pg::query::users::try_decrement_research_credits(pg, auth.user_id).await
        .unwrap_or(false);
    if !decremented {
        return (StatusCode::PAYMENT_REQUIRED,
                Json(serde_json::json!({"error":"no_research_credits"}))).into_response();
    }
    let id = Uuid::new_v4();
    let am = nasrudin_pg::entity::conjecture_jobs::ActiveModel {
        id: sea_orm::ActiveValue::Set(id),
        owner_id: sea_orm::ActiveValue::Set(auth.user_id),
        state: sea_orm::ActiveValue::Set("queued".into()),
        hunch: sea_orm::ActiveValue::Set(body.hunch),
        domain_hint: sea_orm::ActiveValue::Set(body.domain_hint),
        provider: sea_orm::ActiveValue::Set("internal".into()),
        model: sea_orm::ActiveValue::Set("ga".into()),
        budget: sea_orm::ActiveValue::Set(serde_json::json!({"wall_seconds":86400,"max_candidates":10000000})),
        candidates_attempted: sea_orm::ActiveValue::Set(0),
        candidates_verified: sea_orm::ActiveValue::Set(0),
        lake_slot_hours_quota: sea_orm::ActiveValue::Set(96),
        lake_slot_hours_consumed: sea_orm::ActiveValue::Set(0.0),
        slice_priority: sea_orm::ActiveValue::Set(5),
        tier: sea_orm::ActiveValue::Set("researcher".into()),
        ..Default::default()
    };
    use sea_orm::ActiveModelTrait;
    am.insert(pg).await.ok();
    (StatusCode::CREATED, Json(serde_json::json!({ "job_id": id, "state": "queued" }))).into_response()
}
```

`try_decrement_research_credits`:
```rust
pub async fn try_decrement_research_credits(
    db: &DatabaseConnection, user_id: Uuid,
) -> Result<bool, DbErr> {
    let r = db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = research_credits - 1
         WHERE id=$1 AND research_credits > 0",
        [user_id.into()],
    )).await?;
    Ok(r.rows_affected() == 1)
}

pub async fn refund_research_credit(db: &DatabaseConnection, user_id: Uuid) -> Result<(), DbErr> {
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE users SET research_credits = research_credits + 1 WHERE id=$1",
        [user_id.into()],
    )).await?;
    Ok(())
}
```

Route: `.route("/api/research/jobs", post(handlers::research_jobs::create))`.

- [ ] **Step 4: Run test + commit**

Run: `cargo test -p physics-api --test create_research_job`
Expected: PASS.

```bash
git add engine/crates/
git commit -m "Add POST /api/research/jobs with credit decrement"
```

---

### Task 5.2: `GET /api/research/jobs` + `GET /api/research/jobs/{id}`

**Files:**
- Modify: `engine/crates/api/src/handlers/research_jobs.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Implement list + detail**

```rust
pub async fn list(
    State(state): State<Arc<AppState>>, auth: AuthSess,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return StatusCode::SERVICE_UNAVAILABLE.into_response() };
    use sea_orm::*;
    let rows = nasrudin_pg::entity::conjecture_jobs::Entity::find()
        .filter(nasrudin_pg::entity::conjecture_jobs::Column::OwnerId.eq(auth.user_id))
        .order_by_desc(nasrudin_pg::entity::conjecture_jobs::Column::CreatedAt)
        .all(pg).await.unwrap_or_default();
    Json(serde_json::json!({"jobs": rows})).into_response()
}

pub async fn detail(
    State(state): State<Arc<AppState>>, auth: AuthSess, Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return StatusCode::SERVICE_UNAVAILABLE.into_response() };
    match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) if j.owner_id == auth.user_id => Json(j).into_response(),
        Ok(Some(_)) => StatusCode::FORBIDDEN.into_response(),
        Ok(None) => StatusCode::NOT_FOUND.into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response(),
    }
}
```

Routes: `.route("/api/research/jobs", get(...).post(...))` and `.route("/api/research/jobs/:id", get(handlers::research_jobs::detail))`.

- [ ] **Step 2: Smoke test + commit**

```bash
git add engine/crates/api/src/
git commit -m "Add list + detail for /api/research/jobs"
```

---

### Task 5.3: SSE `/api/research/jobs/{id}/events`

**Files:**
- Modify: `engine/crates/api/src/handlers/research_jobs.rs`
- Modify: `engine/crates/api/src/state.rs` (per-job broadcast channel)
- Modify: `engine/crates/api/src/handlers/jobs_claim.rs` (emit on heartbeat + state change)

- [ ] **Step 1: Add per-job broadcast in `AppState`**

```rust
pub job_events: Arc<DashMap<Uuid, tokio::sync::broadcast::Sender<JobEvent>>>,
```

```rust
#[derive(Debug, Clone, Serialize)]
pub enum JobEvent {
    JobState { state: String },
    Progress { candidates_attempted: i32, candidates_verified: i32, best_fitness: f32, best_chain_length: i32 },
    TheoremVerified { theorem_id: String, statement_latex: String },
    Proved { lean_url: String },
    BudgetExhausted { best_partial_summary: String, refund_credits: i32 },
}
```

Helper to fire:
```rust
pub fn emit_job_event(state: &AppState, job_id: Uuid, ev: JobEvent) {
    let entry = state.job_events.entry(job_id).or_insert_with(|| {
        let (tx, _) = tokio::sync::broadcast::channel(64);
        tx
    });
    let _ = entry.send(ev);
}
```

- [ ] **Step 2: Emit from heartbeat / release / create**

Wherever `release_claim` is called with a terminal state, fire the matching `JobEvent`. On heartbeat fire `Progress`.

- [ ] **Step 3: Implement SSE handler**

```rust
use axum::response::sse::{Event, KeepAlive, Sse};
use futures::stream::{self, Stream};
use std::convert::Infallible;
use tokio_stream::wrappers::BroadcastStream;
use tokio_stream::StreamExt;

pub async fn events(
    State(state): State<Arc<AppState>>, auth: AuthSess, Path(id): Path<Uuid>,
) -> Result<Sse<impl Stream<Item = Result<Event, Infallible>>>, StatusCode> {
    let pg = state.pg.as_ref().ok_or(StatusCode::SERVICE_UNAVAILABLE)?;
    let job = nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?.ok_or(StatusCode::NOT_FOUND)?;
    if job.owner_id != auth.user_id { return Err(StatusCode::FORBIDDEN); }
    let entry = state.job_events.entry(id).or_insert_with(|| {
        let (tx, _) = tokio::sync::broadcast::channel(64); tx
    });
    let rx = entry.subscribe();
    let stream = BroadcastStream::new(rx).filter_map(|r| r.ok()).map(|ev| {
        let json = serde_json::to_string(&ev).unwrap_or_else(|_| "{}".into());
        Ok(Event::default().data(json))
    });
    Ok(Sse::new(stream).keep_alive(KeepAlive::default()))
}
```

Route: `.route("/api/research/jobs/:id/events", get(handlers::research_jobs::events))`.

- [ ] **Step 4: Smoke + commit**

Smoke: open SSE via `curl -N`, fire a heartbeat from a worker, see Progress event.
```bash
git add engine/crates/api/src/
git commit -m "Add SSE /api/research/jobs/{id}/events"
```

---

### Task 5.4: Cancel + refund

**Files:**
- Modify: `engine/crates/api/src/handlers/research_jobs.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Implement cancel**

```rust
pub async fn cancel(
    State(state): State<Arc<AppState>>, auth: AuthSess, Path(id): Path<Uuid>,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return StatusCode::SERVICE_UNAVAILABLE.into_response() };
    let job = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) if j.owner_id == auth.user_id => j,
        Ok(Some(_)) => return StatusCode::FORBIDDEN.into_response(),
        Ok(None) => return StatusCode::NOT_FOUND.into_response(),
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response(),
    };
    if matches!(job.state.as_str(), "proved" | "budget_exhausted" | "cancelled") {
        return (StatusCode::CONFLICT, "terminal").into_response();
    }
    let was_in_flight = job.state == "claimed" || job.state == "running";
    nasrudin_pg::query::conjecture_jobs::release_claim(pg, id, "cancelled").await.ok();
    nasrudin_pg::query::users::refund_research_credit(pg, auth.user_id).await.ok();
    if was_in_flight { state.capacity.release_paid_slots(4); }
    crate::handlers::research_jobs::emit_job_event(&state, id,
        crate::state::JobEvent::JobState { state: "cancelled".into() });
    StatusCode::OK.into_response()
}
```

Route: `.route("/api/research/jobs/:id/cancel", post(handlers::research_jobs::cancel))`.

- [ ] **Step 2: Test + commit**

Smoke: create job, cancel, assert credit returned.
```bash
git add engine/crates/api/src/
git commit -m "Add cancel + refund for research jobs"
```

---

## Phase 6 — Worker integration

### Task 6.1: Worker `/api/jobs/claim` poll

**Files:**
- Modify: `engine/crates/ga/src/bin/worker.rs`

- [ ] **Step 1: Add claim poll between chunks**

In the worker's chunk-boundary loop, before requesting a fresh `/api/seed`:
```rust
let claim = http.post(format!("{}/api/jobs/claim", api_base))
    .bearer_auth(&worker_key)
    .json(&serde_json::json!({
        "available_lake_slots": resource_budget.lake_slots,
        "domains_supported": vec!["all"],
    }))
    .send().await.ok();
match claim.as_ref().map(|r| r.status()) {
    Some(s) if s.is_success() => {
        let job: serde_json::Value = claim.unwrap().json().await.unwrap();
        run_paid_slice(&job, &http, &api_base, &worker_key, &resource_budget).await;
        continue;  // skip explorer-fleet duty this chunk
    }
    Some(s) if s.as_u16() == 204 => { /* fall through to explorer fleet */ }
    _ => { /* error: log + fall through */ }
}
```

- [ ] **Step 2: Smoke**

Boot API + worker, seed one queued job, watch worker logs claim + run slice.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/ga/src/bin/worker.rs
git commit -m "Add /api/jobs/claim poll to worker chunk loop"
```

---

### Task 6.2: Per-job slice GA loop

**Files:**
- Create: `engine/crates/ga/src/paid_slice.rs`
- Modify: `engine/crates/ga/src/bin/worker.rs`

The slice runner takes a job's hunch + domain_hint + suggestions, sets up a chain_engine pinned to the conjecture target, and grinds for a budget window emitting heartbeats every 30s.

- [ ] **Step 1: Stub slice runner**

```rust
//! Run a single paid GA slice for one conjecture job.

use std::time::Duration;
use serde::Deserialize;

#[derive(Deserialize)]
pub struct PaidJobSpec {
    pub job_id: uuid::Uuid,
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub suggestions: Option<serde_json::Value>,
    pub lake_slot_hours_remaining: f32,
    pub heartbeat_url: String,
}

pub async fn run_paid_slice(
    spec: &PaidJobSpec,
    http: &reqwest::Client,
    api_base: &str,
    worker_key: &str,
    budget: &crate::auto_size::ResourceBudget,
) {
    let mut tick = tokio::time::interval(Duration::from_secs(30));
    let mut candidates_attempted = 0i32;
    let mut candidates_verified = 0i32;
    let mut consumed_h = 0.0f32;
    let mut last_hb = std::time::Instant::now();
    let slot_h = budget.lake_slots as f32;
    // For v1: drive a chain_engine here with target_shape pinned to spec.hunch.
    // Pseudocode — wire into existing chain_engine APIs:
    //   let mut engine = ChainEngine::new_for_paid_slice(spec.hunch, spec.domain_hint, ...);
    //   loop one chunk; collect (attempted, verified, best_fitness, best_chain_length).
    loop {
        tick.tick().await;
        let dt = last_hb.elapsed().as_secs_f32() / 3600.0;
        consumed_h += dt * slot_h;
        last_hb = std::time::Instant::now();
        let resp = http.post(format!("{}{}", api_base, spec.heartbeat_url))
            .bearer_auth(worker_key)
            .json(&serde_json::json!({
                "candidates_attempted_delta": candidates_attempted,
                "candidates_verified_delta": candidates_verified,
                "lake_slot_hours_consumed_delta": dt * slot_h,
                "current_best_fitness": 0.0,
                "current_best_chain_length": 0,
            }))
            .send().await;
        candidates_attempted = 0;
        candidates_verified = 0;
        if let Ok(r) = resp {
            if let Ok(v) = r.json::<serde_json::Value>().await {
                if v["continue"] == false { break; }
            }
        }
        if consumed_h >= spec.lake_slot_hours_remaining { break; }
    }
}
```

- [ ] **Step 2: Wire chain_engine for per-slice fitness**

Add `ChainEngine::with_target(hunch_latex)` constructor that compiles the hunch via `nasrudin_core::expr::parse_latex` (existing in the conjecture system) into a target Expr, and adds a `target_proximity` term to the fitness. Reuse the `target_shape` field already in `LlmSuggestion`.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/ga/
git commit -m "Add paid-slice GA loop in worker"
```

---

### Task 6.3: Lean-success detection in slice → Proved

**Files:**
- Modify: `engine/crates/ga/src/paid_slice.rs`
- Modify: `engine/crates/api/src/handlers/jobs_claim.rs` (new endpoint `mark_proved`)

- [ ] **Step 1: Detection trigger**

When the slice's chain_engine emits a Verified theorem whose canonical hash matches the target Expr (or whose `lean_source` lake-builds successfully against the target), the worker calls `POST /api/jobs/{id}/mark_proved` with the verified theorem's id.

- [ ] **Step 2: Implement `mark_proved`**

```rust
pub async fn mark_proved(
    State(state): State<Arc<AppState>>, auth: WorkerAuth, Path(id): Path<Uuid>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let theorem_id_hex = body["theorem_id_hex"].as_str().unwrap_or("");
    let pg = match &state.pg { Some(p) => p, None => return StatusCode::SERVICE_UNAVAILABLE.into_response() };
    let job = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(j)) => j, _ => return StatusCode::NOT_FOUND.into_response(),
    };
    if job.claimed_by.as_deref() != Some(&auth.worker_id_string()) {
        return StatusCode::FORBIDDEN.into_response();
    }
    // Append the verified theorem to verified_theorem_ids and flip state.
    nasrudin_pg::query::conjecture_jobs::append_verified_and_finalise(pg, id, theorem_id_hex).await.ok();
    state.capacity.release_paid_slots(4);
    crate::handlers::research_jobs::emit_job_event(&state, id,
        crate::state::JobEvent::Proved { lean_url: format!("/api/theorems/{theorem_id_hex}/lean") });
    StatusCode::OK.into_response()
}
```

`append_verified_and_finalise`:
```rust
pub async fn append_verified_and_finalise(db: &DatabaseConnection, id: Uuid, hex: &str) -> Result<(), DbErr> {
    let id_bytes = hex::decode(hex).unwrap_or_default();
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"UPDATE conjecture_jobs SET
            state='proved', outcome='proved',
            verified_theorem_ids = COALESCE(verified_theorem_ids, ARRAY[]::bytea[]) || ARRAY[$2::bytea],
            completed_at = NOW(),
            claimed_by=NULL, claimed_at=NULL, lease_expires_at=NULL
           WHERE id=$1"#,
        [id.into(), id_bytes.into()],
    )).await?;
    Ok(())
}
```

Route: `.route("/api/jobs/:id/mark_proved", post(handlers::jobs_claim::mark_proved))`.

- [ ] **Step 3: Smoke + commit**

```bash
git add engine/crates/
git commit -m "Add proof-success detection from worker slice"
```

---

## Phase 7 — Observability + admin

### Task 7.1: Metrics

**Files:**
- Modify: `engine/crates/api/src/metrics.rs`

- [ ] **Step 1: Add gauges**

Append to the existing `/metrics` handler:
```rust
let snap = state.steering.load();
out.push_str("# TYPE nasrudin_steerer_mode gauge\n");
out.push_str(&format!("nasrudin_steerer_mode{{scope=\"{}\"}} 1\n",
    snap.config["scope"].as_str().unwrap_or("?")));

if let Ok(active) = nasrudin_pg::query::conjecture_jobs::count_by_state(pg, &["claimed","running"]).await {
    out.push_str("# TYPE nasrudin_paid_jobs_active gauge\n");
    out.push_str(&format!("nasrudin_paid_jobs_active {active}\n"));
}
if let Ok(queued) = nasrudin_pg::query::conjecture_jobs::count_by_state(pg, &["queued"]).await {
    out.push_str("# TYPE nasrudin_paid_jobs_queued gauge\n");
    out.push_str(&format!("nasrudin_paid_jobs_queued {queued}\n"));
}
let total = state.capacity.total_lake_slots();
let paid = state.capacity.paid_slots();
out.push_str("# TYPE nasrudin_explorer_slot_count gauge\n");
out.push_str(&format!("nasrudin_explorer_slot_count {}\n", total.saturating_sub(paid)));
out.push_str("# TYPE nasrudin_explorer_floor_satisfied gauge\n");
out.push_str(&format!("nasrudin_explorer_floor_satisfied {}\n",
    if crate::jobs::quota::floor_satisfied(total, paid) { 1 } else { 0 }));
```

Add counters via static `AtomicU64` for `steerer_cycles_total`, `steerer_validation_fails_total`, `steerer_provider_errors_total{model}`. Increment in `cycle.rs` at the relevant points.

- [ ] **Step 2: Smoke**

`curl http://localhost:3001/metrics | grep nasrudin_steerer`

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/
git commit -m "Add steerer + paid-job metrics"
```

---

### Task 7.2: Admin endpoints

**Files:**
- Modify: `engine/crates/api/src/handlers/admin.rs`
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Add `GET /api/admin/steering/recent`**

```rust
pub async fn steering_recent(
    State(state): State<Arc<AppState>>, _admin: AdminToken,
) -> impl IntoResponse {
    let pg = match &state.pg { Some(p) => p, None => return StatusCode::SERVICE_UNAVAILABLE.into_response() };
    match nasrudin_pg::query::cluster_steering::list_recent(pg, 50).await {
        Ok(rows) => Json(rows).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response(),
    }
}
```

- [ ] **Step 2: Add `POST /api/admin/steering/force`**

Body = a `SteeringConfig`. Validates, persists as a manual cycle (model_id="admin_override"), updates ArcSwap.

- [ ] **Step 3: Routes + commit**

```rust
.route("/api/admin/steering/recent", get(handlers::admin::steering_recent))
.route("/api/admin/steering/force", post(handlers::admin::steering_force))
```

```bash
git add engine/crates/api/src/
git commit -m "Add admin endpoints for steering observability"
```

---

## Phase 8 — Soak + cutover

### Task 8.1: Smoke fixture script

**Files:**
- Create: `deploy/test/soak-cluster-steerer.sh`

- [ ] **Step 1: Write the script**

```bash
#!/usr/bin/env bash
# 24h soak: 1 paid job, 5 simulated workers, fake demand traffic.
# Asserts: steerer cycles, mode flips, paid job runs through proved-or-budget-exhausted,
# explorer floor never violated.
set -euo pipefail
API=${API:-http://localhost:3001}
# 1. POST /api/research/jobs as a seeded researcher account.
# 2. Boot 5 worker processes pointed at the API.
# 3. Generate fake search hits via curl loops in 3 domains.
# 4. Tail /metrics every minute and log nasrudin_steerer_*, nasrudin_paid_jobs_*.
# 5. After 24h: dump cluster_steering rows + the conjecture_jobs row.
```

- [ ] **Step 2: Commit**

```bash
git add deploy/test/
git commit -m "Add 24h soak fixture for steerer + paid jobs"
```

---

### Task 8.2: 24h soak run + acceptance

**Files:** none (operational task).

- [ ] **Step 1: Run the soak**

Run the script on a non-production droplet. Watch metrics + logs for 24h.

- [ ] **Step 2: Acceptance checklist**

- [ ] `cluster_steering` has ~144 rows (one per 10 min).
- [ ] At least 5 rows have `validation_failed=false` AND `outcome_json` populated.
- [ ] Mode flipped to B during the paid-job's active window; flipped back to C after.
- [ ] `nasrudin_explorer_floor_satisfied == 1` for ≥99.9% of the window.
- [ ] Paid job either completed `proved` with a Lean artifact or `budget_exhausted` with a credit refund.
- [ ] Reaper requeued at least one expired lease cleanly (kill a worker mid-job to verify).

- [ ] **Step 3: Tag release**

```bash
git tag v0.10.0-cluster-steerer
git push origin v0.10.0-cluster-steerer
```

---

## Cross-cutting safeguards

- **Server-owned Gradient key.** `GRADIENT_API_KEY` lives only in the API daemon's env (deploy/.env on the droplet). Never user-stored, never decrypted per-request — distinct from the per-user encrypted key flow in `conjecture/orchestrate.rs`.
- **No runtime panics on Gradient outage.** All Gradient calls go through `LlmCaller`; on error, the steerer logs + reuses last-known-good. The cluster keeps running with stale-but-validated config indefinitely.
- **Floor never violated by claim path.** The claim handler checks `floor_satisfied(total, paid + this_worker_slots)` BEFORE awarding the claim. If awarding would violate floor → 204 (worker falls through to explorer).
- **Quota cannot go negative.** `lake_slot_hours_consumed_delta` is server-side capped at `2 * (wallclock / 3600) * slots_held`.
- **Refund rule: zero verified AND <1000 candidates.** Anything with a partial result (≥1 verified or ≥1000 candidates) does NOT refund — the user got value (their conjecture led to corpus growth under their attribution).
- **Steering writes invalidate seed cache.** Otherwise workers see stale steering for up to 30s after a cycle.
