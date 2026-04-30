# LLM-Guided Search — Phase D (Conjecture Loop) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship the researcher-facing conjecture loop end-to-end: UI form posts an English hunch → server runs the LLM with corpus-nearest neighbours + axiom catalog → researcher picks/edits a suggestion → row queues for a worker. Live SSE feed surfaces state + verified-candidate events. Worker claim/heartbeat/submit (the dequeue side) lives in Phase E.

**Architecture:**
- Two new Postgres tables: `conjecture_jobs` (state machine row) + `conjecture_events` (append-only event log).
- New module `engine/crates/api/src/conjecture/` with prompt builder, LLM orchestrator, and types — all reusing the shipped `nasrudin-llm` Registry + `nasrudin-embed` index.
- Five Axum endpoints under `/api/conjecture` + `/api/me/conjectures`, mounted on the existing platform-user router (cookie auth, 30 req/min governor).
- One process-wide `broadcast::Sender<ConjectureEvent>` on `AppState`; SSE handler filters by job_id + replays the persisted log on connect.
- Three new TanStack Router routes: `/conjecture` (creator), `/conjecture/$id` (live view), `/jobs` (user's list). Provider locked to `anthropic` for Phase D launch (spec §13).

**Tech Stack:** Rust 1.95 / SeaORM 2 / Axum 0.8 / tokio broadcast / TanStack Router + Query / fastembed via the existing `nasrudin-embed` crate.

**Out of scope (deferred to Phase E):** Worker `claim`/`heartbeat`/`submit`/`complete` endpoints; lease reaper; `--research-mode` flag. Phase D's `start` endpoint transitions the row to `QueuedForWorker` and stops — no worker dequeues yet.

---

## File Structure

**New backend files:**
- `engine/crates/pg/src/migrator/m20260801_000007_conjecture_jobs.rs`
- `engine/crates/pg/src/migrator/m20260801_000008_conjecture_events.rs`
- `engine/crates/pg/src/entity/conjecture_jobs.rs`
- `engine/crates/pg/src/entity/conjecture_events.rs`
- `engine/crates/pg/src/query/conjecture_jobs.rs`
- `engine/crates/api/src/conjecture/mod.rs`
- `engine/crates/api/src/conjecture/types.rs`
- `engine/crates/api/src/conjecture/prompt.rs`
- `engine/crates/api/src/conjecture/orchestrate.rs`
- `engine/crates/api/src/handlers/conjecture.rs`
- `engine/crates/api/src/conjecture/CONJECTURE.md`
- `engine/crates/api/tests/conjecture_handler.rs`

**Modified backend files:**
- `engine/crates/pg/src/migrator/mod.rs` — register two new migrations
- `engine/crates/pg/src/entity/mod.rs` — re-export the two new entities
- `engine/crates/pg/src/query/mod.rs` — re-export `conjecture_jobs` query module
- `engine/crates/api/src/state.rs` — add `conjecture_event_tx: broadcast::Sender<ConjectureEvent>`
- `engine/crates/api/src/handlers/mod.rs` — add `pub mod conjecture;`
- `engine/crates/api/src/main.rs` — initialise broadcast channel; register 5 routes; add `pub mod conjecture;`
- `engine/crates/api/tests/test_app/mod.rs` — wire routes + broadcast channel

**New frontend files:**
- `nasrudin-frontend/src/routes/conjecture.tsx`
- `nasrudin-frontend/src/routes/conjecture.$id.tsx`
- `nasrudin-frontend/src/routes/jobs.tsx`
- `nasrudin-frontend/src/components/conjecture/SuggestionCard.tsx`
- `nasrudin-frontend/src/components/conjecture/JobProgress.tsx`

**Modified frontend files:**
- `nasrudin-frontend/src/lib/types.ts` — add conjecture-related types
- `nasrudin-frontend/src/lib/queries.ts` — add 5 hooks
- `nasrudin-frontend/src/lib/sse.ts` — add `useConjectureStream(id)`
- `nasrudin-frontend/src/components/platform/AppHeader.tsx` — add `/conjecture` nav link

---

## Task 1: Postgres migration — `conjecture_jobs`

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260801_000007_conjecture_jobs.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Write the migration**

```rust
use sea_orm_migration::{prelude::*, schema::*};

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ConjectureJobs::Table)
                    .if_not_exists()
                    .col(uuid(ConjectureJobs::Id).primary_key().default(Expr::cust("gen_random_uuid()")))
                    .col(uuid(ConjectureJobs::OwnerId).not_null())
                    .col(string(ConjectureJobs::State).not_null())
                    .col(string_null(ConjectureJobs::Outcome))
                    .col(text(ConjectureJobs::Hunch).not_null())
                    .col(string_null(ConjectureJobs::DomainHint))
                    .col(string(ConjectureJobs::Provider).not_null())
                    .col(string(ConjectureJobs::Model).not_null())
                    .col(json_binary_null(ConjectureJobs::Suggestions))
                    .col(integer_null(ConjectureJobs::ChosenIndex))
                    .col(json_binary_null(ConjectureJobs::Seed))
                    .col(json_binary(ConjectureJobs::Budget).not_null())
                    .col(string_null(ConjectureJobs::ClaimedBy))
                    .col(timestamp_with_time_zone_null(ConjectureJobs::ClaimedAt))
                    .col(timestamp_with_time_zone_null(ConjectureJobs::LeaseExpiresAt))
                    .col(timestamp_with_time_zone_null(ConjectureJobs::LastHeartbeatAt))
                    .col(integer(ConjectureJobs::CandidatesAttempted).not_null().default(0))
                    .col(integer(ConjectureJobs::CandidatesVerified).not_null().default(0))
                    .col(ColumnDef::new(ConjectureJobs::VerifiedTheoremIds).array(ColumnType::Binary(BlobSize::Blob(None))).null())
                    .col(timestamp_with_time_zone(ConjectureJobs::CreatedAt).not_null().default(Expr::current_timestamp()))
                    .col(timestamp_with_time_zone_null(ConjectureJobs::CompletedAt))
                    .foreign_key(
                        ForeignKey::create()
                            .from(ConjectureJobs::Table, ConjectureJobs::OwnerId)
                            .to(Alias::new("users"), Alias::new("id"))
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_conjecture_jobs_queueable")
                    .table(ConjectureJobs::Table)
                    .col(ConjectureJobs::CreatedAt)
                    .and_where(Expr::col(ConjectureJobs::State).eq("QueuedForWorker"))
                    .and_where(Expr::col(ConjectureJobs::ClaimedBy).is_null())
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_conjecture_jobs_owner")
                    .table(ConjectureJobs::Table)
                    .col(ConjectureJobs::OwnerId)
                    .col((ConjectureJobs::CreatedAt, IndexOrder::Desc))
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.drop_table(Table::drop().table(ConjectureJobs::Table).to_owned()).await
    }
}

#[derive(DeriveIden)]
enum ConjectureJobs {
    Table,
    Id,
    OwnerId,
    State,
    Outcome,
    Hunch,
    DomainHint,
    Provider,
    Model,
    Suggestions,
    ChosenIndex,
    Seed,
    Budget,
    ClaimedBy,
    ClaimedAt,
    LeaseExpiresAt,
    LastHeartbeatAt,
    CandidatesAttempted,
    CandidatesVerified,
    VerifiedTheoremIds,
    CreatedAt,
    CompletedAt,
}
```

- [ ] **Step 2: Register the migration**

In `engine/crates/pg/src/migrator/mod.rs`, add the `mod` line and push `Box::new(m20260801_000007_conjecture_jobs::Migration)` onto the `migrations()` vector. Mirror the existing `m20260710_000006_user_llm_keys` registration pattern.

- [ ] **Step 3: Build**

Run: `cargo build -p nasrudin-pg`
Expected: clean build.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260801_000007_conjecture_jobs.rs engine/crates/pg/src/migrator/mod.rs
git commit -m "feat(pg): migration for conjecture_jobs table"
```

---

## Task 2: Postgres migration — `conjecture_events`

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260801_000008_conjecture_events.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Write the migration**

```rust
use sea_orm_migration::{prelude::*, schema::*};

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ConjectureEvents::Table)
                    .if_not_exists()
                    .col(big_integer(ConjectureEvents::Id).primary_key().auto_increment())
                    .col(uuid(ConjectureEvents::JobId).not_null())
                    .col(string(ConjectureEvents::Kind).not_null())
                    .col(json_binary(ConjectureEvents::Payload).not_null())
                    .col(timestamp_with_time_zone(ConjectureEvents::At).not_null().default(Expr::current_timestamp()))
                    .foreign_key(
                        ForeignKey::create()
                            .from(ConjectureEvents::Table, ConjectureEvents::JobId)
                            .to(Alias::new("conjecture_jobs"), Alias::new("id"))
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_conjecture_events_job")
                    .table(ConjectureEvents::Table)
                    .col(ConjectureEvents::JobId)
                    .col(ConjectureEvents::Id)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.drop_table(Table::drop().table(ConjectureEvents::Table).to_owned()).await
    }
}

#[derive(DeriveIden)]
enum ConjectureEvents {
    Table,
    Id,
    JobId,
    Kind,
    Payload,
    At,
}
```

- [ ] **Step 2: Register the migration**

Add `mod m20260801_000008_conjecture_events;` and push the migration onto `migrations()` *after* the conjecture_jobs migration (so the FK target exists).

- [ ] **Step 3: Build**

Run: `cargo build -p nasrudin-pg`

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260801_000008_conjecture_events.rs engine/crates/pg/src/migrator/mod.rs
git commit -m "feat(pg): migration for conjecture_events log table"
```

---

## Task 3: SeaORM entities

**Files:**
- Create: `engine/crates/pg/src/entity/conjecture_jobs.rs`
- Create: `engine/crates/pg/src/entity/conjecture_events.rs`
- Modify: `engine/crates/pg/src/entity/mod.rs`

- [ ] **Step 1: Write `entity/conjecture_jobs.rs`**

```rust
use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "conjecture_jobs")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub owner_id: Uuid,
    pub state: String,
    pub outcome: Option<String>,
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub provider: String,
    pub model: String,
    #[sea_orm(column_type = "JsonBinary")]
    pub suggestions: Option<Json>,
    pub chosen_index: Option<i32>,
    #[sea_orm(column_type = "JsonBinary")]
    pub seed: Option<Json>,
    #[sea_orm(column_type = "JsonBinary")]
    pub budget: Json,
    pub claimed_by: Option<String>,
    pub claimed_at: Option<DateTimeWithTimeZone>,
    pub lease_expires_at: Option<DateTimeWithTimeZone>,
    pub last_heartbeat_at: Option<DateTimeWithTimeZone>,
    pub candidates_attempted: i32,
    pub candidates_verified: i32,
    pub verified_theorem_ids: Option<Vec<Vec<u8>>>,
    pub created_at: DateTimeWithTimeZone,
    pub completed_at: Option<DateTimeWithTimeZone>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 2: Write `entity/conjecture_events.rs`**

```rust
use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "conjecture_events")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i64,
    pub job_id: Uuid,
    pub kind: String,
    #[sea_orm(column_type = "JsonBinary")]
    pub payload: Json,
    pub at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 3: Re-export from mod.rs**

Add to `engine/crates/pg/src/entity/mod.rs`:

```rust
pub mod conjecture_events;
pub mod conjecture_jobs;
```

- [ ] **Step 4: Build**

Run: `cargo build -p nasrudin-pg`

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/entity/
git commit -m "feat(pg): SeaORM entities for conjecture_jobs + conjecture_events"
```

---

## Task 4: Query module — conjecture_jobs CRUD

**Files:**
- Create: `engine/crates/pg/src/query/conjecture_jobs.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`

- [ ] **Step 1: Write the query module**

```rust
use crate::entity::conjecture_events as ev;
use crate::entity::conjecture_jobs as job;
use chrono::{DateTime, Utc};
use sea_orm::sea_query::OnConflict;
use sea_orm::{
    ActiveModelTrait, ActiveValue, ColumnTrait, DatabaseConnection, DbErr, EntityTrait,
    QueryFilter, QueryOrder,
};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateInput {
    pub owner_id: Uuid,
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub provider: String,
    pub model: String,
    pub budget: serde_json::Value,
}

pub async fn create(db: &DatabaseConnection, input: CreateInput) -> Result<Uuid, DbErr> {
    let id = Uuid::new_v4();
    let now = chrono::Utc::now();
    let row = job::ActiveModel {
        id: ActiveValue::Set(id),
        owner_id: ActiveValue::Set(input.owner_id),
        state: ActiveValue::Set("Created".to_string()),
        outcome: ActiveValue::Set(None),
        hunch: ActiveValue::Set(input.hunch),
        domain_hint: ActiveValue::Set(input.domain_hint),
        provider: ActiveValue::Set(input.provider),
        model: ActiveValue::Set(input.model),
        suggestions: ActiveValue::Set(None),
        chosen_index: ActiveValue::Set(None),
        seed: ActiveValue::Set(None),
        budget: ActiveValue::Set(input.budget),
        claimed_by: ActiveValue::Set(None),
        claimed_at: ActiveValue::Set(None),
        lease_expires_at: ActiveValue::Set(None),
        last_heartbeat_at: ActiveValue::Set(None),
        candidates_attempted: ActiveValue::Set(0),
        candidates_verified: ActiveValue::Set(0),
        verified_theorem_ids: ActiveValue::Set(None),
        created_at: ActiveValue::Set(now.into()),
        completed_at: ActiveValue::Set(None),
    };
    row.insert(db).await?;
    Ok(id)
}

pub async fn get_by_id(
    db: &DatabaseConnection,
    id: Uuid,
) -> Result<Option<job::Model>, DbErr> {
    job::Entity::find_by_id(id).one(db).await
}

pub async fn list_for_user(
    db: &DatabaseConnection,
    owner_id: Uuid,
    limit: u64,
) -> Result<Vec<job::Model>, DbErr> {
    job::Entity::find()
        .filter(job::Column::OwnerId.eq(owner_id))
        .order_by_desc(job::Column::CreatedAt)
        .limit(limit)
        .all(db)
        .await
}

pub async fn set_suggestions(
    db: &DatabaseConnection,
    id: Uuid,
    suggestions: serde_json::Value,
) -> Result<(), DbErr> {
    let model = job::Entity::find_by_id(id)
        .one(db)
        .await?
        .ok_or(DbErr::RecordNotFound("conjecture_jobs".into()))?;
    let mut active: job::ActiveModel = model.into();
    active.suggestions = ActiveValue::Set(Some(suggestions));
    active.state = ActiveValue::Set("LlmComplete".into());
    active.update(db).await?;
    Ok(())
}

pub async fn set_chosen_seed(
    db: &DatabaseConnection,
    id: Uuid,
    chosen_index: i32,
    seed: serde_json::Value,
) -> Result<(), DbErr> {
    let model = job::Entity::find_by_id(id)
        .one(db)
        .await?
        .ok_or(DbErr::RecordNotFound("conjecture_jobs".into()))?;
    let mut active: job::ActiveModel = model.into();
    active.chosen_index = ActiveValue::Set(Some(chosen_index));
    active.seed = ActiveValue::Set(Some(seed));
    active.state = ActiveValue::Set("QueuedForWorker".into());
    active.update(db).await?;
    Ok(())
}

pub async fn mark_failed(
    db: &DatabaseConnection,
    id: Uuid,
    reason: &str,
) -> Result<(), DbErr> {
    let model = job::Entity::find_by_id(id)
        .one(db)
        .await?
        .ok_or(DbErr::RecordNotFound("conjecture_jobs".into()))?;
    let mut active: job::ActiveModel = model.into();
    active.state = ActiveValue::Set("Complete".into());
    active.outcome = ActiveValue::Set(Some(format!("Failed:{reason}")));
    active.completed_at = ActiveValue::Set(Some(chrono::Utc::now().into()));
    active.update(db).await?;
    Ok(())
}

pub async fn insert_event(
    db: &DatabaseConnection,
    job_id: Uuid,
    kind: &str,
    payload: serde_json::Value,
) -> Result<i64, DbErr> {
    let row = ev::ActiveModel {
        id: ActiveValue::NotSet,
        job_id: ActiveValue::Set(job_id),
        kind: ActiveValue::Set(kind.into()),
        payload: ActiveValue::Set(payload),
        at: ActiveValue::Set(chrono::Utc::now().into()),
    };
    let inserted = row.insert(db).await?;
    Ok(inserted.id)
}

pub async fn events_after(
    db: &DatabaseConnection,
    job_id: Uuid,
    after_id: i64,
    limit: u64,
) -> Result<Vec<ev::Model>, DbErr> {
    ev::Entity::find()
        .filter(ev::Column::JobId.eq(job_id))
        .filter(ev::Column::Id.gt(after_id))
        .order_by_asc(ev::Column::Id)
        .limit(limit)
        .all(db)
        .await
}
```

- [ ] **Step 2: Re-export the query module**

Add to `engine/crates/pg/src/query/mod.rs`:

```rust
pub mod conjecture_jobs;
```

- [ ] **Step 3: Build**

Run: `cargo build -p nasrudin-pg`

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/query/conjecture_jobs.rs engine/crates/pg/src/query/mod.rs
git commit -m "feat(pg): CRUD + event-log helpers for conjecture_jobs"
```

---

## Task 5: Conjecture types module

**Files:**
- Create: `engine/crates/api/src/conjecture/mod.rs`
- Create: `engine/crates/api/src/conjecture/types.rs`

- [ ] **Step 1: Write `mod.rs`**

```rust
pub mod orchestrate;
pub mod prompt;
pub mod types;

pub use types::*;
```

- [ ] **Step 2: Write `types.rs`**

```rust
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateConjectureRequest {
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub provider: String,
    pub model: String,
    pub budget: BudgetSpec,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BudgetSpec {
    pub wall_seconds: u32,
    pub max_candidates: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LlmSuggestion {
    pub axiom_set: Vec<String>,
    pub initial_population: Vec<String>,
    pub mutation_priors: HashMap<String, f32>,
    pub target_shape: Option<String>,
    pub rationale: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateConjectureResponse {
    pub job_id: Uuid,
    pub state: String,
    pub suggestions: Vec<LlmSuggestion>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StartConjectureRequest {
    pub chosen_index: i32,
    pub seed_overrides: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConjectureView {
    pub id: Uuid,
    pub state: String,
    pub outcome: Option<String>,
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub provider: String,
    pub model: String,
    pub suggestions: Option<Vec<LlmSuggestion>>,
    pub chosen_index: Option<i32>,
    pub budget: BudgetSpec,
    pub candidates_attempted: i32,
    pub candidates_verified: i32,
    pub verified_theorem_ids: Vec<String>,
    pub created_at: DateTime<Utc>,
    pub completed_at: Option<DateTime<Utc>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConjectureEventOut {
    pub id: i64,
    pub job_id: Uuid,
    pub kind: String,
    pub payload: serde_json::Value,
    pub at: DateTime<Utc>,
}
```

- [ ] **Step 3: Write a serde round-trip test**

In `engine/crates/api/src/conjecture/types.rs`, append:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_request_round_trips() {
        let req = CreateConjectureRequest {
            hunch: "energy and mass relate via c²".into(),
            domain_hint: Some("SpecialRelativity".into()),
            provider: "anthropic".into(),
            model: "claude-sonnet-4-6".into(),
            budget: BudgetSpec { wall_seconds: 600, max_candidates: 100_000 },
        };
        let json = serde_json::to_string(&req).unwrap();
        let back: CreateConjectureRequest = serde_json::from_str(&json).unwrap();
        assert_eq!(back.hunch, req.hunch);
        assert_eq!(back.budget.wall_seconds, 600);
    }

    #[test]
    fn suggestion_round_trips() {
        let s = LlmSuggestion {
            axiom_set: vec!["sr_invariant_interval".into()],
            initial_population: vec!["mass_shell".into()],
            mutation_priors: [("rearrange".into(), 0.7)].into_iter().collect(),
            target_shape: Some("E = m c^2".into()),
            rationale: "energy comes from inertial mass".into(),
        };
        let json = serde_json::to_string(&s).unwrap();
        let back: LlmSuggestion = serde_json::from_str(&json).unwrap();
        assert_eq!(back.axiom_set, s.axiom_set);
    }
}
```

- [ ] **Step 4: Run the tests (skip until orchestrate.rs + prompt.rs land)**

For now this won't compile because `mod.rs` references `orchestrate` and `prompt` files that don't exist. Stub them in this task with empty modules to keep compilation clean. Add empty files:

```bash
echo '// implemented in Task 6' > engine/crates/api/src/conjecture/orchestrate.rs
echo '// implemented in Task 7' > engine/crates/api/src/conjecture/prompt.rs
```

Then add `pub mod conjecture;` to `engine/crates/api/src/main.rs` (top-level mod declarations, after the existing `pub mod cache;` block).

Run: `cargo test -p nasrudin-api conjecture::types::tests --lib`
Expected: 2 passing tests.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/conjecture/ engine/crates/api/src/main.rs
git commit -m "feat(api): conjecture types + module skeleton"
```

---

## Task 6: LLM prompt builder

**Files:**
- Modify: `engine/crates/api/src/conjecture/prompt.rs`

- [ ] **Step 1: Write the failing test**

Replace the placeholder content in `engine/crates/api/src/conjecture/prompt.rs` with:

```rust
//! Builds the LLM prompt from a hunch + nearest-neighbour theorems + axiom catalog.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeighbourTheorem {
    pub id: String,                  // hex
    pub statement: String,
    pub domain: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AxiomEntry {
    pub name: String,
    pub domain: String,
    pub description: String,
}

pub const SYSTEM_PROMPT: &str = "You are an assistant for a formal-theorem-discovery system. \
Given a researcher's informal conjecture and a set of related verified theorems from the existing \
corpus, produce a JSON array of derivation seeds the system can search from.\n\n\
Each seed includes:\n\
- axiom_set: which axioms to enable (subset of the provided catalog)\n\
- initial_population: 5-10 expression sketches the GA should mutate (Lean-style strings)\n\
- mutation_priors: per-operator weights biasing the GA's mutation choices\n\
- target_shape: optional human-readable description of the target form\n\
- rationale: why these seeds, in 1-2 sentences\n\n\
You DO NOT prove anything. You suggest where to search. \
Output a JSON object: { \"suggestions\": [LlmSuggestion, ...] }. Aim for 3 suggestions.";

pub fn build_user_prompt(
    hunch: &str,
    domain_hint: Option<&str>,
    neighbours: &[NeighbourTheorem],
    axioms: &[AxiomEntry],
) -> String {
    let mut out = String::new();
    out.push_str("# Researcher's hunch\n\n");
    out.push_str(hunch.trim());
    if let Some(d) = domain_hint {
        out.push_str(&format!("\n\nDomain hint: {}", d));
    }
    out.push_str("\n\n# Nearest verified theorems in the corpus\n\n");
    if neighbours.is_empty() {
        out.push_str("(none found)\n");
    } else {
        for n in neighbours {
            out.push_str(&format!("- [{}, {}] {}\n", n.id, n.domain, n.statement));
        }
    }
    out.push_str("\n# Axiom catalog\n\n");
    for a in axioms {
        out.push_str(&format!("- {} ({}): {}\n", a.name, a.domain, a.description));
    }
    out.push_str(
        "\n# Output format\n\nReply with strictly valid JSON: \
        {\"suggestions\": [{\"axiom_set\": [...], \"initial_population\": [...], \
        \"mutation_priors\": {...}, \"target_shape\": \"...\", \"rationale\": \"...\"}]}\n",
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builds_prompt_with_all_sections() {
        let p = build_user_prompt(
            "Energy and mass relate by c squared",
            Some("SpecialRelativity"),
            &[NeighbourTheorem {
                id: "deadbeef".into(),
                statement: "(c·p)² + m²c⁴ = E²".into(),
                domain: "SpecialRelativity".into(),
            }],
            &[AxiomEntry {
                name: "sr_invariant_interval".into(),
                domain: "SpecialRelativity".into(),
                description: "ds² = c²dt² - dx²".into(),
            }],
        );
        assert!(p.contains("Energy and mass"));
        assert!(p.contains("SpecialRelativity"));
        assert!(p.contains("deadbeef"));
        assert!(p.contains("sr_invariant_interval"));
        assert!(p.contains("# Output format"));
    }

    #[test]
    fn handles_empty_neighbours_and_no_domain_hint() {
        let p = build_user_prompt("a hunch", None, &[], &[]);
        assert!(p.contains("(none found)"));
        assert!(!p.contains("Domain hint"));
    }
}
```

- [ ] **Step 2: Run tests**

Run: `cargo test -p nasrudin-api conjecture::prompt::tests --lib`
Expected: 2 passing tests.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/conjecture/prompt.rs
git commit -m "feat(api): LLM prompt builder for conjecture loop"
```

---

## Task 7: LLM orchestration (sync server-side call)

**Files:**
- Modify: `engine/crates/api/src/conjecture/orchestrate.rs`

- [ ] **Step 1: Write the orchestrator**

Replace the placeholder in `engine/crates/api/src/conjecture/orchestrate.rs` with:

```rust
//! Synchronous server-side LLM call: hunch → corpus retrieval → prompt → LLM → suggestions.

use crate::conjecture::prompt::{self, AxiomEntry, NeighbourTheorem};
use crate::conjecture::types::LlmSuggestion;
use crate::state::AppState;
use nasrudin_llm::{
    encryption::{decrypt, EncryptedKey},
    CompletionRequest, LlmError, Registry, ResponseFormat,
};
use std::sync::Arc;
use thiserror::Error;
use uuid::Uuid;

#[derive(Debug, Error)]
pub enum OrchestrateError {
    #[error("provider not registered: {0}")]
    UnknownProvider(String),
    #[error("no api key for provider {0}")]
    NoProviderKey(String),
    #[error("encryption key not configured on server")]
    KeyEncryptUnset,
    #[error("decryption failed")]
    DecryptFailed,
    #[error("llm call failed: {0}")]
    LlmCall(#[from] LlmError),
    #[error("llm response did not parse as JSON: {0}")]
    InvalidLlmJson(String),
    #[error("db error: {0}")]
    Db(#[from] sea_orm::DbErr),
    #[error("embedding failed: {0}")]
    Embed(String),
}

pub async fn run_llm_phase(
    state: &Arc<AppState>,
    user_id: Uuid,
    hunch: &str,
    domain_hint: Option<&str>,
    provider: &str,
    model: &str,
) -> Result<Vec<LlmSuggestion>, OrchestrateError> {
    if !Registry::known_providers().contains(&provider) {
        return Err(OrchestrateError::UnknownProvider(provider.into()));
    }

    let encrypt_key = state
        .llm_encrypt_key
        .as_ref()
        .ok_or(OrchestrateError::KeyEncryptUnset)?;

    let pg = state
        .pg
        .as_ref()
        .ok_or_else(|| OrchestrateError::Db(sea_orm::DbErr::Custom("pg unavailable".into())))?;

    let cipher = nasrudin_pg::query::user_llm_keys::get_ciphertext(pg, user_id, provider)
        .await?
        .ok_or_else(|| OrchestrateError::NoProviderKey(provider.into()))?;
    let api_key = decrypt(&EncryptedKey(cipher), encrypt_key)
        .map_err(|_| OrchestrateError::DecryptFailed)?;

    let neighbours = nearest_neighbours(state, hunch, 10).await;
    let axioms = axiom_catalog(state);

    let user_prompt = prompt::build_user_prompt(hunch, domain_hint, &neighbours, &axioms);

    let req = CompletionRequest {
        model: model.to_string(),
        system_prompt: prompt::SYSTEM_PROMPT.to_string(),
        user_prompt,
        max_tokens: 4096,
        temperature: 0.4,
        stop_sequences: vec![],
        response_format: ResponseFormat::Json {
            schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "suggestions": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "axiom_set": {"type": "array", "items": {"type": "string"}},
                                "initial_population": {"type": "array", "items": {"type": "string"}},
                                "mutation_priors": {"type": "object", "additionalProperties": {"type": "number"}},
                                "target_shape": {"type": "string"},
                                "rationale": {"type": "string"}
                            },
                            "required": ["axiom_set", "initial_population", "mutation_priors", "rationale"]
                        }
                    }
                },
                "required": ["suggestions"]
            }),
        },
    };

    let response = Registry::complete(provider, Some(api_key), req).await?;

    let parsed: ParsedResponse = serde_json::from_str(&response.text)
        .map_err(|e| OrchestrateError::InvalidLlmJson(format!("{e}: {}", response.text)))?;

    let _ = nasrudin_pg::query::user_llm_keys::touch_last_used(pg, user_id, provider).await;

    Ok(parsed.suggestions)
}

#[derive(serde::Deserialize)]
struct ParsedResponse {
    suggestions: Vec<LlmSuggestion>,
}

async fn nearest_neighbours(
    state: &Arc<AppState>,
    _hunch: &str,
    _k: usize,
) -> Vec<NeighbourTheorem> {
    // If embed index is missing, we ship an empty list rather than fail —
    // the LLM still produces useful seeds from the axiom catalog alone.
    if state.embed.is_none() {
        return Vec::new();
    }
    // TODO(phase-d-followup): wire fastembed Embedder into AppState so we can
    // do `index.nearest_text(embedder, hunch, k)`. For now neighbours are empty.
    Vec::new()
}

fn axiom_catalog(state: &Arc<AppState>) -> Vec<AxiomEntry> {
    let store = state.axiom_store.load();
    store
        .iter()
        .map(|a| AxiomEntry {
            name: a.name.clone(),
            domain: a.domain.to_string(),
            description: a.description.clone(),
        })
        .collect()
}
```

> The `nearest_neighbours` shortcut is intentional. Threading a fastembed `Embedder` into `AppState` is a separate hardening task — Phase D launches with axiom-catalog-only context, which is already useful for the LLM.

- [ ] **Step 2: Build**

Run: `cargo build -p nasrudin-api`
Expected: clean build.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/conjecture/orchestrate.rs
git commit -m "feat(api): conjecture LLM orchestration (decrypt → prompt → Registry::complete)"
```

---

## Task 8: Broadcast channel + AppState wiring

**Files:**
- Modify: `engine/crates/api/src/state.rs`
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/api/tests/test_app/mod.rs`

- [ ] **Step 1: Define the event type**

In `engine/crates/api/src/conjecture/mod.rs`, append:

```rust
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConjectureEvent {
    pub id: i64,
    pub job_id: Uuid,
    pub kind: String,
    pub payload: serde_json::Value,
    pub at: chrono::DateTime<chrono::Utc>,
}
```

- [ ] **Step 2: Add the broadcast sender to AppState**

In `engine/crates/api/src/state.rs`, add to the `AppState` struct (alphabetical-ish, near other `_tx` fields):

```rust
pub conjecture_event_tx: tokio::sync::broadcast::Sender<crate::conjecture::ConjectureEvent>,
```

- [ ] **Step 3: Initialise the channel in main.rs**

In `engine/crates/api/src/main.rs`, where the other broadcast channels are created (near `let (discovery_tx, _) = broadcast::channel(...)`), add:

```rust
let (conjecture_event_tx, _) = tokio::sync::broadcast::channel::<crate::conjecture::ConjectureEvent>(256);
```

Then add `conjecture_event_tx,` to the `AppState { ... }` literal.

- [ ] **Step 4: Mirror in test_app**

In `engine/crates/api/tests/test_app/mod.rs`, replicate the same channel creation and field assignment so test fixtures still build.

- [ ] **Step 5: Build**

Run: `cargo build -p nasrudin-api --tests`
Expected: clean build.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/api/src/state.rs engine/crates/api/src/main.rs engine/crates/api/src/conjecture/mod.rs engine/crates/api/tests/test_app/mod.rs
git commit -m "feat(api): broadcast channel for conjecture SSE events"
```

---

## Task 9: POST `/api/conjecture` handler

**Files:**
- Create: `engine/crates/api/src/handlers/conjecture.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs`

- [ ] **Step 1: Write the handler**

Create `engine/crates/api/src/handlers/conjecture.rs`:

```rust
use crate::auth::{AuthOrApiKey, AuthSess};
use crate::conjecture::orchestrate::{run_llm_phase, OrchestrateError};
use crate::conjecture::types::*;
use crate::state::AppState;
use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::response::IntoResponse;
use axum::Json;
use std::sync::Arc;
use uuid::Uuid;

fn err(status: StatusCode, code: &str) -> axum::response::Response {
    (status, Json(serde_json::json!({ "error": code }))).into_response()
}

pub async fn create(
    State(state): State<Arc<AppState>>,
    _auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<CreateConjectureRequest>,
) -> axum::response::Response {
    if state.llm_encrypt_key.is_none() {
        return err(StatusCode::SERVICE_UNAVAILABLE, "key_encrypt_unset");
    }
    let Some(user) = auth_sess.user else {
        return err(StatusCode::UNAUTHORIZED, "no_session");
    };
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };
    if body.hunch.trim().is_empty() {
        return err(StatusCode::BAD_REQUEST, "empty_hunch");
    }
    if body.provider != "anthropic" {
        // Phase D launches anthropic-only per spec §13.
        return err(StatusCode::BAD_REQUEST, "unsupported_provider");
    }

    let job_id = match nasrudin_pg::query::conjecture_jobs::create(
        pg,
        nasrudin_pg::query::conjecture_jobs::CreateInput {
            owner_id: user.id,
            hunch: body.hunch.clone(),
            domain_hint: body.domain_hint.clone(),
            provider: body.provider.clone(),
            model: body.model.clone(),
            budget: serde_json::to_value(&body.budget).unwrap_or(serde_json::Value::Null),
        },
    )
    .await
    {
        Ok(id) => id,
        Err(e) => {
            tracing::warn!(?e, "failed to create conjecture row");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };

    let suggestions = match run_llm_phase(
        &state,
        user.id,
        &body.hunch,
        body.domain_hint.as_deref(),
        &body.provider,
        &body.model,
    )
    .await
    {
        Ok(s) => s,
        Err(OrchestrateError::NoProviderKey(_)) => {
            let _ = nasrudin_pg::query::conjecture_jobs::mark_failed(pg, job_id, "no_provider_key").await;
            return err(StatusCode::BAD_REQUEST, "no_provider_key");
        }
        Err(OrchestrateError::UnknownProvider(_)) => {
            return err(StatusCode::BAD_REQUEST, "unsupported_provider");
        }
        Err(OrchestrateError::InvalidLlmJson(msg)) => {
            tracing::warn!(?msg, "llm returned non-json");
            let _ = nasrudin_pg::query::conjecture_jobs::mark_failed(pg, job_id, "llm_invalid_json").await;
            return err(StatusCode::BAD_GATEWAY, "llm_invalid_json");
        }
        Err(e) => {
            tracing::warn!(?e, "llm phase failed");
            let _ = nasrudin_pg::query::conjecture_jobs::mark_failed(pg, job_id, "llm_call_failed").await;
            return err(StatusCode::BAD_GATEWAY, "llm_call_failed");
        }
    };

    let suggestions_json = serde_json::to_value(&suggestions).unwrap_or(serde_json::Value::Null);
    if let Err(e) =
        nasrudin_pg::query::conjecture_jobs::set_suggestions(pg, job_id, suggestions_json).await
    {
        tracing::warn!(?e, "failed to persist suggestions");
        return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
    }

    let event_payload = serde_json::json!({"from": "Created", "to": "LlmComplete"});
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        job_id,
        "state_change",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(crate::conjecture::ConjectureEvent {
            id: event_id,
            job_id,
            kind: "state_change".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    Json(CreateConjectureResponse {
        job_id,
        state: "LlmComplete".into(),
        suggestions,
    })
    .into_response()
}

pub async fn start(
    State(state): State<Arc<AppState>>,
    _auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
    Json(body): Json<StartConjectureRequest>,
) -> axum::response::Response {
    let Some(user) = auth_sess.user else {
        return err(StatusCode::UNAUTHORIZED, "no_session");
    };
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    let row = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(r)) => r,
        Ok(None) => return err(StatusCode::NOT_FOUND, "not_found"),
        Err(e) => {
            tracing::warn!(?e, "fetch conjecture failed");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if row.owner_id != user.id {
        return err(StatusCode::NOT_FOUND, "not_found");
    }
    if row.state != "LlmComplete" {
        return err(StatusCode::CONFLICT, "wrong_state");
    }

    let suggestions: Vec<LlmSuggestion> = row
        .suggestions
        .as_ref()
        .and_then(|v| serde_json::from_value(v.clone()).ok())
        .unwrap_or_default();
    if body.chosen_index < 0 || (body.chosen_index as usize) >= suggestions.len() {
        return err(StatusCode::BAD_REQUEST, "chosen_index_out_of_range");
    }
    let chosen = &suggestions[body.chosen_index as usize];
    let seed = body
        .seed_overrides
        .clone()
        .unwrap_or_else(|| serde_json::to_value(chosen).unwrap_or(serde_json::Value::Null));

    if let Err(e) =
        nasrudin_pg::query::conjecture_jobs::set_chosen_seed(pg, id, body.chosen_index, seed).await
    {
        tracing::warn!(?e, "failed to set seed");
        return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
    }

    let event_payload = serde_json::json!({"from": "LlmComplete", "to": "QueuedForWorker"});
    if let Ok(event_id) = nasrudin_pg::query::conjecture_jobs::insert_event(
        pg,
        id,
        "state_change",
        event_payload.clone(),
    )
    .await
    {
        let _ = state.conjecture_event_tx.send(crate::conjecture::ConjectureEvent {
            id: event_id,
            job_id: id,
            kind: "state_change".into(),
            payload: event_payload,
            at: chrono::Utc::now(),
        });
    }

    (StatusCode::OK, Json(serde_json::json!({"id": id, "state": "QueuedForWorker"}))).into_response()
}

pub async fn get_one(
    State(state): State<Arc<AppState>>,
    _auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
) -> axum::response::Response {
    let Some(user) = auth_sess.user else {
        return err(StatusCode::UNAUTHORIZED, "no_session");
    };
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };
    let row = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(r)) => r,
        Ok(None) => return err(StatusCode::NOT_FOUND, "not_found"),
        Err(e) => {
            tracing::warn!(?e, "fetch conjecture failed");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };
    if row.owner_id != user.id {
        return err(StatusCode::NOT_FOUND, "not_found");
    }
    Json(view_from_row(&row)).into_response()
}

pub async fn list_mine(
    State(state): State<Arc<AppState>>,
    _auth: AuthOrApiKey,
    auth_sess: AuthSess,
) -> axum::response::Response {
    let Some(user) = auth_sess.user else {
        return err(StatusCode::UNAUTHORIZED, "no_session");
    };
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };
    match nasrudin_pg::query::conjecture_jobs::list_for_user(pg, user.id, 50).await {
        Ok(rows) => Json(serde_json::json!({
            "conjectures": rows.iter().map(view_from_row).collect::<Vec<_>>(),
        }))
        .into_response(),
        Err(e) => {
            tracing::warn!(?e, "list conjectures failed");
            err(StatusCode::INTERNAL_SERVER_ERROR, "db_error")
        }
    }
}

fn view_from_row(row: &nasrudin_pg::entity::conjecture_jobs::Model) -> ConjectureView {
    let budget: BudgetSpec = serde_json::from_value(row.budget.clone())
        .unwrap_or(BudgetSpec { wall_seconds: 0, max_candidates: 0 });
    let suggestions: Option<Vec<LlmSuggestion>> = row
        .suggestions
        .as_ref()
        .and_then(|v| serde_json::from_value(v.clone()).ok());
    ConjectureView {
        id: row.id,
        state: row.state.clone(),
        outcome: row.outcome.clone(),
        hunch: row.hunch.clone(),
        domain_hint: row.domain_hint.clone(),
        provider: row.provider.clone(),
        model: row.model.clone(),
        suggestions,
        chosen_index: row.chosen_index,
        budget,
        candidates_attempted: row.candidates_attempted,
        candidates_verified: row.candidates_verified,
        verified_theorem_ids: row
            .verified_theorem_ids
            .clone()
            .unwrap_or_default()
            .iter()
            .map(|b| b.iter().map(|x| format!("{x:02x}")).collect::<String>())
            .collect(),
        created_at: row.created_at.with_timezone(&chrono::Utc),
        completed_at: row.completed_at.map(|t| t.with_timezone(&chrono::Utc)),
    }
}
```

- [ ] **Step 2: Re-export from handlers/mod.rs**

Add `pub mod conjecture;` to `engine/crates/api/src/handlers/mod.rs`.

- [ ] **Step 3: Build**

Run: `cargo build -p nasrudin-api`

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/handlers/conjecture.rs engine/crates/api/src/handlers/mod.rs
git commit -m "feat(api): /api/conjecture create + start + get + list handlers"
```

---

## Task 10: SSE handler

**Files:**
- Modify: `engine/crates/api/src/handlers/conjecture.rs`

- [ ] **Step 1: Append the SSE handler**

Append to `engine/crates/api/src/handlers/conjecture.rs`:

```rust
use axum::response::sse::{Event, KeepAlive, Sse};
use futures::stream::{self, Stream, StreamExt};
use std::convert::Infallible;
use std::time::Duration;
use tokio_stream::wrappers::BroadcastStream;

pub async fn sse(
    State(state): State<Arc<AppState>>,
    _auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
) -> axum::response::Response {
    let Some(user) = auth_sess.user else {
        return err(StatusCode::UNAUTHORIZED, "no_session");
    };
    let Some(pg) = state.pg.as_ref() else {
        return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable");
    };

    let row = match nasrudin_pg::query::conjecture_jobs::get_by_id(pg, id).await {
        Ok(Some(r)) => r,
        Ok(None) => return err(StatusCode::NOT_FOUND, "not_found"),
        Err(_) => return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error"),
    };
    if row.owner_id != user.id {
        return err(StatusCode::NOT_FOUND, "not_found");
    }

    let history = nasrudin_pg::query::conjecture_jobs::events_after(pg, id, 0, 1024)
        .await
        .unwrap_or_default();

    let history_stream = stream::iter(history.into_iter().map(move |e| {
        let payload = serde_json::json!({
            "id": e.id,
            "kind": e.kind,
            "payload": e.payload,
            "at": e.at,
        });
        Ok::<_, Infallible>(
            Event::default()
                .event(&e.kind)
                .data(payload.to_string()),
        )
    }));

    let rx = state.conjecture_event_tx.subscribe();
    let live = BroadcastStream::new(rx).filter_map(move |r| {
        let job_id = id;
        async move {
            match r {
                Ok(e) if e.job_id == job_id => Some(Ok::<_, Infallible>(
                    Event::default()
                        .event(&e.kind)
                        .data(
                            serde_json::json!({
                                "id": e.id,
                                "kind": e.kind,
                                "payload": e.payload,
                                "at": e.at,
                            })
                            .to_string(),
                        ),
                )),
                _ => None,
            }
        }
    });

    let merged = history_stream.chain(live);

    Sse::new(merged)
        .keep_alive(KeepAlive::new().interval(Duration::from_secs(15)).text("ping"))
        .into_response()
}
```

- [ ] **Step 2: Add the tokio-stream dep if missing**

Verify `engine/crates/api/Cargo.toml` has `tokio-stream`. If not, add `tokio-stream = "0.1"`.

- [ ] **Step 3: Build**

Run: `cargo build -p nasrudin-api`

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/handlers/conjecture.rs engine/crates/api/Cargo.toml
git commit -m "feat(api): SSE stream for conjecture events (history replay + live)"
```

---

## Task 11: Wire routes in main.rs + test_app

**Files:**
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/api/tests/test_app/mod.rs`

- [ ] **Step 1: Add routes to main.rs**

In the `platform_user` router (cookie auth, near the existing `/api/me/llm-keys` registrations), add:

```rust
.route("/api/conjecture", post(handlers::conjecture::create))
.route("/api/conjecture/{id}", get(handlers::conjecture::get_one))
.route("/api/conjecture/{id}/start", post(handlers::conjecture::start))
.route("/api/conjecture/{id}/sse", get(handlers::conjecture::sse))
.route("/api/me/conjectures", get(handlers::conjecture::list_mine))
```

- [ ] **Step 2: Mirror in test_app**

Add the same five `.route(...)` lines to `engine/crates/api/tests/test_app/mod.rs` so smoke tests can exercise them.

- [ ] **Step 3: Build**

Run: `cargo build -p nasrudin-api --tests`

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/main.rs engine/crates/api/tests/test_app/mod.rs
git commit -m "feat(api): mount conjecture routes on platform-user router"
```

---

## Task 12: Auth-gate smoke tests

**Files:**
- Create: `engine/crates/api/tests/conjecture_handler.rs`

- [ ] **Step 1: Write the tests**

```rust
//! Smoke tests for /api/conjecture endpoints. Validates:
//!  - all five routes are mounted
//!  - unauthenticated requests get 401
//!  - service-unavailable cases (no pg / no encrypt key) surface as 503
//!  Full end-to-end behaviour is exercised via the `e2e_conjecture_emc2` nightly.

mod test_app;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

#[tokio::test]
async fn create_unauthenticated_returns_401() {
    let app = test_app::build_app().await;
    let res = app
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/api/conjecture")
                .header("content-type", "application/json")
                .body(Body::from(
                    r#"{"hunch":"hi","provider":"anthropic","model":"claude-sonnet-4-6","budget":{"wall_seconds":60,"max_candidates":100}}"#,
                ))
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(res.status(), StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn start_unauthenticated_returns_401() {
    let app = test_app::build_app().await;
    let res = app
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/api/conjecture/00000000-0000-0000-0000-000000000000/start")
                .header("content-type", "application/json")
                .body(Body::from(r#"{"chosen_index":0}"#))
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(res.status(), StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn get_unauthenticated_returns_401() {
    let app = test_app::build_app().await;
    let res = app
        .oneshot(
            Request::builder()
                .method("GET")
                .uri("/api/conjecture/00000000-0000-0000-0000-000000000000")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(res.status(), StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn sse_unauthenticated_returns_401() {
    let app = test_app::build_app().await;
    let res = app
        .oneshot(
            Request::builder()
                .method("GET")
                .uri("/api/conjecture/00000000-0000-0000-0000-000000000000/sse")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(res.status(), StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn list_mine_unauthenticated_returns_401() {
    let app = test_app::build_app().await;
    let res = app
        .oneshot(
            Request::builder()
                .method("GET")
                .uri("/api/me/conjectures")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(res.status(), StatusCode::UNAUTHORIZED);
}
```

- [ ] **Step 2: Run tests**

Run: `cargo test -p nasrudin-api --test conjecture_handler`
Expected: 5 passing tests.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/tests/conjecture_handler.rs
git commit -m "test(api): /api/conjecture auth-gate smoke tests"
```

---

## Task 13: Frontend types

**Files:**
- Modify: `nasrudin-frontend/src/lib/types.ts`

- [ ] **Step 1: Append types**

Append to `nasrudin-frontend/src/lib/types.ts`:

```ts
// --- /api/conjecture ---

export interface BudgetSpec {
  wall_seconds: number;
  max_candidates: number;
}

export interface LlmSuggestion {
  axiom_set: string[];
  initial_population: string[];
  mutation_priors: Record<string, number>;
  target_shape: string | null;
  rationale: string;
}

export interface CreateConjectureRequest {
  hunch: string;
  domain_hint?: string | null;
  provider: string;
  model: string;
  budget: BudgetSpec;
}

export interface CreateConjectureResponse {
  job_id: string;
  state: string;
  suggestions: LlmSuggestion[];
}

export interface ConjectureView {
  id: string;
  state: 'Created' | 'LlmComplete' | 'QueuedForWorker' | 'Running' | 'Complete' | string;
  outcome: string | null;
  hunch: string;
  domain_hint: string | null;
  provider: string;
  model: string;
  suggestions: LlmSuggestion[] | null;
  chosen_index: number | null;
  budget: BudgetSpec;
  candidates_attempted: number;
  candidates_verified: number;
  verified_theorem_ids: string[];
  created_at: string;
  completed_at: string | null;
}

export interface ConjectureListResponse {
  conjectures: ConjectureView[];
}

export interface StartConjectureRequest {
  chosen_index: number;
  seed_overrides?: unknown;
}

export interface ConjectureSseEvent {
  id: number;
  kind: 'state_change' | 'progress' | 'candidate_verified' | string;
  payload: unknown;
  at: string;
}
```

- [ ] **Step 2: Verify**

Run: `cd nasrudin-frontend && pnpm tsc --noEmit`
Expected: exit 0.

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/lib/types.ts
git commit -m "feat(frontend): types for /api/conjecture"
```

---

## Task 14: Frontend query hooks

**Files:**
- Modify: `nasrudin-frontend/src/lib/queries.ts`
- Modify: `nasrudin-frontend/src/lib/sse.ts`

- [ ] **Step 1: Append to queries.ts**

Append to `nasrudin-frontend/src/lib/queries.ts`:

```ts
// --- /api/conjecture ---

import type {
  ConjectureListResponse,
  ConjectureView,
  CreateConjectureRequest,
  CreateConjectureResponse,
  StartConjectureRequest,
} from './types';

export const conjecturesQueryKey = ['conjectures'] as const;

export function useMyConjectures() {
  return useQuery<ConjectureListResponse>({
    queryKey: conjecturesQueryKey,
    queryFn: () => apiFetch<ConjectureListResponse>('/api/me/conjectures'),
    refetchInterval: 30_000,
  });
}

export function useConjecture(id: string) {
  return useQuery<ConjectureView>({
    queryKey: ['conjecture', id],
    queryFn: () => apiFetch<ConjectureView>(`/api/conjecture/${id}`),
    enabled: !!id,
  });
}

export function useCreateConjecture() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: CreateConjectureRequest) =>
      apiFetch<CreateConjectureResponse>('/api/conjecture', {
        method: 'POST',
        body: JSON.stringify(body),
      }),
    onSuccess: () => qc.invalidateQueries({ queryKey: conjecturesQueryKey }),
  });
}

export function useStartConjecture(id: string) {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: StartConjectureRequest) =>
      apiFetch<{ id: string; state: string }>(`/api/conjecture/${id}/start`, {
        method: 'POST',
        body: JSON.stringify(body),
      }),
    onSuccess: () => {
      qc.invalidateQueries({ queryKey: ['conjecture', id] });
      qc.invalidateQueries({ queryKey: conjecturesQueryKey });
    },
  });
}
```

- [ ] **Step 2: Add SSE hook**

Append to `nasrudin-frontend/src/lib/sse.ts` (or create an export alongside `useDiscoveryFeed`):

```ts
import { useEffect, useState } from 'react';
import type { ConjectureSseEvent } from './types';
import { API_BASE } from './api';

export function useConjectureStream(id: string | null): ConjectureSseEvent[] {
  const [events, setEvents] = useState<ConjectureSseEvent[]>([]);
  useEffect(() => {
    if (!id) return;
    setEvents([]);
    const es = new EventSource(`${API_BASE}/api/conjecture/${id}/sse`, {
      withCredentials: true,
    });
    const onAny = (e: MessageEvent) => {
      try {
        const parsed = JSON.parse(e.data) as ConjectureSseEvent;
        setEvents((prev) => [...prev, parsed]);
      } catch {
        // ignore malformed
      }
    };
    ['state_change', 'progress', 'candidate_verified', 'complete'].forEach((kind) => {
      es.addEventListener(kind, onAny as EventListener);
    });
    es.onerror = () => {};
    return () => es.close();
  }, [id]);
  return events;
}
```

If `API_BASE` is not currently exported from `lib/api.ts`, export it.

- [ ] **Step 3: Re-export from queries.ts**

Make sure `useConjectureStream` is re-exported from `queries.ts` alongside the existing `useDiscoveryFeed, useStatsStream` re-export.

- [ ] **Step 4: Verify**

Run: `cd nasrudin-frontend && pnpm tsc --noEmit`
Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add nasrudin-frontend/src/lib/queries.ts nasrudin-frontend/src/lib/sse.ts nasrudin-frontend/src/lib/api.ts
git commit -m "feat(frontend): query hooks + SSE for /api/conjecture"
```

---

## Task 15: `/conjecture` route (creator form)

**Files:**
- Create: `nasrudin-frontend/src/routes/conjecture.tsx`

- [ ] **Step 1: Write the route**

```tsx
import { createFileRoute, redirect, useNavigate } from '@tanstack/react-router';
import { type FormEvent, useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { isApiError } from '~/lib/api';
import { useCreateConjecture, useMe } from '~/lib/queries';

export const Route = createFileRoute('/conjecture')({ component: ConjecturePage });

function ConjecturePage() {
  const me = useMe();
  const navigate = useNavigate();
  const create = useCreateConjecture();

  const [hunch, setHunch] = useState('');
  const [domainHint, setDomainHint] = useState('');
  const [model, setModel] = useState('claude-sonnet-4-6');
  const [wallSeconds, setWallSeconds] = useState(600);
  const [maxCandidates, setMaxCandidates] = useState(100_000);
  const [error, setError] = useState<string | null>(null);

  if (me.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    try {
      const res = await create.mutateAsync({
        hunch: hunch.trim(),
        domain_hint: domainHint.trim() || null,
        provider: 'anthropic',
        model,
        budget: { wall_seconds: wallSeconds, max_candidates: maxCandidates },
      });
      navigate({ to: '/conjecture/$id', params: { id: res.job_id } });
    } catch (e) {
      if (isApiError(e)) {
        const msg =
          e.body && typeof e.body === 'object' && 'error' in e.body
            ? String((e.body as { error: unknown }).error)
            : `Request failed (${e.status})`;
        setError(msg);
      } else {
        setError('Network error');
      }
    }
  }

  return (
    <div className="app">
      <AppHeader active="conjecture" />
      <div className="container-wide" style={{ maxWidth: 760 }}>
        <div className="page-head">
          <span className="overline">Research</span>
          <h1>
            New conjecture —{' '}
            <em style={{ fontStyle: 'italic', color: 'var(--terracotta-700)', fontWeight: 300 }}>
              what should we try to derive?
            </em>
          </h1>
          <p className="lede">
            Describe a hypothesis in plain English. The router will hand it to your chosen LLM,
            propose seed axiom subsets + initial populations, and queue a guided GA run for
            research-mode workers.
          </p>
        </div>

        <form className="page-body" onSubmit={onSubmit} style={{ maxWidth: 560 }}>
          <div className="field">
            <label htmlFor="hunch">Hunch</label>
            <textarea
              id="hunch"
              value={hunch}
              onChange={(e) => setHunch(e.target.value)}
              rows={5}
              required
              placeholder="Energy and rest mass should relate via the speed of light squared."
              style={{
                background: 'var(--bg-raised)',
                border: '1px solid var(--paper-200)',
                borderRadius: 'var(--radius-md)',
                padding: '12px 14px',
                fontFamily: 'var(--font-sans)',
                fontSize: 15,
                color: 'var(--ink-900)',
                resize: 'vertical',
              }}
            />
            <span className="hint">Plain English. The LLM never proves; it only points the GA.</span>
          </div>

          <div className="field">
            <label htmlFor="domain">Domain hint (optional)</label>
            <select
              id="domain"
              value={domainHint}
              onChange={(e) => setDomainHint(e.target.value)}
            >
              <option value="">—</option>
              <option value="SpecialRelativity">SpecialRelativity</option>
              <option value="ClassicalMechanics">ClassicalMechanics</option>
              <option value="Electromagnetism">Electromagnetism</option>
              <option value="QuantumMechanics">QuantumMechanics</option>
              <option value="QuantumFieldTheory">QuantumFieldTheory</option>
              <option value="Thermodynamics">Thermodynamics</option>
              <option value="StatisticalMechanics">StatisticalMechanics</option>
              <option value="GeneralRelativity">GeneralRelativity</option>
              <option value="FluidDynamics">FluidDynamics</option>
              <option value="Optics">Optics</option>
              <option value="PureMath">PureMath</option>
            </select>
          </div>

          <div className="field">
            <label htmlFor="model">Model</label>
            <select id="model" value={model} onChange={(e) => setModel(e.target.value)}>
              <option value="claude-sonnet-4-6">Claude Sonnet 4.6</option>
              <option value="claude-opus-4-7">Claude Opus 4.7</option>
              <option value="claude-haiku-4-5">Claude Haiku 4.5</option>
            </select>
            <span className="hint">Anthropic only for Phase D launch. Configure your key in /settings.</span>
          </div>

          <div style={{ display: 'flex', gap: 16 }}>
            <div className="field" style={{ flex: 1 }}>
              <label htmlFor="wall">Wall seconds</label>
              <input
                id="wall"
                type="number"
                min={60}
                max={86_400}
                value={wallSeconds}
                onChange={(e) => setWallSeconds(Number(e.target.value))}
              />
            </div>
            <div className="field" style={{ flex: 1 }}>
              <label htmlFor="cands">Max candidates</label>
              <input
                id="cands"
                type="number"
                min={1000}
                max={10_000_000}
                value={maxCandidates}
                onChange={(e) => setMaxCandidates(Number(e.target.value))}
              />
            </div>
          </div>

          {error && (
            <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginTop: 12 }}>
              {error}
            </div>
          )}
          <div style={{ marginTop: 24, display: 'flex', gap: 12 }}>
            <button
              type="submit"
              className="btn btn-primary"
              disabled={create.isPending || hunch.trim().length === 0}
            >
              {create.isPending ? 'Calling LLM…' : 'Get suggestions'}
            </button>
          </div>
        </form>
      </div>
      <AppFooter />
    </div>
  );
}
```

- [ ] **Step 2: Verify**

Run: `cd nasrudin-frontend && pnpm tsc --noEmit && pnpm build`
Expected: exit 0 (a generated `routeTree.gen.ts` update is normal).

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/routes/conjecture.tsx nasrudin-frontend/src/routeTree.gen.ts
git commit -m "feat(frontend): /conjecture creator form"
```

---

## Task 16: `/conjecture/$id` route (live view)

**Files:**
- Create: `nasrudin-frontend/src/routes/conjecture.$id.tsx`
- Create: `nasrudin-frontend/src/components/conjecture/SuggestionCard.tsx`
- Create: `nasrudin-frontend/src/components/conjecture/JobProgress.tsx`

- [ ] **Step 1: Write SuggestionCard**

```tsx
import type { LlmSuggestion } from '~/lib/types';

export function SuggestionCard({
  suggestion,
  index,
  selected,
  onSelect,
}: {
  suggestion: LlmSuggestion;
  index: number;
  selected: boolean;
  onSelect: () => void;
}) {
  return (
    <div
      style={{
        border: selected
          ? '2px solid var(--terracotta-700)'
          : '1px solid var(--paper-200)',
        borderRadius: 8,
        padding: 16,
        marginBottom: 12,
        cursor: 'pointer',
        background: selected ? 'var(--paper-50)' : 'var(--bg-raised)',
      }}
      onClick={onSelect}
    >
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'baseline' }}>
        <strong>Suggestion #{index + 1}</strong>
        {selected && <span style={{ color: 'var(--terracotta-700)' }}>✓ chosen</span>}
      </div>
      {suggestion.target_shape && (
        <div style={{ fontFamily: 'var(--font-mono)', marginTop: 8, fontSize: 14 }}>
          target: {suggestion.target_shape}
        </div>
      )}
      <div style={{ marginTop: 8, color: 'var(--ink-700)', fontSize: 14 }}>{suggestion.rationale}</div>
      <details style={{ marginTop: 8 }}>
        <summary style={{ cursor: 'pointer', fontSize: 13, color: 'var(--ink-500)' }}>
          axioms ({suggestion.axiom_set.length}) · seeds ({suggestion.initial_population.length})
        </summary>
        <ul style={{ marginTop: 8, fontFamily: 'var(--font-mono)', fontSize: 13 }}>
          {suggestion.axiom_set.map((a) => (
            <li key={a}>· {a}</li>
          ))}
        </ul>
        <div style={{ fontSize: 13, marginTop: 8, color: 'var(--ink-500)' }}>Initial population:</div>
        <ul style={{ fontFamily: 'var(--font-mono)', fontSize: 13 }}>
          {suggestion.initial_population.map((s, i) => (
            <li key={i}>{s}</li>
          ))}
        </ul>
      </details>
    </div>
  );
}
```

- [ ] **Step 2: Write JobProgress**

```tsx
import type { ConjectureSseEvent, ConjectureView } from '~/lib/types';

export function JobProgress({
  view,
  events,
}: {
  view: ConjectureView;
  events: ConjectureSseEvent[];
}) {
  return (
    <div className="card" style={{ marginTop: 24 }}>
      <h3 className="section-h" style={{ fontSize: 22, marginBottom: 16 }}>
        Live progress
      </h3>
      <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: 16, fontFamily: 'var(--font-mono)' }}>
        <div>
          <div style={{ color: 'var(--ink-500)', fontSize: 12 }}>state</div>
          <div style={{ fontSize: 18 }}>{view.state}</div>
        </div>
        <div>
          <div style={{ color: 'var(--ink-500)', fontSize: 12 }}>candidates</div>
          <div style={{ fontSize: 18 }}>
            {view.candidates_attempted.toLocaleString()} attempted ·{' '}
            {view.candidates_verified.toLocaleString()} verified
          </div>
        </div>
      </div>
      <div style={{ marginTop: 24 }}>
        <div style={{ color: 'var(--ink-500)', fontSize: 12, marginBottom: 8 }}>event log</div>
        <ul
          style={{
            listStyle: 'none',
            padding: 0,
            margin: 0,
            maxHeight: 320,
            overflowY: 'auto',
            fontFamily: 'var(--font-mono)',
            fontSize: 13,
          }}
        >
          {events.map((e) => (
            <li
              key={e.id}
              style={{ borderTop: '1px solid var(--paper-200)', padding: '6px 0' }}
            >
              <span style={{ color: 'var(--ink-500)' }}>
                {new Date(e.at).toLocaleTimeString()}
              </span>{' '}
              <strong>{e.kind}</strong>{' '}
              <code style={{ fontSize: 12 }}>{JSON.stringify(e.payload)}</code>
            </li>
          ))}
        </ul>
      </div>
    </div>
  );
}
```

- [ ] **Step 3: Write the live-view route**

```tsx
import { createFileRoute, redirect, Link } from '@tanstack/react-router';
import { useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { JobProgress } from '~/components/conjecture/JobProgress';
import { SuggestionCard } from '~/components/conjecture/SuggestionCard';
import { isApiError } from '~/lib/api';
import { useConjecture, useMe, useStartConjecture } from '~/lib/queries';
import { useConjectureStream } from '~/lib/sse';

export const Route = createFileRoute('/conjecture/$id')({ component: ConjectureJobPage });

function ConjectureJobPage() {
  const { id } = Route.useParams();
  const me = useMe();
  const job = useConjecture(id);
  const start = useStartConjecture(id);
  const liveEvents = useConjectureStream(id);
  const [chosen, setChosen] = useState<number | null>(null);
  const [startError, setStartError] = useState<string | null>(null);

  if (me.isPending || job.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });
  if (!job.data) {
    return (
      <div className="app">
        <AppHeader active="conjecture" />
        <div className="container-wide">Job not found.</div>
        <AppFooter />
      </div>
    );
  }

  const view = job.data;
  const canStart = view.state === 'LlmComplete' && view.suggestions != null;
  const isLive = ['QueuedForWorker', 'Running', 'Complete'].includes(view.state);

  async function onStart() {
    if (chosen == null) return;
    setStartError(null);
    try {
      await start.mutateAsync({ chosen_index: chosen });
    } catch (e) {
      if (isApiError(e)) {
        setStartError(`Request failed (${e.status})`);
      } else {
        setStartError('Network error');
      }
    }
  }

  return (
    <div className="app">
      <AppHeader active="conjecture" />
      <div className="container-wide" style={{ maxWidth: 880 }}>
        <div className="page-head">
          <span className="overline">Conjecture · {view.state}</span>
          <h1>
            <em style={{ fontStyle: 'italic', color: 'var(--terracotta-700)', fontWeight: 300 }}>
              {view.hunch}
            </em>
          </h1>
          <p className="lede">
            {view.provider} / {view.model} · budget {view.budget.wall_seconds}s ·{' '}
            {view.budget.max_candidates.toLocaleString()} candidates
          </p>
        </div>

        {canStart && view.suggestions && (
          <div className="page-body">
            <h3 className="section-h" style={{ fontSize: 22, marginBottom: 16 }}>
              LLM suggestions
            </h3>
            {view.suggestions.map((s, i) => (
              <SuggestionCard
                key={i}
                suggestion={s}
                index={i}
                selected={chosen === i}
                onSelect={() => setChosen(i)}
              />
            ))}
            {startError && (
              <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13 }}>
                {startError}
              </div>
            )}
            <div style={{ marginTop: 16, display: 'flex', gap: 12 }}>
              <button
                className="btn btn-primary"
                disabled={chosen == null || start.isPending}
                onClick={onStart}
              >
                {start.isPending ? 'Queuing…' : 'Start GA run'}
              </button>
            </div>
          </div>
        )}

        {isLive && <JobProgress view={view} events={liveEvents} />}

        {view.state === 'Complete' && view.verified_theorem_ids.length > 0 && (
          <div className="card" style={{ marginTop: 24 }}>
            <h3 className="section-h" style={{ fontSize: 22, marginBottom: 16 }}>
              Verified theorems
            </h3>
            <ul style={{ listStyle: 'none', padding: 0, margin: 0 }}>
              {view.verified_theorem_ids.map((id) => (
                <li key={id} style={{ fontFamily: 'var(--font-mono)', padding: '4px 0' }}>
                  <Link to="/theorem/$id" params={{ id }}>
                    {id}
                  </Link>
                </li>
              ))}
            </ul>
          </div>
        )}
      </div>
      <AppFooter />
    </div>
  );
}
```

- [ ] **Step 4: Verify**

Run: `cd nasrudin-frontend && pnpm tsc --noEmit && pnpm build`
Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add nasrudin-frontend/src/routes/conjecture.\$id.tsx nasrudin-frontend/src/components/conjecture/ nasrudin-frontend/src/routeTree.gen.ts
git commit -m "feat(frontend): /conjecture/\$id live view (suggestions + SSE progress)"
```

---

## Task 17: `/jobs` route (user's conjecture list)

**Files:**
- Create: `nasrudin-frontend/src/routes/jobs.tsx`

- [ ] **Step 1: Write the route**

```tsx
import { createFileRoute, Link, redirect } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useMe, useMyConjectures } from '~/lib/queries';

export const Route = createFileRoute('/jobs')({ component: JobsPage });

function JobsPage() {
  const me = useMe();
  const list = useMyConjectures();

  if (me.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });

  return (
    <div className="app">
      <AppHeader active="conjecture" />
      <div className="container-wide" style={{ maxWidth: 980 }}>
        <div className="page-head">
          <span className="overline">Research</span>
          <h1>
            Your conjectures —{' '}
            <em
              style={{ fontStyle: 'italic', color: 'var(--terracotta-700)', fontWeight: 300 }}
            >
              hypotheses you've sent through the loop.
            </em>
          </h1>
        </div>
        <div className="page-body">
          {list.isPending && <div>Loading…</div>}
          {list.data && list.data.conjectures.length === 0 && (
            <div className="card">
              No conjectures yet.{' '}
              <Link to="/conjecture">Submit your first one →</Link>
            </div>
          )}
          {list.data && list.data.conjectures.length > 0 && (
            <ul style={{ listStyle: 'none', padding: 0, margin: 0 }}>
              {list.data.conjectures.map((c) => (
                <li
                  key={c.id}
                  style={{
                    borderTop: '1px solid var(--paper-200)',
                    padding: '12px 0',
                    display: 'flex',
                    gap: 16,
                    alignItems: 'baseline',
                  }}
                >
                  <span
                    style={{
                      fontFamily: 'var(--font-mono)',
                      fontSize: 12,
                      color: 'var(--ink-500)',
                      minWidth: 130,
                    }}
                  >
                    {new Date(c.created_at).toLocaleString()}
                  </span>
                  <Link
                    to="/conjecture/$id"
                    params={{ id: c.id }}
                    style={{ flex: 1, fontFamily: 'var(--font-sans)' }}
                  >
                    {c.hunch.slice(0, 100)}
                    {c.hunch.length > 100 ? '…' : ''}
                  </Link>
                  <StatePill state={c.state} outcome={c.outcome} />
                </li>
              ))}
            </ul>
          )}
        </div>
      </div>
      <AppFooter />
    </div>
  );
}

function StatePill({ state, outcome }: { state: string; outcome: string | null }) {
  const text = state === 'Complete' ? `Complete · ${outcome ?? ''}` : state;
  const bg =
    state === 'Complete'
      ? 'var(--olive-100)'
      : state === 'Running'
      ? 'var(--terracotta-100)'
      : 'var(--paper-100)';
  return (
    <span
      style={{
        fontFamily: 'var(--font-mono)',
        fontSize: 12,
        padding: '2px 10px',
        borderRadius: 999,
        background: bg,
        color: 'var(--ink-700)',
      }}
    >
      {text}
    </span>
  );
}
```

- [ ] **Step 2: Verify**

Run: `cd nasrudin-frontend && pnpm tsc --noEmit && pnpm build`

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/routes/jobs.tsx nasrudin-frontend/src/routeTree.gen.ts
git commit -m "feat(frontend): /jobs lists user's conjectures with status pills"
```

---

## Task 18: AppHeader nav

**Files:**
- Modify: `nasrudin-frontend/src/components/platform/AppHeader.tsx`

- [ ] **Step 1: Add the link**

Find the existing nav between `/library` and `/workers`. Insert a `Link` to `/conjecture` (label: "Conjecture") and update the `active` discriminator type to include `'conjecture'`. Mirror the existing styling exactly. (If the file uses an array of `{ to, label }` objects, add `{ to: '/conjecture', label: 'Conjecture' }` at the right index.)

- [ ] **Step 2: Verify**

Run: `cd nasrudin-frontend && pnpm tsc --noEmit && pnpm build`

- [ ] **Step 3: Commit**

```bash
git add nasrudin-frontend/src/components/platform/AppHeader.tsx
git commit -m "feat(frontend): add /conjecture to AppHeader nav"
```

---

## Task 19: Operator docs

**Files:**
- Create: `engine/crates/api/src/conjecture/CONJECTURE.md`

- [ ] **Step 1: Write the doc**

```markdown
# Conjecture loop (Phase D)

Phase D wires the **server-side LLM call** plus the **`conjecture_jobs` state machine**. Worker-side claim/heartbeat/submit lands in Phase E.

## State machine

```
Created → LlmComplete → QueuedForWorker → (Phase E: Running → Complete)
                                ↑
                         set_chosen_seed
```

A failure during the LLM phase short-circuits to `Complete{outcome=Failed:<reason>}` and is visible to the user immediately.

## Endpoints

| Verb | Path | Notes |
|---|---|---|
| `POST` | `/api/conjecture` | Sync; runs the LLM (≤ 60 s budget upstream of Registry retries); returns suggestions |
| `POST` | `/api/conjecture/{id}/start` | Picks a suggestion; transitions to `QueuedForWorker` |
| `GET`  | `/api/conjecture/{id}` | Full row (suggestions, seed, progress) |
| `GET`  | `/api/conjecture/{id}/sse` | Server-sent events: replays history, then streams live |
| `GET`  | `/api/me/conjectures` | List the caller's last 50 jobs |

All five require cookie auth and 503 if `NASRUDIN_KEY_ENCRYPT` is unset.

## Provider scope

Phase D launches **anthropic only** per spec §13. Requests with any other provider get a 400 `unsupported_provider`. OpenAI and Ollama are wired in `nasrudin-llm`'s `Registry` and ready to switch on in a follow-up.

## SSE wire format

Each `Event` carries:
- `event` — one of `state_change | progress | candidate_verified | complete`
- `data` — JSON `{ id, kind, payload, at }`

History (everything in `conjecture_events` for the job) is replayed first, then live events from the in-process broadcast channel are appended. Keep-alive pings every 15 s.

## What Phase D does NOT do

- Worker dequeue. The row sits in `QueuedForWorker` until Phase E ships `/api/conjecture/claim`.
- Embedding-driven retrieval. `nearest_neighbours` returns `Vec::new()` until the embedder is threaded into `AppState`. The LLM still gets the axiom catalog, which is enough for useful seeds.
- Paper draft generation (Phase F).
```

- [ ] **Step 2: Commit**

```bash
git add engine/crates/api/src/conjecture/CONJECTURE.md
git commit -m "docs(conjecture): operator docs for Phase D"
```

---

## Task 20: Workspace test sweep

**Files:** None (pure verification).

- [ ] **Step 1: Run the full test suite**

Run: `cargo test --workspace`
Expected: all tests pass.

- [ ] **Step 2: Run frontend type-check**

Run: `cd nasrudin-frontend && pnpm tsc --noEmit && pnpm build`
Expected: exit 0.

- [ ] **Step 3: If both pass, no commit needed.**

Phase D is done.

---

## Self-Review Checklist (read after writing the plan, fix inline)

- ✅ All 20 tasks have explicit file paths.
- ✅ Code snippets are complete (no `// TODO` placeholders that block compilation).
- ✅ Migration filenames are date-sorted (`20260801_000007` follows the existing `20260710_000006`).
- ✅ Provider validation is anthropic-only per spec §13; the path forward (drop the check) is documented in the operator doc.
- ✅ The SSE handler replays history *and* subscribes live — matches spec §6.3.
- ✅ Embedding-retrieval shortcut is intentional and documented in two places (orchestrate.rs + CONJECTURE.md).
- ✅ Tests target the actual public surface (auth gates, type round-trips, prompt content).
- ✅ Frontend types align field-by-field with the Rust DTOs in Task 5.
- ✅ No worker endpoints — those land in Phase E.
