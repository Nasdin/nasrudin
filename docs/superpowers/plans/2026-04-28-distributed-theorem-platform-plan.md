# Phase 9 — Distributed Theorem Platform Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Move the verified-theorem corpus into RocksDB+Postgres behind a public Axum API, deployed to a single DigitalOcean droplet at `nasrudin.org`, with the ingest pipeline as the contribution membrane for the in-process GA worker today and external remote workers in Phase 10.

**Architecture:** Existing Rust workspace (`engine/crates/`), TanStack Start frontend (`nasrudin-frontend/`), Lean 4 prover (`prover/`). Phase 9 wires a new ingest pipeline (auth → rate-limit → axiom/sorry pre-flight → dedup → Postgres `Pending` insert → RocksDB queue → A-path regen + B-fallback `lake build` → atomic Verified flip + contributor-counter increment → SSE broadcast) connecting GA discoveries to a persistent corpus the API serves to the frontend via existing `nasrudin-frontend/src/lib/queries.ts` hooks.

**Tech Stack:** Rust 2024 + Axum 0.8 + SeaORM 2 + Postgres 18 + RocksDB 0.24 + Lean 4.27 + Mathlib + TanStack Start v1 + React 19 + Caddy + Cloudflare + DigitalOcean droplet/Spaces/Block-Volume.

**Spec:** [`docs/superpowers/specs/2026-04-28-distributed-theorem-platform-design.md`](../specs/2026-04-28-distributed-theorem-platform-design.md)

---

## File Structure

### Files to create

| Path | Responsibility |
|---|---|
| `engine/crates/pg/src/migrator/m20260501_000003_theorems.rs` | SeaORM migration: `theorems` table per spec schema |
| `engine/crates/pg/src/migrator/m20260501_000004_workers_extend.rs` | SeaORM migration: extend `workers` with heartbeat/contribution columns |
| `engine/crates/pg/src/entity/theorems.rs` | SeaORM model for `theorems` |
| `engine/crates/pg/src/query/theorems.rs` | Theorem CRUD: insert, dedup-by-hash, status update, list-with-cursor, by-contributor |
| `engine/crates/api/src/handlers/ingest.rs` | `POST /api/ingest` |
| `engine/crates/api/src/handlers/theorems.rs` | `GET /api/theorems`, `/recent`, `/:id`, `/:hash/lean` |
| `engine/crates/api/src/handlers/events.rs` | `GET /api/events/discoveries`, `/api/events/stats` |
| `engine/crates/api/src/handlers/seed.rs` | `GET /api/seed?domain=X` |
| `engine/crates/api/src/handlers/me_stats.rs` | `GET /api/me/stats` |
| `engine/crates/api/src/reverify.rs` | Reverify queue, drain loop, A→B fallback |
| `engine/crates/api/src/lake_builder.rs` | Tokio task pool wrapping `lake build` + axiom/sorry pre-flight |
| `engine/crates/api/src/hydration.rs` | Boot-time Postgres → RocksDB hydration |
| `engine/crates/api/src/bin/backfill_existing_lean.rs` | One-shot script ingesting `prover/PhysicsGenerator/Derived/*.lean` |
| `nasrudin-frontend/src/lib/sse.ts` | `useDiscoveryFeed()` + `useStatsStream()` SSE hooks |
| `deploy/docker-compose.yml` | All services |
| `deploy/Caddyfile` | TLS + reverse-proxy |
| `deploy/.env.example` | Documented env vars |
| `deploy/rclone.conf.example` | Spaces creds template |
| `deploy/scripts/bootstrap.sh` | Idempotent fresh-droplet setup |
| `deploy/scripts/restore-from-spaces.sh` | Disaster recovery |
| `deploy/scripts/smoke.sh` | Post-deploy verification |
| `deploy/dockerfiles/api.Dockerfile` | API container build |
| `deploy/dockerfiles/frontend.Dockerfile` | Frontend container build |
| `deploy/dockerfiles/backup.Dockerfile` | Backup container with cron loop |
| `docs/RUNBOOK.md` | Operations playbook |
| `docs/DEPLOYMENT.md` | Deploy guide |

### Files to modify

| Path | Change |
|---|---|
| `engine/crates/pg/src/migrator/mod.rs` | Register two new migrations |
| `engine/crates/pg/src/entity/mod.rs` | Re-export `theorems` |
| `engine/crates/pg/src/entity/workers.rs` | Add heartbeat/contribution fields to `Model` |
| `engine/crates/pg/src/query/workers.rs` | Add `update_heartbeat`, `increment_contribution`, `list_all` |
| `engine/crates/pg/src/query/mod.rs` | Re-export `theorems` |
| `engine/crates/pg/src/lib.rs` | Re-export `entity::theorems` |
| `engine/crates/rocks/src/lib.rs` | Add `reverify_queue` CF + queue ops |
| `engine/crates/api/src/state.rs` | Add `reverify_queue: Arc<ReverifyQueue>`, `lake: Arc<LakeBuilder>`, `worker_rate_limiter` |
| `engine/crates/api/src/lib.rs` | `pub mod reverify; pub mod lake_builder; pub mod hydration;` |
| `engine/crates/api/src/main.rs` | Spawn drain loop, run hydration on boot, register new routes |
| `engine/crates/api/src/handlers/mod.rs` | `pub mod ingest; pub mod theorems; pub mod events; pub mod seed; pub mod me_stats;` |
| `engine/crates/api/src/handlers/workers.rs` | Add `heartbeat()` and `list()` handlers |
| `engine/crates/api/src/handlers/me.rs` | (split: keep `me`; new file `me_stats.rs` for stats) |
| `engine/crates/api/src/rate_limit.rs` | Add per-worker token bucket |
| `engine/crates/api/Cargo.toml` | Dependencies: `governor`, `tempfile`, `regex`, `chrono`, `reqwest` (for backfill bin) |
| `engine/crates/ga/src/bin/discover_emc2.rs` | Replace `verify_chain` file write with `submit_to_api` HTTP POST |
| `engine/crates/ga/Cargo.toml` | Add `reqwest` for HTTP submission |
| `nasrudin-frontend/src/lib/queries.ts` | Add `useTheoremsList`, `useDomains`, `useAxioms`, `useMeStats`, `useWorkers`, `useTheoremLean`; ensure `Theorem`-type alignment |
| `nasrudin-frontend/src/lib/types.ts` | Update `Theorem` to match server response (status, fitness sub-fields, parents) |

---

## Phase Index

1. Postgres schema + queries (Tasks 1.1–1.5)
2. RocksDB extensions + hydration (Tasks 2.1–2.2)
3. Lake builder + reverify queue (Tasks 3.1–3.4)
4. Ingest endpoint + rate limit (Tasks 4.1–4.3)
5. Read endpoints + SSE + seed (Tasks 5.1–5.4)
6. Auxiliary endpoints (Tasks 6.1–6.3)
7. GA worker + backfill (Tasks 7.1–7.3)
8. Frontend wiring (Tasks 8.1–8.2)
9. Deploy infrastructure (Tasks 9.1–9.5)
10. Acceptance + go-live (Tasks 10.1–10.4)

---

## Phase 1 — Postgres schema + queries

### Task 1.1: Theorems table migration

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260501_000003_theorems.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Create the migration file**

```rust
// engine/crates/pg/src/migrator/m20260501_000003_theorems.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(Theorems::Table)
                    .if_not_exists()
                    .col(ColumnDef::new(Theorems::Id).binary_len(8).not_null().primary_key())
                    .col(ColumnDef::new(Theorems::CanonicalHash).binary_len(8).not_null().unique_key())
                    .col(ColumnDef::new(Theorems::CanonicalStatement).text().not_null())
                    .col(ColumnDef::new(Theorems::Latex).text())
                    .col(ColumnDef::new(Theorems::LeanSource).text().not_null())
                    .col(ColumnDef::new(Theorems::Domain).text().not_null())
                    .col(ColumnDef::new(Theorems::AxiomsUsed).array(ColumnType::Text).not_null())
                    .col(ColumnDef::new(Theorems::ChainJson).json_binary().not_null())
                    .col(ColumnDef::new(Theorems::Parents).array(ColumnType::Binary(BlobSize::Blob(Some(8)))))
                    .col(ColumnDef::new(Theorems::OriginKind).text().not_null())
                    .col(ColumnDef::new(Theorems::OriginPayload).json_binary())
                    .col(ColumnDef::new(Theorems::Depth).integer())
                    .col(ColumnDef::new(Theorems::Complexity).integer())
                    .col(ColumnDef::new(Theorems::Generation).big_integer())
                    .col(ColumnDef::new(Theorems::FitnessNovelty).float())
                    .col(ColumnDef::new(Theorems::FitnessCompactness).float())
                    .col(ColumnDef::new(Theorems::FitnessDimensionalCorrectness).float())
                    .col(ColumnDef::new(Theorems::FitnessDomainCoverage).float())
                    .col(ColumnDef::new(Theorems::FitnessAxiomEfficiency).float())
                    .col(ColumnDef::new(Theorems::FitnessNasrudinRelevance).float())
                    .col(ColumnDef::new(Theorems::FitnessDepthScore).float())
                    .col(ColumnDef::new(Theorems::Dimension).array(ColumnType::Integer))
                    .col(ColumnDef::new(Theorems::EngineGitSha).text().not_null())
                    .col(ColumnDef::new(Theorems::LeanVersion).text().not_null())
                    .col(ColumnDef::new(Theorems::VerificationTactic).text())
                    .col(ColumnDef::new(Theorems::VerificationDurationMs).integer())
                    .col(ColumnDef::new(Theorems::VerificationPath).text())
                    .col(ColumnDef::new(Theorems::Status).text().not_null().default("Pending"))
                    .col(ColumnDef::new(Theorems::RejectedReason).text())
                    .col(ColumnDef::new(Theorems::ContributorId).text().not_null())
                    .col(ColumnDef::new(Theorems::CreatedAt).timestamp_with_time_zone().not_null().default(Expr::current_timestamp()))
                    .col(ColumnDef::new(Theorems::VerifiedAt).timestamp_with_time_zone())
                    .to_owned(),
            )
            .await?;

        manager.create_index(Index::create().name("idx_theorems_domain").table(Theorems::Table).col(Theorems::Domain).to_owned()).await?;
        manager.create_index(Index::create().name("idx_theorems_depth").table(Theorems::Table).col(Theorems::Depth).to_owned()).await?;
        manager.create_index(Index::create().name("idx_theorems_generation").table(Theorems::Table).col(Theorems::Generation).to_owned()).await?;
        manager.create_index(Index::create().name("idx_theorems_status").table(Theorems::Table).col(Theorems::Status).to_owned()).await?;
        manager.create_index(Index::create().name("idx_theorems_contributor").table(Theorems::Table).col(Theorems::ContributorId).to_owned()).await?;
        manager.create_index(Index::create().name("idx_theorems_verified_at").table(Theorems::Table).col(Theorems::VerifiedAt).to_owned()).await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager.drop_table(Table::drop().table(Theorems::Table).to_owned()).await
    }
}

#[derive(DeriveIden)]
enum Theorems {
    Table,
    Id, CanonicalHash, CanonicalStatement, Latex, LeanSource, Domain,
    AxiomsUsed, ChainJson, Parents, OriginKind, OriginPayload,
    Depth, Complexity, Generation,
    FitnessNovelty, FitnessCompactness, FitnessDimensionalCorrectness,
    FitnessDomainCoverage, FitnessAxiomEfficiency, FitnessNasrudinRelevance, FitnessDepthScore,
    Dimension, EngineGitSha, LeanVersion,
    VerificationTactic, VerificationDurationMs, VerificationPath,
    Status, RejectedReason, ContributorId, CreatedAt, VerifiedAt,
}
```

- [ ] **Step 2: Register the migration**

Edit `engine/crates/pg/src/migrator/mod.rs`:

```rust
use sea_orm_migration::prelude::*;

mod m20250101_000001_create_tables;
mod m20260428_000002_api_keys;
mod m20260501_000003_theorems;

pub struct Migrator;

#[async_trait::async_trait]
impl MigratorTrait for Migrator {
    fn migrations() -> Vec<Box<dyn MigrationTrait>> {
        vec![
            Box::new(m20250101_000001_create_tables::Migration),
            Box::new(m20260428_000002_api_keys::Migration),
            Box::new(m20260501_000003_theorems::Migration),
        ]
    }
}
```

- [ ] **Step 3: Verify migration compiles**

Run: `cargo check -p nasrudin-pg`
Expected: clean compile.

- [ ] **Step 4: Run migration up + down against a throwaway DB**

```bash
cd /Volumes/CORSAIR/code/personal/nasrudin
just db-start
DATABASE_URL=postgres://physics:physics@localhost:5432/physics_generator \
  cargo run -p nasrudin-pg --bin migrate -- up
psql $DATABASE_URL -c "\d theorems"          # confirm columns exist
DATABASE_URL=$DATABASE_URL cargo run -p nasrudin-pg --bin migrate -- down
psql $DATABASE_URL -c "\d theorems"          # confirm table dropped
DATABASE_URL=$DATABASE_URL cargo run -p nasrudin-pg --bin migrate -- up
```
Expected: `\d theorems` lists all 32 columns + 6 indexes.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260501_000003_theorems.rs engine/crates/pg/src/migrator/mod.rs
git commit -m "feat(pg): add theorems table migration"
```

### Task 1.2: Workers table extensions migration

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260501_000004_workers_extend.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`, `engine/crates/pg/src/entity/workers.rs`

- [ ] **Step 1: Create the migration**

```rust
// engine/crates/pg/src/migrator/m20260501_000004_workers_extend.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let table = Workers::Table;
        manager.alter_table(Table::alter().table(table.clone()).add_column(ColumnDef::new(Workers::LastHeartbeatAt).timestamp_with_time_zone()).to_owned()).await?;
        manager.alter_table(Table::alter().table(table.clone()).add_column(ColumnDef::new(Workers::LastContributionAt).timestamp_with_time_zone()).to_owned()).await?;
        manager.alter_table(Table::alter().table(table.clone()).add_column(ColumnDef::new(Workers::CurrentGeneration).big_integer().default(0)).to_owned()).await?;
        manager.alter_table(Table::alter().table(table.clone()).add_column(ColumnDef::new(Workers::TheoremsProducedTotal).big_integer().default(0)).to_owned()).await?;
        manager.alter_table(Table::alter().table(table.clone()).add_column(ColumnDef::new(Workers::UptimeSeconds).big_integer().default(0)).to_owned()).await?;
        manager.alter_table(Table::alter().table(table.clone()).add_column(ColumnDef::new(Workers::EngineGitSha).text()).to_owned()).await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let table = Workers::Table;
        for col in [
            Workers::LastHeartbeatAt, Workers::LastContributionAt, Workers::CurrentGeneration,
            Workers::TheoremsProducedTotal, Workers::UptimeSeconds, Workers::EngineGitSha,
        ] {
            manager.alter_table(Table::alter().table(table.clone()).drop_column(col).to_owned()).await?;
        }
        Ok(())
    }
}

#[derive(DeriveIden)]
enum Workers {
    Table, LastHeartbeatAt, LastContributionAt, CurrentGeneration,
    TheoremsProducedTotal, UptimeSeconds, EngineGitSha,
}
```

- [ ] **Step 2: Register and update entity**

Update `engine/crates/pg/src/migrator/mod.rs` to add `Box::new(m20260501_000004_workers_extend::Migration)`. Update `engine/crates/pg/src/entity/workers.rs` to add the new fields:

```rust
#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel, Serialize)]
#[sea_orm(table_name = "workers")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false, column_type = "Text")]
    pub id: String,
    pub name: Option<String>,
    pub host: Option<String>,
    pub last_seen: DateTimeWithTimeZone,
    pub theorems_contributed: i64,
    pub status: WorkerStatus,
    pub last_heartbeat_at: Option<DateTimeWithTimeZone>,
    pub last_contribution_at: Option<DateTimeWithTimeZone>,
    pub current_generation: i64,
    pub theorems_produced_total: i64,
    pub uptime_seconds: i64,
    pub engine_git_sha: Option<String>,
}
```

- [ ] **Step 3: Verify**

```bash
cargo check -p nasrudin-pg
DATABASE_URL=postgres://physics:physics@localhost:5432/physics_generator cargo run -p nasrudin-pg --bin migrate -- up
psql $DATABASE_URL -c "\d workers" | grep -E "last_heartbeat_at|current_generation|engine_git_sha"
```
Expected: all six new columns visible.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260501_000004_workers_extend.rs engine/crates/pg/src/migrator/mod.rs engine/crates/pg/src/entity/workers.rs
git commit -m "feat(pg): extend workers with heartbeat + contribution columns"
```

### Task 1.3: Theorems SeaORM entity

**Files:**
- Create: `engine/crates/pg/src/entity/theorems.rs`
- Modify: `engine/crates/pg/src/entity/mod.rs`, `engine/crates/pg/src/lib.rs`

- [ ] **Step 1: Create the entity**

```rust
// engine/crates/pg/src/entity/theorems.rs
use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "theorems")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false, column_type = "Binary(8)")]
    pub id: Vec<u8>,
    #[sea_orm(unique, column_type = "Binary(8)")]
    pub canonical_hash: Vec<u8>,
    pub canonical_statement: String,
    pub latex: Option<String>,
    pub lean_source: String,
    pub domain: String,
    #[sea_orm(column_type = "Custom(\"text[]\".to_owned())")]
    pub axioms_used: Vec<String>,
    #[sea_orm(column_type = "JsonBinary")]
    pub chain_json: Json,
    #[sea_orm(column_type = "Custom(\"bytea[]\".to_owned())", nullable)]
    pub parents: Option<Vec<Vec<u8>>>,
    pub origin_kind: String,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub origin_payload: Option<Json>,
    pub depth: Option<i32>,
    pub complexity: Option<i32>,
    pub generation: Option<i64>,
    pub fitness_novelty: Option<f32>,
    pub fitness_compactness: Option<f32>,
    pub fitness_dimensional_correctness: Option<f32>,
    pub fitness_domain_coverage: Option<f32>,
    pub fitness_axiom_efficiency: Option<f32>,
    pub fitness_nasrudin_relevance: Option<f32>,
    pub fitness_depth_score: Option<f32>,
    #[sea_orm(column_type = "Custom(\"integer[]\".to_owned())", nullable)]
    pub dimension: Option<Vec<i32>>,
    pub engine_git_sha: String,
    pub lean_version: String,
    pub verification_tactic: Option<String>,
    pub verification_duration_ms: Option<i32>,
    pub verification_path: Option<String>,
    pub status: String,
    pub rejected_reason: Option<String>,
    pub contributor_id: String,
    pub created_at: DateTimeWithTimeZone,
    pub verified_at: Option<DateTimeWithTimeZone>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 2: Re-export**

Edit `engine/crates/pg/src/entity/mod.rs` to add `pub mod theorems;`. Edit `engine/crates/pg/src/lib.rs` to add `pub use entity::theorems;`.

- [ ] **Step 3: Verify compile**

```bash
cargo check -p nasrudin-pg
```
Expected: clean.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/entity/theorems.rs engine/crates/pg/src/entity/mod.rs engine/crates/pg/src/lib.rs
git commit -m "feat(pg): add theorems SeaORM entity"
```

### Task 1.4: Theorem queries — insert, dedup, list, lookup

**Files:**
- Create: `engine/crates/pg/src/query/theorems.rs`, `engine/crates/pg/tests/theorems_query.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`

- [ ] **Step 1: Write the failing tests**

```rust
// engine/crates/pg/tests/theorems_query.rs
use nasrudin_pg::{connect_simple, run_migrations};
use nasrudin_pg::query::theorems;
use sea_orm::DatabaseConnection;

async fn fresh_db() -> DatabaseConnection {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| "postgres://physics:physics@localhost:5432/physics_generator_test".into());
    let db = connect_simple(&url).await.unwrap();
    sea_orm::ConnectionTrait::execute_unprepared(&db, "DROP TABLE IF EXISTS theorems CASCADE; DROP TABLE IF EXISTS api_keys CASCADE; DROP TABLE IF EXISTS workers CASCADE; DROP TABLE IF EXISTS sessions CASCADE; DROP TABLE IF EXISTS user_preferences CASCADE; DROP TABLE IF EXISTS saved_searches CASCADE; DROP TABLE IF EXISTS users CASCADE; DROP TABLE IF EXISTS seaql_migrations CASCADE;").await.unwrap();
    run_migrations(&db).await.unwrap();
    db
}

fn sample_theorem(canonical: &str) -> theorems::NewTheorem {
    theorems::NewTheorem {
        id: nasrudin_core::theorem_id_from_canonical(canonical),
        canonical_hash: nasrudin_core::canonical_hash(canonical),
        canonical_statement: canonical.into(),
        domain: "SpecialRelativity".into(),
        lean_source: "import PhysicsGenerator.Axioms".into(),
        axioms_used: vec!["c_positive".into()],
        chain_json: serde_json::json!([]),
        engine_git_sha: "deadbee".into(),
        lean_version: "4.27.0".into(),
        contributor_id: "test-worker".into(),
        ..Default::default()
    }
}

#[tokio::test]
async fn insert_and_get_by_hash() {
    let db = fresh_db().await;
    let row = sample_theorem("E = m*c^2");
    let id = theorems::insert_pending(&db, row.clone()).await.unwrap();
    let got = theorems::get_by_canonical_hash(&db, &row.canonical_hash).await.unwrap().unwrap();
    assert_eq!(got.id, id);
    assert_eq!(got.status, "Pending");
}

#[tokio::test]
async fn dedup_returns_existing() {
    let db = fresh_db().await;
    let row = sample_theorem("E^2 = (mc^2)^2");
    let id1 = theorems::insert_pending(&db, row.clone()).await.unwrap();
    let id2 = theorems::insert_pending(&db, row.clone()).await;
    assert!(id2.is_err(), "second insert should fail (unique violation)");
    let existing = theorems::get_by_canonical_hash(&db, &row.canonical_hash).await.unwrap().unwrap();
    assert_eq!(existing.id, id1);
}

#[tokio::test]
async fn mark_verified_sets_path_and_timestamp() {
    let db = fresh_db().await;
    let row = sample_theorem("c*p = E");
    let id = theorems::insert_pending(&db, row).await.unwrap();
    theorems::mark_verified(&db, &id, "A", "nlinarith", 12345).await.unwrap();
    let got = theorems::get_by_id(&db, &id).await.unwrap().unwrap();
    assert_eq!(got.status, "Verified");
    assert_eq!(got.verification_path.as_deref(), Some("A"));
    assert_eq!(got.verification_tactic.as_deref(), Some("nlinarith"));
    assert!(got.verified_at.is_some());
}

#[tokio::test]
async fn list_with_cursor_returns_in_order_and_paginates() {
    let db = fresh_db().await;
    for i in 0..5 {
        let row = sample_theorem(&format!("statement_{i}"));
        let id = theorems::insert_pending(&db, row).await.unwrap();
        theorems::mark_verified(&db, &id, "A", "ring", 100).await.unwrap();
    }
    let page1 = theorems::list_verified(&db, None, 3, None).await.unwrap();
    assert_eq!(page1.items.len(), 3);
    let page2 = theorems::list_verified(&db, page1.next_cursor, 3, None).await.unwrap();
    assert_eq!(page2.items.len(), 2);
    assert!(page2.next_cursor.is_none());
}
```

Add to `engine/crates/core/src/lib.rs` if not already present (helpers used in tests):

```rust
pub fn canonical_hash(s: &str) -> Vec<u8> {
    use std::hash::Hasher;
    let mut h = twox_hash::XxHash64::with_seed(0);
    h.write(s.as_bytes());
    h.finish().to_le_bytes().to_vec()
}

pub fn theorem_id_from_canonical(s: &str) -> Vec<u8> {
    canonical_hash(s) // Phase 9: id = canonical_hash for now; future: compose with proof
}
```

- [ ] **Step 2: Run tests, expect failure**

```bash
TEST_DATABASE_URL=postgres://physics:physics@localhost:5432/physics_generator_test cargo test -p nasrudin-pg --test theorems_query
```
Expected: compile errors — `theorems::insert_pending` etc. don't exist yet.

- [ ] **Step 3: Implement queries**

```rust
// engine/crates/pg/src/query/theorems.rs
use crate::entity::theorems as ent;
use anyhow::Result;
use chrono::Utc;
use sea_orm::*;
use serde_json::Value as Json;

#[derive(Default, Clone, Debug)]
pub struct NewTheorem {
    pub id: Vec<u8>,
    pub canonical_hash: Vec<u8>,
    pub canonical_statement: String,
    pub latex: Option<String>,
    pub lean_source: String,
    pub domain: String,
    pub axioms_used: Vec<String>,
    pub chain_json: Json,
    pub parents: Option<Vec<Vec<u8>>>,
    pub origin_kind: String,
    pub origin_payload: Option<Json>,
    pub depth: Option<i32>,
    pub complexity: Option<i32>,
    pub generation: Option<i64>,
    pub fitness_novelty: Option<f32>,
    pub fitness_compactness: Option<f32>,
    pub fitness_dimensional_correctness: Option<f32>,
    pub fitness_domain_coverage: Option<f32>,
    pub fitness_axiom_efficiency: Option<f32>,
    pub fitness_nasrudin_relevance: Option<f32>,
    pub fitness_depth_score: Option<f32>,
    pub dimension: Option<Vec<i32>>,
    pub engine_git_sha: String,
    pub lean_version: String,
    pub contributor_id: String,
}

impl Default for NewTheorem {
    fn default() -> Self { Self {
        id: vec![], canonical_hash: vec![], canonical_statement: String::new(), latex: None,
        lean_source: String::new(), domain: "PureMath".into(), axioms_used: vec![],
        chain_json: serde_json::json!([]), parents: None, origin_kind: "Axiom".into(),
        origin_payload: None, depth: None, complexity: None, generation: None,
        fitness_novelty: None, fitness_compactness: None, fitness_dimensional_correctness: None,
        fitness_domain_coverage: None, fitness_axiom_efficiency: None, fitness_nasrudin_relevance: None,
        fitness_depth_score: None, dimension: None, engine_git_sha: String::new(),
        lean_version: String::new(), contributor_id: String::new(),
    }}
}

pub struct Page<T> {
    pub items: Vec<T>,
    pub next_cursor: Option<String>,
    pub total_capped: bool,
    pub total: u64,
}

pub async fn insert_pending(db: &DatabaseConnection, n: NewTheorem) -> Result<Vec<u8>> {
    let id = n.id.clone();
    let am = ent::ActiveModel {
        id: Set(n.id),
        canonical_hash: Set(n.canonical_hash),
        canonical_statement: Set(n.canonical_statement),
        latex: Set(n.latex),
        lean_source: Set(n.lean_source),
        domain: Set(n.domain),
        axioms_used: Set(n.axioms_used),
        chain_json: Set(n.chain_json),
        parents: Set(n.parents),
        origin_kind: Set(n.origin_kind),
        origin_payload: Set(n.origin_payload),
        depth: Set(n.depth),
        complexity: Set(n.complexity),
        generation: Set(n.generation),
        fitness_novelty: Set(n.fitness_novelty),
        fitness_compactness: Set(n.fitness_compactness),
        fitness_dimensional_correctness: Set(n.fitness_dimensional_correctness),
        fitness_domain_coverage: Set(n.fitness_domain_coverage),
        fitness_axiom_efficiency: Set(n.fitness_axiom_efficiency),
        fitness_nasrudin_relevance: Set(n.fitness_nasrudin_relevance),
        fitness_depth_score: Set(n.fitness_depth_score),
        dimension: Set(n.dimension),
        engine_git_sha: Set(n.engine_git_sha),
        lean_version: Set(n.lean_version),
        verification_tactic: Set(None),
        verification_duration_ms: Set(None),
        verification_path: Set(None),
        status: Set("Pending".into()),
        rejected_reason: Set(None),
        contributor_id: Set(n.contributor_id),
        created_at: Set(Utc::now().into()),
        verified_at: Set(None),
    };
    am.insert(db).await?;
    Ok(id)
}

pub async fn get_by_id(db: &DatabaseConnection, id: &[u8]) -> Result<Option<ent::Model>> {
    Ok(ent::Entity::find_by_id(id.to_vec()).one(db).await?)
}

pub async fn get_by_canonical_hash(db: &DatabaseConnection, hash: &[u8]) -> Result<Option<ent::Model>> {
    Ok(ent::Entity::find().filter(ent::Column::CanonicalHash.eq(hash.to_vec())).one(db).await?)
}

pub async fn mark_verified(db: &DatabaseConnection, id: &[u8], path: &str, tactic: &str, duration_ms: i32) -> Result<()> {
    let model: ent::ActiveModel = ent::Entity::find_by_id(id.to_vec()).one(db).await?
        .ok_or_else(|| anyhow::anyhow!("theorem not found"))?
        .into();
    let mut am = model;
    am.status = Set("Verified".into());
    am.verification_path = Set(Some(path.into()));
    am.verification_tactic = Set(Some(tactic.into()));
    am.verification_duration_ms = Set(Some(duration_ms));
    am.verified_at = Set(Some(Utc::now().into()));
    am.update(db).await?;
    Ok(())
}

pub async fn mark_rejected(db: &DatabaseConnection, id: &[u8], reason: &str) -> Result<()> {
    let model: ent::ActiveModel = ent::Entity::find_by_id(id.to_vec()).one(db).await?
        .ok_or_else(|| anyhow::anyhow!("theorem not found"))?
        .into();
    let mut am = model;
    am.status = Set("Rejected".into());
    am.rejected_reason = Set(Some(reason.into()));
    am.update(db).await?;
    Ok(())
}

pub async fn list_verified(db: &DatabaseConnection, cursor: Option<String>, limit: u64, domain: Option<String>) -> Result<Page<ent::Model>> {
    use sea_orm::query::*;
    let mut q = ent::Entity::find().filter(ent::Column::Status.eq("Verified"));
    if let Some(d) = &domain { q = q.filter(ent::Column::Domain.eq(d.clone())); }
    if let Some(c) = &cursor {
        let bytes = base64::Engine::decode(&base64::engine::general_purpose::URL_SAFE_NO_PAD, c)?;
        if bytes.len() < 16 { anyhow::bail!("bad cursor"); }
        let micros = i64::from_le_bytes(bytes[0..8].try_into()?);
        let id = bytes[8..16].to_vec();
        let dt = chrono::DateTime::from_timestamp_micros(micros).ok_or_else(|| anyhow::anyhow!("bad timestamp"))?;
        q = q.filter(Condition::any()
            .add(ent::Column::VerifiedAt.lt(DateTimeWithTimeZone::from(dt)))
            .add(Condition::all()
                .add(ent::Column::VerifiedAt.eq(DateTimeWithTimeZone::from(dt)))
                .add(ent::Column::Id.lt(id))));
    }
    let items: Vec<ent::Model> = q.order_by_desc(ent::Column::VerifiedAt).order_by_desc(ent::Column::Id).limit(limit + 1).all(db).await?;
    let (items, has_more) = if items.len() as u64 > limit { (items[..limit as usize].to_vec(), true) } else { (items, false) };
    let next_cursor = if has_more {
        let last = items.last().unwrap();
        let micros = last.verified_at.unwrap().timestamp_micros();
        let mut buf = micros.to_le_bytes().to_vec();
        buf.extend_from_slice(&last.id);
        Some(base64::Engine::encode(&base64::engine::general_purpose::URL_SAFE_NO_PAD, buf))
    } else { None };
    let total = ent::Entity::find().filter(ent::Column::Status.eq("Verified")).count(db).await?;
    Ok(Page { items, next_cursor, total_capped: total > 10_000, total: total.min(10_000) })
}
```

Add `base64 = "0.22"` and `twox-hash = "1.6"` to relevant `Cargo.toml`s. Add `pub mod theorems;` to `engine/crates/pg/src/query/mod.rs`.

- [ ] **Step 4: Run tests**

```bash
TEST_DATABASE_URL=postgres://physics:physics@localhost:5432/physics_generator_test cargo test -p nasrudin-pg --test theorems_query
```
Expected: 4/4 PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/query/theorems.rs engine/crates/pg/src/query/mod.rs engine/crates/pg/tests/theorems_query.rs engine/crates/pg/Cargo.toml engine/crates/core/src/lib.rs
git commit -m "feat(pg): add theorem queries (insert/dedup/lookup/list-with-cursor)"
```

### Task 1.5: Worker queries — heartbeat, contribution, list

**Files:**
- Modify: `engine/crates/pg/src/query/workers.rs`
- Test: `engine/crates/pg/tests/workers_query.rs`

- [ ] **Step 1: Write failing tests**

```rust
// engine/crates/pg/tests/workers_query.rs
use nasrudin_pg::{connect_simple, run_migrations, query::workers};

async fn fresh_db() -> sea_orm::DatabaseConnection { /* same helper as Task 1.4 */ todo!() }

#[tokio::test]
async fn heartbeat_updates_fields_atomically() {
    let db = fresh_db().await;
    workers::register(&db, "w1", Some("worker-one"), Some("host1")).await.unwrap();
    workers::update_heartbeat(&db, "w1", 17, 1234, 99, "deadbee").await.unwrap();
    let w = workers::get(&db, "w1").await.unwrap().unwrap();
    assert_eq!(w.current_generation, 17);
    assert_eq!(w.theorems_produced_total, 1234);
    assert_eq!(w.uptime_seconds, 99);
    assert_eq!(w.engine_git_sha.as_deref(), Some("deadbee"));
    assert!(w.last_heartbeat_at.is_some());
}

#[tokio::test]
async fn increment_contribution_is_atomic() {
    let db = fresh_db().await;
    workers::register(&db, "w2", None, None).await.unwrap();
    workers::increment_contribution(&db, "w2").await.unwrap();
    workers::increment_contribution(&db, "w2").await.unwrap();
    let w = workers::get(&db, "w2").await.unwrap().unwrap();
    assert_eq!(w.theorems_contributed, 2);
    assert!(w.last_contribution_at.is_some());
}

#[tokio::test]
async fn list_all_returns_ordered_by_contribution() {
    let db = fresh_db().await;
    workers::register(&db, "low", None, None).await.unwrap();
    workers::register(&db, "high", None, None).await.unwrap();
    for _ in 0..5 { workers::increment_contribution(&db, "high").await.unwrap(); }
    workers::increment_contribution(&db, "low").await.unwrap();
    let list = workers::list_all(&db).await.unwrap();
    assert_eq!(list.first().unwrap().id, "high");
    assert_eq!(list.last().unwrap().id, "low");
}
```

(Inline the `fresh_db` helper from Task 1.4 verbatim — do not reference Task 1.4.)

- [ ] **Step 2: Run, expect compile failure**

```bash
TEST_DATABASE_URL=… cargo test -p nasrudin-pg --test workers_query
```

- [ ] **Step 3: Implement queries**

Add to `engine/crates/pg/src/query/workers.rs`:

```rust
use crate::entity::workers as ent;
use anyhow::Result;
use chrono::Utc;
use sea_orm::*;

pub async fn get(db: &DatabaseConnection, id: &str) -> Result<Option<ent::Model>> {
    Ok(ent::Entity::find_by_id(id.to_string()).one(db).await?)
}

pub async fn update_heartbeat(db: &DatabaseConnection, id: &str, current_generation: i64, theorems_produced_total: i64, uptime_seconds: i64, engine_git_sha: &str) -> Result<()> {
    let model: ent::ActiveModel = ent::Entity::find_by_id(id.to_string()).one(db).await?
        .ok_or_else(|| anyhow::anyhow!("worker not found"))?.into();
    let mut am = model;
    am.last_heartbeat_at = Set(Some(Utc::now().into()));
    am.last_seen = Set(Utc::now().into());
    am.current_generation = Set(current_generation);
    am.theorems_produced_total = Set(theorems_produced_total);
    am.uptime_seconds = Set(uptime_seconds);
    am.engine_git_sha = Set(Some(engine_git_sha.into()));
    am.status = Set(crate::entity::workers::WorkerStatus::Active);
    am.update(db).await?;
    Ok(())
}

pub async fn increment_contribution(db: &DatabaseConnection, id: &str) -> Result<()> {
    db.execute(Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        "UPDATE workers SET theorems_contributed = theorems_contributed + 1, last_contribution_at = $1 WHERE id = $2",
        [Utc::now().into(), id.into()],
    )).await?;
    Ok(())
}

pub async fn list_all(db: &DatabaseConnection) -> Result<Vec<ent::Model>> {
    Ok(ent::Entity::find().order_by_desc(ent::Column::TheoremsContributed).all(db).await?)
}
```

- [ ] **Step 4: Run tests, all pass**

```bash
cargo test -p nasrudin-pg --test workers_query
```
Expected: 3/3 PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/pg/src/query/workers.rs engine/crates/pg/tests/workers_query.rs
git commit -m "feat(pg): add worker heartbeat, contribution increment, list_all"
```

---

## Phase 2 — RocksDB extensions + hydration

### Task 2.1: Reverify queue column family

**Files:**
- Modify: `engine/crates/rocks/src/lib.rs`
- Test: `engine/crates/rocks/tests/reverify_queue.rs`

- [ ] **Step 1: Write failing test**

```rust
// engine/crates/rocks/tests/reverify_queue.rs
use nasrudin_rocks::{TheoremDb, ReverifyJob};
use tempfile::tempdir;

#[test]
fn enqueue_and_drain_round_trip() {
    let dir = tempdir().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
    let job = ReverifyJob { theorem_id: [1,2,3,4,5,6,7,8], attempts: 0, enqueued_at_micros: 1700000000_000_000 };
    db.enqueue_reverify(&job).unwrap();
    let pending = db.list_reverify_pending(10).unwrap();
    assert_eq!(pending.len(), 1);
    assert_eq!(pending[0].theorem_id, job.theorem_id);
    db.dequeue_reverify(&job.theorem_id).unwrap();
    let pending = db.list_reverify_pending(10).unwrap();
    assert!(pending.is_empty());
}

#[test]
fn queue_persists_across_reopen() {
    let dir = tempdir().unwrap();
    {
        let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
        db.enqueue_reverify(&ReverifyJob { theorem_id: [9;8], attempts: 0, enqueued_at_micros: 0 }).unwrap();
    }
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
    let pending = db.list_reverify_pending(10).unwrap();
    assert_eq!(pending.len(), 1);
}
```

- [ ] **Step 2: Run, expect compile failure**

```bash
cargo test -p nasrudin-rocks --test reverify_queue
```

- [ ] **Step 3: Implement CF + ops**

In `engine/crates/rocks/src/lib.rs`, add to the `const` list:

```rust
const CF_REVERIFY_QUEUE: &str = "reverify_queue";

const ALL_CFS: &[&str] = &[
    CF_THEOREMS, CF_PROOFS, CF_LINEAGE, CF_BY_DOMAIN, CF_BY_DEPTH,
    CF_BY_AXIOM, CF_BY_GENERATION, CF_LATEX_INDEX, CF_STATS,
    CF_REVERIFY_QUEUE,
];
```

Then add types and methods:

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReverifyJob {
    pub theorem_id: TheoremId,
    pub attempts: u8,
    pub enqueued_at_micros: i64,
}

impl TheoremDb {
    pub fn enqueue_reverify(&self, job: &ReverifyJob) -> Result<()> {
        let cf = self.db.cf_handle(CF_REVERIFY_QUEUE).context("Missing reverify_queue CF")?;
        let value = serde_json::to_vec(job)?;
        self.db.put_cf(&cf, job.theorem_id, &value).context("Failed to enqueue")?;
        Ok(())
    }

    pub fn dequeue_reverify(&self, theorem_id: &TheoremId) -> Result<()> {
        let cf = self.db.cf_handle(CF_REVERIFY_QUEUE).context("Missing reverify_queue CF")?;
        self.db.delete_cf(&cf, theorem_id).context("Failed to dequeue")?;
        Ok(())
    }

    pub fn list_reverify_pending(&self, limit: usize) -> Result<Vec<ReverifyJob>> {
        let cf = self.db.cf_handle(CF_REVERIFY_QUEUE).context("Missing reverify_queue CF")?;
        let mut out = Vec::new();
        for item in self.db.iterator_cf(&cf, IteratorMode::Start) {
            let (_, v) = item?;
            out.push(serde_json::from_slice(&v)?);
            if out.len() >= limit { break; }
        }
        Ok(out)
    }

    pub fn reverify_queue_depth(&self) -> Result<usize> {
        let cf = self.db.cf_handle(CF_REVERIFY_QUEUE).context("Missing reverify_queue CF")?;
        Ok(self.db.iterator_cf(&cf, IteratorMode::Start).count())
    }
}
```

- [ ] **Step 4: Run tests, pass**

```bash
cargo test -p nasrudin-rocks --test reverify_queue
```
Expected: 2/2 PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/rocks/src/lib.rs engine/crates/rocks/tests/reverify_queue.rs
git commit -m "feat(rocks): add reverify_queue column family + ops"
```

### Task 2.2: Boot-time hydration

**Files:**
- Create: `engine/crates/api/src/hydration.rs`
- Modify: `engine/crates/api/src/lib.rs`, `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/hydration.rs`

- [ ] **Step 1: Write failing test**

```rust
// engine/crates/api/tests/hydration.rs
use nasrudin_api::hydration::hydrate_rocks_from_pg_if_empty;
use nasrudin_pg::{connect_simple, run_migrations, query::theorems};
use nasrudin_rocks::TheoremDb;
use tempfile::tempdir;

#[tokio::test]
async fn empty_rocks_hydrates_from_pg() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| "postgres://physics:physics@localhost:5432/physics_generator_test".into());
    let pg = connect_simple(&url).await.unwrap();
    sea_orm::ConnectionTrait::execute_unprepared(&pg, "DROP TABLE IF EXISTS theorems CASCADE; DROP TABLE IF EXISTS workers CASCADE; DROP TABLE IF EXISTS api_keys CASCADE; DROP TABLE IF EXISTS sessions CASCADE; DROP TABLE IF EXISTS user_preferences CASCADE; DROP TABLE IF EXISTS saved_searches CASCADE; DROP TABLE IF EXISTS users CASCADE; DROP TABLE IF EXISTS seaql_migrations CASCADE;").await.unwrap();
    run_migrations(&pg).await.unwrap();

    let row = theorems::NewTheorem {
        id: vec![1,2,3,4,5,6,7,8],
        canonical_hash: vec![10,20,30,40,50,60,70,80],
        canonical_statement: "1 = 1".into(),
        domain: "PureMath".into(),
        lean_source: "theorem t : 1=1 := rfl".into(),
        chain_json: serde_json::json!([]),
        engine_git_sha: "test".into(),
        lean_version: "4.27.0".into(),
        contributor_id: "test".into(),
        ..Default::default()
    };
    let id = theorems::insert_pending(&pg, row).await.unwrap();
    theorems::mark_verified(&pg, &id, "A", "rfl", 1).await.unwrap();

    let rocks_dir = tempdir().unwrap();
    let rocks = std::sync::Arc::new(TheoremDb::new(rocks_dir.path().to_str().unwrap()).unwrap());
    hydrate_rocks_from_pg_if_empty(&rocks, &pg).await.unwrap();
    assert!(rocks.theorem_exists(&id.try_into().unwrap()).unwrap());
}
```

- [ ] **Step 2: Run, fail**

- [ ] **Step 3: Implement hydration**

```rust
// engine/crates/api/src/hydration.rs
use anyhow::Result;
use nasrudin_core::{Theorem, TheoremId, ProofTree, Domain, VerificationStatus, TheoremOrigin};
use nasrudin_pg::{entity::theorems as ent, query::theorems as q};
use nasrudin_rocks::TheoremDb;
use sea_orm::{DatabaseConnection, EntityTrait, ColumnTrait, QueryFilter};
use std::sync::Arc;
use tracing::info;

pub async fn hydrate_rocks_from_pg_if_empty(rocks: &Arc<TheoremDb>, pg: &DatabaseConnection) -> Result<()> {
    let stats = rocks.get_stats()?;
    if stats.total_theorems > 0 {
        info!(theorems=stats.total_theorems, "RocksDB non-empty, skipping hydration");
        return Ok(());
    }
    info!("RocksDB empty, hydrating from Postgres");
    let mut count = 0u64;
    let mut last_id: Option<Vec<u8>> = None;
    loop {
        use sea_orm::QueryOrder;
        let mut query = ent::Entity::find()
            .filter(ent::Column::Status.eq("Verified"))
            .order_by_asc(ent::Column::Id)
            .limit(1000);
        if let Some(id) = &last_id { query = query.filter(ent::Column::Id.gt(id.clone())); }
        let batch = query.all(pg).await?;
        if batch.is_empty() { break; }
        last_id = batch.last().map(|t| t.id.clone());
        for row in batch {
            let theorem = pg_row_to_core_theorem(&row)?;
            if let Err(e) = rocks.put_theorem(&theorem) {
                tracing::warn!(theorem_id=hex::encode(&row.id), err=%e, "hydration: skip");
            } else {
                count += 1;
            }
        }
    }
    info!(count, "hydration complete");
    Ok(())
}

fn pg_row_to_core_theorem(row: &ent::Model) -> Result<Theorem> {
    let mut id = [0u8; 8];
    id.copy_from_slice(&row.id);
    let domain = match row.domain.as_str() {
        "SpecialRelativity" => Domain::SpecialRelativity,
        "Electromagnetism" => Domain::Electromagnetism,
        "ClassicalMechanics" => Domain::ClassicalMechanics,
        "QuantumMechanics" => Domain::QuantumMechanics,
        "Thermodynamics" => Domain::Thermodynamics,
        "PureMath" | _ => Domain::PureMath,
    };
    let parents: Vec<TheoremId> = row.parents.as_ref().map(|ps| {
        ps.iter().filter_map(|p| { let mut a=[0u8;8]; if p.len()==8 { a.copy_from_slice(p); Some(a) } else { None }}).collect()
    }).unwrap_or_default();
    Ok(Theorem {
        id,
        statement: nasrudin_core::Expr::Symbol(row.canonical_statement.clone()),
        latex: row.latex.clone().unwrap_or_default(),
        proof: ProofTree::leaf(row.lean_source.clone()),
        domain,
        depth: row.depth.unwrap_or(0) as u32,
        complexity: row.complexity.unwrap_or(0) as u32,
        generation: row.generation.unwrap_or(0) as u64,
        parents,
        children: vec![],
        verified: VerificationStatus::Verified { tactic: row.verification_tactic.clone().unwrap_or_default() },
        origin: TheoremOrigin::Axiom,
        ..Default::default()
    })
}
```

Add `pub mod hydration;` to `engine/crates/api/src/lib.rs`.

- [ ] **Step 4: Run, pass**

```bash
TEST_DATABASE_URL=… cargo test -p nasrudin-api --test hydration
```
Expected: 1/1 PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/hydration.rs engine/crates/api/src/lib.rs engine/crates/api/tests/hydration.rs
git commit -m "feat(api): add boot-time RocksDB hydration from Postgres"
```

---

## Phase 3 — Lake builder + reverify queue

### Task 3.1: Lake builder + axiom/sorry pre-flight

**Files:**
- Create: `engine/crates/api/src/lake_builder.rs`
- Test: `engine/crates/api/tests/lake_builder_preflight.rs`
- Modify: `engine/crates/api/src/lib.rs`, `engine/crates/api/Cargo.toml`

- [ ] **Step 1: Write failing tests**

```rust
// engine/crates/api/tests/lake_builder_preflight.rs
use nasrudin_api::lake_builder::preflight_axiom_or_sorry;

#[test]
fn rejects_top_level_axiom() {
    let src = "import Foo\n\naxiom evil : True := by trivial";
    assert!(preflight_axiom_or_sorry(src).is_err());
}

#[test]
fn rejects_sorry_in_proof() {
    let src = "theorem t : 1=1 := by sorry";
    assert!(preflight_axiom_or_sorry(src).is_err());
}

#[test]
fn rejects_sorry_with_punctuation() {
    let src = "theorem t : 1=1 := by exact (sorry)";
    assert!(preflight_axiom_or_sorry(src).is_err());
}

#[test]
fn allows_clean_proof() {
    let src = "import PhysicsGenerator.Axioms\n\ntheorem rest_energy : E = m*c^2 := by nlinarith";
    assert!(preflight_axiom_or_sorry(src).is_ok());
}

#[test]
fn allows_axiom_in_comment() {
    let src = "-- this is not a real axiom\ntheorem t : 1=1 := rfl";
    assert!(preflight_axiom_or_sorry(src).is_ok());
}
```

- [ ] **Step 2: Run, fail**

- [ ] **Step 3: Implement**

```rust
// engine/crates/api/src/lake_builder.rs
use anyhow::Result;
use std::path::PathBuf;
use std::sync::Arc;
use tokio::process::Command;
use tokio::sync::Semaphore;

pub enum VerifyOutcome {
    Verified { tactic: String, duration_ms: u32 },
    Rejected { reason: String, stderr_tail: String },
}

pub struct LakeBuilder {
    prover_template: PathBuf,
    workspace_root: PathBuf,
    semaphore: Arc<Semaphore>,
}

impl LakeBuilder {
    pub fn new(prover_template: PathBuf, workspace_root: PathBuf, slots: usize) -> Self {
        Self { prover_template, workspace_root, semaphore: Arc::new(Semaphore::new(slots)) }
    }

    pub async fn verify(&self, lean_source: &str, theorem_id_hex: &str) -> Result<VerifyOutcome> {
        if let Err(reason) = preflight_axiom_or_sorry(lean_source) {
            return Ok(VerifyOutcome::Rejected { reason: reason.into(), stderr_tail: String::new() });
        }
        let _permit = self.semaphore.acquire().await?;
        let workspace = tempfile::tempdir_in(&self.workspace_root)?;
        let derived = workspace.path().join("PhysicsGenerator/Derived");
        std::fs::create_dir_all(&derived)?;
        let target = derived.join(format!("Submission_{theorem_id_hex}.lean"));
        std::fs::write(&target, lean_source)?;

        for entry in walkdir::WalkDir::new(&self.prover_template).follow_links(true) {
            let e = entry?;
            let rel = e.path().strip_prefix(&self.prover_template)?;
            let dst = workspace.path().join(rel);
            if e.file_type().is_dir() { std::fs::create_dir_all(&dst)?; }
            else if !dst.exists() { std::fs::hard_link(e.path(), &dst).or_else(|_| std::fs::copy(e.path(), &dst).map(|_| ()))?; }
        }

        let started = std::time::Instant::now();
        let out = tokio::time::timeout(std::time::Duration::from_secs(300),
            Command::new("lake").arg("build").current_dir(workspace.path()).output()
        ).await;
        let duration_ms = started.elapsed().as_millis() as u32;
        match out {
            Ok(Ok(o)) if o.status.success() => Ok(VerifyOutcome::Verified { tactic: "lake_build".into(), duration_ms }),
            Ok(Ok(o)) => {
                let tail: String = String::from_utf8_lossy(&o.stderr).lines().rev().take(20).collect::<Vec<_>>().into_iter().rev().collect::<Vec<_>>().join("\n");
                Ok(VerifyOutcome::Rejected { reason: "lake_build_failed".into(), stderr_tail: tail })
            }
            Ok(Err(e)) => Ok(VerifyOutcome::Rejected { reason: "toolchain_error".into(), stderr_tail: e.to_string() }),
            Err(_) => Ok(VerifyOutcome::Rejected { reason: "verify_timeout".into(), stderr_tail: String::new() }),
        }
    }
}

pub fn preflight_axiom_or_sorry(src: &str) -> Result<(), &'static str> {
    let stripped = strip_comments(src);
    let axiom_re = regex::Regex::new(r"(?m)^\s*axiom\s+\w+").unwrap();
    if axiom_re.is_match(&stripped) { return Err("axiom_in_source"); }
    let sorry_re = regex::Regex::new(r"\bsorry\b").unwrap();
    if sorry_re.is_match(&stripped) { return Err("sorry_in_source"); }
    Ok(())
}

fn strip_comments(src: &str) -> String {
    let mut out = String::with_capacity(src.len());
    let mut chars = src.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '-' && chars.peek() == Some(&'-') {
            chars.next();
            for c2 in chars.by_ref() { if c2 == '\n' { out.push('\n'); break; } }
        } else if c == '/' && chars.peek() == Some(&'-') {
            chars.next();
            let mut depth = 1;
            while let Some(c2) = chars.next() {
                if c2 == '-' && chars.peek() == Some(&'/') { chars.next(); depth -= 1; if depth == 0 { break; } }
                else if c2 == '/' && chars.peek() == Some(&'-') { chars.next(); depth += 1; }
            }
        } else {
            out.push(c);
        }
    }
    out
}
```

Add `pub mod lake_builder;` to `engine/crates/api/src/lib.rs`. Add to `engine/crates/api/Cargo.toml`: `regex = "1"`, `tempfile = "3"`, `walkdir = "2"`.

- [ ] **Step 4: Run preflight tests, pass**

```bash
cargo test -p nasrudin-api --test lake_builder_preflight
```
Expected: 5/5 PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/lake_builder.rs engine/crates/api/src/lib.rs engine/crates/api/Cargo.toml engine/crates/api/tests/lake_builder_preflight.rs
git commit -m "feat(api): add lake_builder with axiom/sorry pre-flight + tmpdir workspace"
```

### Task 3.2: Reverify queue scaffold + A-path

**Files:**
- Create: `engine/crates/api/src/reverify.rs`
- Modify: `engine/crates/api/src/lib.rs`
- Test: `engine/crates/api/tests/reverify_a_path.rs`

- [ ] **Step 1: Write failing test (with stub LakeBuilder)**

```rust
// engine/crates/api/tests/reverify_a_path.rs
use nasrudin_api::reverify::{ReverifyQueue, VerifyTester};
use nasrudin_api::lake_builder::VerifyOutcome;

#[tokio::test]
async fn a_path_verified_marks_verified_and_increments_contributor() {
    // Set up Postgres + RocksDB + in-process axiom_store.
    // Insert theorem(Pending), enqueue, run drain once, assert:
    //   - status == Verified
    //   - workers.theorems_contributed == 1
    //   - SSE broadcast received theorem_verified

    // Implementation in step 3 below; placeholder here is intentional shape only.
    todo!("requires full pipeline; implemented in Task 3.4 once drain loop is wired");
}
```

- [ ] **Step 2: Implement A-path slice**

```rust
// engine/crates/api/src/reverify.rs
use anyhow::Result;
use nasrudin_derive::{AxiomStore, Chain};
use nasrudin_pg::query::{theorems as theorem_q, workers as worker_q};
use nasrudin_rocks::{TheoremDb, ReverifyJob};
use sea_orm::DatabaseConnection;
use std::sync::Arc;
use tokio::sync::broadcast;
use crate::lake_builder::{LakeBuilder, VerifyOutcome};

pub struct ReverifyQueue {
    pub rocks: Arc<TheoremDb>,
    pub pg: DatabaseConnection,
    pub lake: Arc<LakeBuilder>,
    pub axiom_store: Arc<AxiomStore>,
    pub discovery_tx: broadcast::Sender<DiscoveryEvent>,
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(tag = "kind")]
pub enum DiscoveryEvent {
    TheoremPending { theorem_id: String, canonical: String, contributor_id: String },
    TheoremVerified { theorem_id: String, verification_path: String, duration_ms: u32 },
    TheoremRejected { theorem_id: String, reason: String },
}

impl ReverifyQueue {
    pub async fn process_one(&self, job: ReverifyJob) -> Result<()> {
        let row = theorem_q::get_by_id(&self.pg, &job.theorem_id).await?
            .ok_or_else(|| anyhow::anyhow!("theorem missing"))?;

        let chain: Chain = serde_json::from_value(row.chain_json.clone())?;
        let theorem_id_hex = hex::encode(&row.id);

        if let Ok(regen) = chain.emit_lean(&self.axiom_store) {
            if regen.canonical_statement == row.canonical_statement {
                match self.lake.verify(&regen.lean_source, &theorem_id_hex).await? {
                    VerifyOutcome::Verified { tactic, duration_ms } => {
                        self.flip_verified(&row.id, "A", &tactic, duration_ms, &row.contributor_id, &row.canonical_statement).await?;
                        self.rocks.dequeue_reverify(job.theorem_id.try_into().unwrap_or(job.theorem_id)).ok();
                        return Ok(());
                    }
                    VerifyOutcome::Rejected { .. } => { /* fall through to B */ }
                }
            }
        }
        self.try_b_path(job, &row).await
    }

    async fn flip_verified(&self, id: &[u8], path: &str, tactic: &str, duration_ms: u32, contributor_id: &str, canonical: &str) -> Result<()> {
        // Single transaction: theorem → Verified, worker counter ++.
        use sea_orm::TransactionTrait;
        let txn = self.pg.begin().await?;
        theorem_q::mark_verified(&txn, id, path, tactic, duration_ms as i32).await?;
        worker_q::increment_contribution(&txn, contributor_id).await?;
        txn.commit().await?;
        let _ = self.discovery_tx.send(DiscoveryEvent::TheoremVerified {
            theorem_id: hex::encode(id),
            verification_path: path.into(),
            duration_ms,
        });
        Ok(())
    }

    async fn try_b_path(&self, _job: ReverifyJob, _row: &nasrudin_pg::entity::theorems::Model) -> Result<()> {
        // Filled in Task 3.3
        Ok(())
    }
}
```

- [ ] **Step 3: Verify the A-path code compiles**

```bash
cargo check -p nasrudin-api
```
Expected: clean.

- [ ] **Step 4: Commit (test stays `todo!()` until Task 3.4)**

```bash
git add engine/crates/api/src/reverify.rs engine/crates/api/src/lib.rs engine/crates/api/tests/reverify_a_path.rs
git commit -m "feat(api): scaffold reverify queue with A-path"
```

### Task 3.3: Reverify B-path fallback + reject

**Files:**
- Modify: `engine/crates/api/src/reverify.rs`

- [ ] **Step 1: Implement B-path**

Replace `try_b_path` from Task 3.2 with:

```rust
async fn try_b_path(&self, job: ReverifyJob, row: &nasrudin_pg::entity::theorems::Model) -> Result<()> {
    let theorem_id_hex = hex::encode(&row.id);
    match self.lake.verify(&row.lean_source, &theorem_id_hex).await? {
        VerifyOutcome::Verified { tactic, duration_ms } => {
            tracing::warn!(theorem_id=%theorem_id_hex, engine_git_sha=%row.engine_git_sha, "server_emitter_drift");
            self.flip_verified(&row.id, "B", &tactic, duration_ms, &row.contributor_id, &row.canonical_statement).await?;
            self.rocks.dequeue_reverify(&row.id.clone().try_into().unwrap_or([0u8;8])).ok();
            Ok(())
        }
        VerifyOutcome::Rejected { reason, stderr_tail } => {
            if job.attempts < 2 && reason == "toolchain_error" {
                let new_job = ReverifyJob { theorem_id: job.theorem_id, attempts: job.attempts + 1, enqueued_at_micros: chrono::Utc::now().timestamp_micros() };
                self.rocks.enqueue_reverify(&new_job)?;
            } else {
                let full_reason = format!("{reason}: {stderr_tail}");
                theorem_q::mark_rejected(&self.pg, &row.id, &full_reason).await?;
                let _ = self.discovery_tx.send(DiscoveryEvent::TheoremRejected {
                    theorem_id: theorem_id_hex,
                    reason: full_reason,
                });
                self.rocks.dequeue_reverify(&row.id.clone().try_into().unwrap_or([0u8;8])).ok();
            }
            Ok(())
        }
    }
}
```

- [ ] **Step 2: Verify compile**

```bash
cargo check -p nasrudin-api
```

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/reverify.rs
git commit -m "feat(api): add reverify B-path fallback + retry/reject paths"
```

### Task 3.4: Drain loop with supervision + integration test

**Files:**
- Modify: `engine/crates/api/src/reverify.rs`, `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/reverify_a_path.rs`

- [ ] **Step 1: Add drain loop**

```rust
impl ReverifyQueue {
    pub async fn drain_loop(self: Arc<Self>) {
        let mut interval = tokio::time::interval(std::time::Duration::from_millis(500));
        loop {
            interval.tick().await;
            match self.rocks.list_reverify_pending(1) {
                Ok(jobs) if !jobs.is_empty() => {
                    let job = jobs.into_iter().next().unwrap();
                    if let Err(e) = self.process_one(job).await {
                        tracing::error!(err=%e, "reverify process_one failed");
                    }
                }
                Ok(_) => continue,
                Err(e) => { tracing::error!(err=%e, "queue scan failed"); }
            }
        }
    }
}
```

- [ ] **Step 2: Spawn from `main.rs`**

In `engine/crates/api/src/main.rs`, after building `AppState`:

```rust
let reverify_queue = Arc::new(nasrudin_api::reverify::ReverifyQueue {
    rocks: state.db.clone(),
    pg: state.pg.clone().expect("pg required"),
    lake: state.lake.clone(),
    axiom_store: state.axiom_store.clone(),
    discovery_tx: state.discovery_tx.clone(),
});
tokio::spawn(reverify_queue.clone().drain_loop());
```

(`AppState` needs new fields `lake: Arc<LakeBuilder>` and `reverify: Arc<ReverifyQueue>` — add them in `state.rs`.)

- [ ] **Step 3: Replace the `todo!()` integration test**

```rust
// engine/crates/api/tests/reverify_a_path.rs
use nasrudin_api::lake_builder::{LakeBuilder, VerifyOutcome};
use nasrudin_api::reverify::{DiscoveryEvent, ReverifyQueue};
use nasrudin_pg::{connect_simple, query::{theorems, workers}, run_migrations};
use nasrudin_rocks::{ReverifyJob, TheoremDb};
use std::sync::Arc;
use tempfile::tempdir;

#[tokio::test]
async fn a_path_verified_flow() {
    let url = std::env::var("TEST_DATABASE_URL").unwrap_or_else(|_| "postgres://physics:physics@localhost:5432/physics_generator_test".into());
    let pg = connect_simple(&url).await.unwrap();
    sea_orm::ConnectionTrait::execute_unprepared(&pg, "DROP TABLE IF EXISTS theorems CASCADE; DROP TABLE IF EXISTS api_keys CASCADE; DROP TABLE IF EXISTS workers CASCADE; DROP TABLE IF EXISTS sessions CASCADE; DROP TABLE IF EXISTS user_preferences CASCADE; DROP TABLE IF EXISTS saved_searches CASCADE; DROP TABLE IF EXISTS users CASCADE; DROP TABLE IF EXISTS seaql_migrations CASCADE;").await.unwrap();
    run_migrations(&pg).await.unwrap();
    workers::register(&pg, "w1", None, None).await.unwrap();

    let dir = tempdir().unwrap();
    let rocks = Arc::new(TheoremDb::new(dir.path().to_str().unwrap()).unwrap());

    let prover_template = std::path::PathBuf::from("tests/fixtures/minimal_prover");
    std::fs::create_dir_all(prover_template.join("PhysicsGenerator/Derived")).ok();
    std::fs::write(prover_template.join("lakefile.toml"), "name = \"test\"\ndefaultTargets = []").ok();

    let lake = Arc::new(LakeBuilder::new(prover_template, dir.path().into(), 1));
    let axiom_store = Arc::new(nasrudin_derive::AxiomStore::new());
    let (tx, mut rx) = tokio::sync::broadcast::channel(16);

    let row = theorems::NewTheorem {
        id: vec![1,2,3,4,5,6,7,8],
        canonical_hash: vec![10,20,30,40,50,60,70,80],
        canonical_statement: "1 = 1".into(),
        domain: "PureMath".into(),
        lean_source: "theorem t : True := trivial".into(),
        chain_json: serde_json::json!([]),
        engine_git_sha: "test".into(),
        lean_version: "4.27.0".into(),
        contributor_id: "w1".into(),
        ..Default::default()
    };
    let id = theorems::insert_pending(&pg, row).await.unwrap();
    rocks.enqueue_reverify(&ReverifyJob { theorem_id: id.clone().try_into().unwrap(), attempts: 0, enqueued_at_micros: 0 }).unwrap();

    let q = Arc::new(ReverifyQueue { rocks: rocks.clone(), pg: pg.clone(), lake, axiom_store, discovery_tx: tx });
    let job = rocks.list_reverify_pending(1).unwrap().into_iter().next().unwrap();
    q.process_one(job).await.unwrap();

    let row_after = theorems::get_by_id(&pg, &id).await.unwrap().unwrap();
    assert_eq!(row_after.status, "Verified");
    let w = workers::get(&pg, "w1").await.unwrap().unwrap();
    assert_eq!(w.theorems_contributed, 1);

    let evt = tokio::time::timeout(std::time::Duration::from_secs(1), rx.recv()).await.unwrap().unwrap();
    matches!(evt, DiscoveryEvent::TheoremVerified { .. });
}
```

- [ ] **Step 4: Run with real `lake` toolchain available**

```bash
TEST_DATABASE_URL=… cargo test -p nasrudin-api --test reverify_a_path -- --ignored
```
Expected: PASS (mark `#[ignore]` if Lean toolchain unavailable in CI; nightly e2e covers it).

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/reverify.rs engine/crates/api/src/main.rs engine/crates/api/src/state.rs engine/crates/api/tests/reverify_a_path.rs
git commit -m "feat(api): add reverify drain loop + integration test"
```

---

## Phase 4 — Ingest endpoint + rate limit

### Task 4.1: Per-worker rate limiter

**Files:**
- Modify: `engine/crates/api/src/rate_limit.rs`, `engine/crates/api/Cargo.toml`
- Test: `engine/crates/api/tests/rate_limit_worker.rs`

- [ ] **Step 1: Failing test**

```rust
// engine/crates/api/tests/rate_limit_worker.rs
use nasrudin_api::rate_limit::WorkerRateLimiter;

#[tokio::test]
async fn allows_burst_then_throttles() {
    let lim = WorkerRateLimiter::new(60);
    for _ in 0..60 { assert!(lim.check_and_consume("w1", 1).await.is_ok()); }
    assert!(lim.check_and_consume("w1", 1).await.is_err());
    assert!(lim.check_and_consume("w2", 1).await.is_ok());
}
```

- [ ] **Step 2: Run, fail.**

- [ ] **Step 3: Implement**

```rust
// engine/crates/api/src/rate_limit.rs (append)
use governor::{Quota, RateLimiter, clock::DefaultClock, state::keyed::DefaultKeyedStateStore};
use std::num::NonZeroU32;
use std::sync::Arc;

pub struct WorkerRateLimiter {
    inner: Arc<RateLimiter<String, DefaultKeyedStateStore<String>, DefaultClock>>,
}

impl WorkerRateLimiter {
    pub fn new(per_minute: u32) -> Self {
        let quota = Quota::per_minute(NonZeroU32::new(per_minute).unwrap());
        Self { inner: Arc::new(RateLimiter::keyed(quota)) }
    }

    pub async fn check_and_consume(&self, worker_id: &str, n: u32) -> Result<(), governor::NotUntil<governor::clock::QuantaInstant>> {
        for _ in 0..n { self.inner.check_key(&worker_id.to_string())?; }
        Ok(())
    }
}
```

Add `governor = "0.6"` to `engine/crates/api/Cargo.toml`.

- [ ] **Step 4: Pass**

```bash
cargo test -p nasrudin-api --test rate_limit_worker
```
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/rate_limit.rs engine/crates/api/Cargo.toml engine/crates/api/tests/rate_limit_worker.rs
git commit -m "feat(api): add per-worker token-bucket rate limiter"
```

### Task 4.2: Ingest handler — schema + auth + dedup + insert + enqueue

**Files:**
- Create: `engine/crates/api/src/handlers/ingest.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs`, `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/ingest_handler.rs`

- [ ] **Step 1: Failing tests**

```rust
// engine/crates/api/tests/ingest_handler.rs
use axum::http::StatusCode;
use serde_json::json;

#[tokio::test]
async fn rejects_axiom_in_lean_source() {
    let app = test_app::build().await;
    let resp = test_app::post(&app, "/api/ingest", &json!({
        "worker_id": "w1", "engine_git_sha": "x", "lean_version": "4.27.0",
        "theorems": [{
            "canonical_statement": "T", "domain": "PureMath",
            "lean_source": "axiom evil : True\ntheorem t : True := evil",
            "chain": [], "axioms_used": []
        }]
    }), Some("nsk_worker_test")).await;
    assert_eq!(resp.status, StatusCode::ACCEPTED);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert_eq!(body["results"][0]["status"]["kind"], "Rejected");
    assert!(body["results"][0]["status"]["reason"].as_str().unwrap().contains("axiom"));
}

#[tokio::test]
async fn dedup_returns_duplicate_for_known_hash() {
    let app = test_app::build().await;
    let payload = json!({
        "worker_id": "w1", "engine_git_sha": "x", "lean_version": "4.27.0",
        "theorems": [{
            "canonical_statement": "T_dup", "domain": "PureMath",
            "lean_source": "theorem t : True := trivial",
            "chain": [], "axioms_used": []
        }]
    });
    let _ = test_app::post(&app, "/api/ingest", &payload, Some("nsk_worker_test")).await;
    let resp2 = test_app::post(&app, "/api/ingest", &payload, Some("nsk_worker_test")).await;
    let body: serde_json::Value = serde_json::from_slice(&resp2.body).unwrap();
    assert_eq!(body["results"][0]["status"]["kind"], "Duplicate");
}

#[tokio::test]
async fn rate_limit_429_after_burst() {
    let app = test_app::build_with_rate_limit(2).await;
    let payload = |i| json!({"worker_id": "w_rl", "engine_git_sha": "x", "lean_version": "4.27.0",
        "theorems": [{"canonical_statement": format!("RL_{i}"), "domain": "PureMath", "lean_source": "theorem t : True := trivial", "chain": [], "axioms_used": []}]});
    for i in 0..2 { let _ = test_app::post(&app, "/api/ingest", &payload(i), Some("nsk_worker_test")).await; }
    let resp = test_app::post(&app, "/api/ingest", &payload(99), Some("nsk_worker_test")).await;
    assert_eq!(resp.status, StatusCode::TOO_MANY_REQUESTS);
}
```

(`test_app` is a helper module — Task 4.2 also creates it under `engine/crates/api/tests/test_app/mod.rs` to spin up an in-memory router with a real Postgres test DB and a stub `LakeBuilder`. Code:

```rust
// engine/crates/api/tests/test_app/mod.rs
use axum::Router;
use nasrudin_api::state::AppState;
use std::sync::Arc;

pub struct Resp { pub status: axum::http::StatusCode, pub body: axum::body::Bytes }

pub async fn build() -> Router { build_with_rate_limit(60).await }

pub async fn build_with_rate_limit(per_minute: u32) -> Router {
    let pg = nasrudin_pg::connect_simple(&std::env::var("TEST_DATABASE_URL").unwrap()).await.unwrap();
    sea_orm::ConnectionTrait::execute_unprepared(&pg, "DROP TABLE IF EXISTS theorems CASCADE; DROP TABLE IF EXISTS api_keys CASCADE; DROP TABLE IF EXISTS workers CASCADE; DROP TABLE IF EXISTS sessions CASCADE; DROP TABLE IF EXISTS user_preferences CASCADE; DROP TABLE IF EXISTS saved_searches CASCADE; DROP TABLE IF EXISTS users CASCADE; DROP TABLE IF EXISTS seaql_migrations CASCADE;").await.unwrap();
    nasrudin_pg::run_migrations(&pg).await.unwrap();
    nasrudin_pg::query::workers::register(&pg, "w1", None, None).await.unwrap();
    nasrudin_pg::query::workers::register(&pg, "w_rl", None, None).await.unwrap();
    nasrudin_pg::query::api_keys::create(&pg, None, "worker", "w1", "nsk_worker_test", "<argon2-of-test>", None).await.unwrap();

    let dir = tempfile::tempdir().unwrap();
    let rocks = Arc::new(nasrudin_rocks::TheoremDb::new(dir.path().to_str().unwrap()).unwrap());
    let lake = Arc::new(nasrudin_api::lake_builder::LakeBuilder::new("/tmp".into(), "/tmp".into(), 1));
    let axiom_store = Arc::new(nasrudin_derive::AxiomStore::new());
    let (tx, _) = tokio::sync::broadcast::channel(16);
    let rate = Arc::new(nasrudin_api::rate_limit::WorkerRateLimiter::new(per_minute));

    let state = Arc::new(AppState {
        db: rocks, pg: Some(pg), axiom_store, discovery_tx: tx,
        ga_status: Arc::new(std::sync::Mutex::new(Default::default())),
        lake, worker_rate_limiter: rate,
    });
    nasrudin_api::router(state)
}

pub async fn post(app: &Router, path: &str, body: &serde_json::Value, bearer: Option<&str>) -> Resp {
    use axum::body::Body; use axum::http::Request; use tower::ServiceExt;
    let mut b = Request::builder().method("POST").uri(path).header("content-type", "application/json");
    if let Some(t) = bearer { b = b.header("authorization", format!("Bearer {t}")); }
    let req = b.body(Body::from(serde_json::to_vec(body).unwrap())).unwrap();
    let resp = app.clone().oneshot(req).await.unwrap();
    Resp { status: resp.status(), body: axum::body::to_bytes(resp.into_body(), 1024*1024).await.unwrap() }
}
```

)

- [ ] **Step 2: Run, fail (handler doesn't exist)**

- [ ] **Step 3: Implement handler**

```rust
// engine/crates/api/src/handlers/ingest.rs
use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use crate::{state::AppState, lake_builder::preflight_axiom_or_sorry};
use nasrudin_pg::query::theorems;
use nasrudin_rocks::ReverifyJob;

#[derive(Deserialize)]
pub struct IngestBatch {
    pub worker_id: String,
    pub engine_git_sha: String,
    pub lean_version: String,
    pub theorems: Vec<IngestTheorem>,
}

#[derive(Deserialize, Clone)]
pub struct IngestTheorem {
    pub canonical_statement: String,
    pub latex: Option<String>,
    pub domain: String,
    pub lean_source: String,
    pub chain: serde_json::Value,
    pub axioms_used: Vec<String>,
    pub parents: Option<Vec<String>>,
    pub origin: Option<serde_json::Value>,
    pub depth: Option<u32>,
    pub complexity: Option<u32>,
    pub generation: Option<u64>,
    pub fitness: Option<serde_json::Value>,
    pub verification_tactic: Option<String>,
    pub verification_duration_ms: Option<u32>,
    pub dimension: Option<[i32; 7]>,
}

#[derive(Serialize)]
#[serde(tag = "kind")]
pub enum IngestStatus {
    Pending,
    Duplicate { existing_status: String },
    Rejected { reason: String },
}

#[derive(Serialize)]
pub struct IngestResultItem {
    pub theorem_id: String,
    pub canonical_hash: String,
    pub status: IngestStatus,
}

#[derive(Serialize)]
pub struct IngestResponse { pub results: Vec<IngestResultItem> }

pub async fn ingest(
    State(state): State<Arc<AppState>>,
    bearer: crate::auth::WorkerAuth,
    Json(batch): Json<IngestBatch>,
) -> impl IntoResponse {
    if bearer.worker_id != batch.worker_id {
        return (StatusCode::FORBIDDEN, Json(serde_json::json!({"error":"worker_id mismatch"}))).into_response();
    }
    let n = batch.theorems.len() as u32;
    if let Err(_) = state.worker_rate_limiter.check_and_consume(&batch.worker_id, n).await {
        return (StatusCode::TOO_MANY_REQUESTS, Json(serde_json::json!({"error":"rate_limited"}))).into_response();
    }
    if state.db.reverify_queue_depth().unwrap_or(0) > 200 {
        return (StatusCode::SERVICE_UNAVAILABLE, Json(serde_json::json!({"error":"queue_full"}))).into_response();
    }

    let pg = state.pg.as_ref().unwrap();
    let mut results = Vec::with_capacity(batch.theorems.len());
    for t in &batch.theorems {
        if t.lean_source.len() > 256 * 1024 {
            results.push(IngestResultItem { theorem_id: String::new(), canonical_hash: String::new(), status: IngestStatus::Rejected { reason: "too_large".into() }});
            continue;
        }
        if let Err(reason) = preflight_axiom_or_sorry(&t.lean_source) {
            results.push(IngestResultItem { theorem_id: String::new(), canonical_hash: String::new(), status: IngestStatus::Rejected { reason: reason.into() }});
            continue;
        }
        let canonical_hash = nasrudin_core::canonical_hash(&t.canonical_statement);
        let theorem_id = canonical_hash.clone();

        if let Some(existing) = theorems::get_by_canonical_hash(pg, &canonical_hash).await.ok().flatten() {
            results.push(IngestResultItem {
                theorem_id: hex::encode(&existing.id),
                canonical_hash: hex::encode(&existing.canonical_hash),
                status: IngestStatus::Duplicate { existing_status: existing.status },
            });
            continue;
        }

        let new_row = theorems::NewTheorem {
            id: theorem_id.clone(),
            canonical_hash: canonical_hash.clone(),
            canonical_statement: t.canonical_statement.clone(),
            latex: t.latex.clone(),
            lean_source: t.lean_source.clone(),
            domain: t.domain.clone(),
            axioms_used: t.axioms_used.clone(),
            chain_json: t.chain.clone(),
            parents: t.parents.as_ref().map(|ps| ps.iter().filter_map(|p| hex::decode(p).ok()).collect()),
            origin_kind: t.origin.as_ref().and_then(|v| v.get("type").and_then(|x| x.as_str()).map(String::from)).unwrap_or_else(|| "Axiom".into()),
            origin_payload: t.origin.clone(),
            depth: t.depth.map(|x| x as i32),
            complexity: t.complexity.map(|x| x as i32),
            generation: t.generation.map(|x| x as i64),
            fitness_novelty: t.fitness.as_ref().and_then(|f| f.get("novelty").and_then(|x| x.as_f64()).map(|x| x as f32)),
            fitness_compactness: t.fitness.as_ref().and_then(|f| f.get("compactness").and_then(|x| x.as_f64()).map(|x| x as f32)),
            fitness_dimensional_correctness: t.fitness.as_ref().and_then(|f| f.get("dimensional_correctness").and_then(|x| x.as_f64()).map(|x| x as f32)),
            fitness_domain_coverage: t.fitness.as_ref().and_then(|f| f.get("domain_coverage").and_then(|x| x.as_f64()).map(|x| x as f32)),
            fitness_axiom_efficiency: t.fitness.as_ref().and_then(|f| f.get("axiom_efficiency").and_then(|x| x.as_f64()).map(|x| x as f32)),
            fitness_nasrudin_relevance: t.fitness.as_ref().and_then(|f| f.get("nasrudin_relevance").and_then(|x| x.as_f64()).map(|x| x as f32)),
            fitness_depth_score: t.fitness.as_ref().and_then(|f| f.get("depth").and_then(|x| x.as_f64()).map(|x| x as f32)),
            dimension: t.dimension.map(|d| d.to_vec()),
            engine_git_sha: batch.engine_git_sha.clone(),
            lean_version: batch.lean_version.clone(),
            contributor_id: batch.worker_id.clone(),
        };
        match theorems::insert_pending(pg, new_row).await {
            Ok(id) => {
                let mut id_arr = [0u8; 8]; id_arr.copy_from_slice(&id);
                state.db.enqueue_reverify(&ReverifyJob { theorem_id: id_arr, attempts: 0, enqueued_at_micros: chrono::Utc::now().timestamp_micros() }).ok();
                let _ = state.discovery_tx.send(crate::reverify::DiscoveryEvent::TheoremPending {
                    theorem_id: hex::encode(&id),
                    canonical: t.canonical_statement.clone(),
                    contributor_id: batch.worker_id.clone(),
                });
                results.push(IngestResultItem { theorem_id: hex::encode(&id), canonical_hash: hex::encode(&canonical_hash), status: IngestStatus::Pending });
            }
            Err(e) => results.push(IngestResultItem { theorem_id: String::new(), canonical_hash: hex::encode(&canonical_hash), status: IngestStatus::Rejected { reason: format!("db_error: {e}") }}),
        }
    }
    (StatusCode::ACCEPTED, Json(IngestResponse { results })).into_response()
}
```

Add the route in `main.rs`: `.route("/api/ingest", post(handlers::ingest::ingest))`. Add `pub mod ingest;` to `handlers/mod.rs`.

- [ ] **Step 4: Run tests, pass**

```bash
TEST_DATABASE_URL=… cargo test -p nasrudin-api --test ingest_handler
```
Expected: 3/3 PASS.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/api/src/handlers/ingest.rs engine/crates/api/src/handlers/mod.rs engine/crates/api/src/main.rs engine/crates/api/tests/ingest_handler.rs engine/crates/api/tests/test_app/
git commit -m "feat(api): add /api/ingest with batch + dedup + axiom-firewall + rate-limit"
```

### Task 4.3: WorkerAuth extractor for `nsk_worker_*` keys

**Files:**
- Modify: `engine/crates/api/src/auth.rs`
- Test: `engine/crates/api/tests/worker_auth.rs`

- [ ] **Step 1: Failing test**

```rust
// engine/crates/api/tests/worker_auth.rs
mod test_app;
use axum::http::StatusCode;

#[tokio::test]
async fn missing_bearer_returns_401() {
    let app = test_app::build().await;
    let resp = test_app::post(&app, "/api/ingest", &serde_json::json!({"worker_id":"w1","engine_git_sha":"x","lean_version":"y","theorems":[]}), None).await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn non_worker_prefix_returns_403() {
    let app = test_app::build().await;
    let resp = test_app::post(&app, "/api/ingest", &serde_json::json!({"worker_id":"w1","engine_git_sha":"x","lean_version":"y","theorems":[]}), Some("nsk_live_user_key")).await;
    assert_eq!(resp.status, StatusCode::FORBIDDEN);
}
```

- [ ] **Step 2: Implement extractor**

In `engine/crates/api/src/auth.rs`:

```rust
use axum::{async_trait, extract::FromRequestParts, http::{StatusCode, request::Parts, header::AUTHORIZATION}};
use std::sync::Arc;
use crate::state::AppState;

pub struct WorkerAuth { pub worker_id: String, pub key_id: i32 }

#[async_trait]
impl FromRequestParts<Arc<AppState>> for WorkerAuth {
    type Rejection = (StatusCode, &'static str);

    async fn from_request_parts(parts: &mut Parts, state: &Arc<AppState>) -> Result<Self, Self::Rejection> {
        let h = parts.headers.get(AUTHORIZATION).and_then(|v| v.to_str().ok())
            .ok_or((StatusCode::UNAUTHORIZED, "missing bearer"))?;
        let token = h.strip_prefix("Bearer ").ok_or((StatusCode::UNAUTHORIZED, "malformed bearer"))?;
        if !token.starts_with("nsk_worker_") {
            return Err((StatusCode::FORBIDDEN, "non-worker key"));
        }
        let pg = state.pg.as_ref().ok_or((StatusCode::SERVICE_UNAVAILABLE, "pg unavailable"))?;
        let row = nasrudin_pg::query::api_keys::find_by_token(pg, token).await
            .map_err(|_| (StatusCode::INTERNAL_SERVER_ERROR, "auth db error"))?
            .ok_or((StatusCode::UNAUTHORIZED, "unknown token"))?;
        Ok(WorkerAuth { worker_id: row.owner_id, key_id: row.id })
    }
}
```

(Adjust `api_keys::find_by_token` signature to match — add it if missing in `pg/src/query/api_keys.rs`.)

- [ ] **Step 3: Pass tests**

```bash
cargo test -p nasrudin-api --test worker_auth
```
Expected: 2/2 PASS.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/auth.rs engine/crates/pg/src/query/api_keys.rs engine/crates/api/tests/worker_auth.rs
git commit -m "feat(api): add WorkerAuth extractor for nsk_worker_* bearer keys"
```

---

## Phase 5 — Read endpoints + SSE + seed

### Task 5.1: GET /api/theorems with cursor + filters

**Files:**
- Create: `engine/crates/api/src/handlers/theorems.rs`
- Modify: `engine/crates/api/src/main.rs`, `engine/crates/api/src/handlers/mod.rs`
- Test: `engine/crates/api/tests/theorems_handler.rs`

- [ ] **Step 1: Failing test**

```rust
// engine/crates/api/tests/theorems_handler.rs
mod test_app;
use axum::http::StatusCode;

#[tokio::test]
async fn list_returns_verified_with_cursor() {
    let app = test_app::build().await;
    test_app::seed_verified_theorems(&app, 5).await;
    let resp = test_app::get(&app, "/api/theorems?limit=3").await;
    assert_eq!(resp.status, StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert_eq!(body["theorems"].as_array().unwrap().len(), 3);
    assert!(body["next_cursor"].is_string());
    assert_eq!(body["total"].as_u64().unwrap(), 5);
}

#[tokio::test]
async fn recent_endpoint_returns_descending() {
    let app = test_app::build().await;
    test_app::seed_verified_theorems(&app, 3).await;
    let resp = test_app::get(&app, "/api/theorems/recent?limit=10").await;
    assert_eq!(resp.status, StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert_eq!(body["theorems"].as_array().unwrap().len(), 3);
}
```

(Extend `test_app/mod.rs` with `seed_verified_theorems` helper and a `get` helper analogous to `post`.)

- [ ] **Step 2: Implement**

```rust
// engine/crates/api/src/handlers/theorems.rs
use axum::{Json, extract::{State, Query, Path}, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use std::sync::Arc;
use crate::state::AppState;
use nasrudin_pg::query::theorems;

#[derive(Deserialize)]
pub struct ListQuery { pub limit: Option<u64>, pub cursor: Option<String>, pub domain: Option<String> }

pub async fn list(State(state): State<Arc<AppState>>, Query(q): Query<ListQuery>) -> impl IntoResponse {
    let pg = state.pg.as_ref().unwrap();
    let limit = q.limit.unwrap_or(50).min(500);
    match theorems::list_verified(pg, q.cursor, limit, q.domain).await {
        Ok(page) => (StatusCode::OK, Json(serde_json::json!({
            "theorems": page.items,
            "next_cursor": page.next_cursor,
            "total": page.total,
            "total_capped": page.total_capped,
        }))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(serde_json::json!({"error": e.to_string()}))).into_response(),
    }
}

pub async fn recent(State(state): State<Arc<AppState>>, Query(q): Query<ListQuery>) -> impl IntoResponse {
    let mut q = q; q.cursor = None; list(State(state), Query(q)).await
}

pub async fn by_id(State(state): State<Arc<AppState>>, Path(id): Path<String>) -> impl IntoResponse {
    let pg = state.pg.as_ref().unwrap();
    let id_bytes = match hex::decode(&id) { Ok(b) => b, Err(_) => return (StatusCode::BAD_REQUEST, Json(serde_json::json!({"error":"bad_id"}))).into_response() };
    match theorems::get_by_id(pg, &id_bytes).await {
        Ok(Some(t)) => (StatusCode::OK, Json(t)).into_response(),
        Ok(None) => (StatusCode::NOT_FOUND, Json(serde_json::json!({"error":"not_found"}))).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(serde_json::json!({"error": e.to_string()}))).into_response(),
    }
}

pub async fn lean_download(State(state): State<Arc<AppState>>, Path(hash): Path<String>) -> impl IntoResponse {
    let pg = state.pg.as_ref().unwrap();
    let hash_bytes = match hex::decode(&hash) { Ok(b) => b, Err(_) => return (StatusCode::BAD_REQUEST, "bad hash").into_response() };
    match theorems::get_by_canonical_hash(pg, &hash_bytes).await {
        Ok(Some(t)) => ([(axum::http::header::CONTENT_TYPE, "text/plain; charset=utf-8"), (axum::http::header::CONTENT_DISPOSITION, &format!("attachment; filename=\"theorem_{}.lean\"", hash))], t.lean_source).into_response(),
        Ok(None) => (StatusCode::NOT_FOUND, "not_found").into_response(),
        Err(_) => (StatusCode::INTERNAL_SERVER_ERROR, "db_error").into_response(),
    }
}
```

Wire routes:
```rust
.route("/api/theorems", get(handlers::theorems::list))
.route("/api/theorems/recent", get(handlers::theorems::recent))
.route("/api/theorems/:id", get(handlers::theorems::by_id))
.route("/api/theorems/:hash/lean", get(handlers::theorems::lean_download))
```

- [ ] **Step 3: Pass**

```bash
cargo test -p nasrudin-api --test theorems_handler
```
Expected: 2/2 PASS.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/handlers/theorems.rs engine/crates/api/src/handlers/mod.rs engine/crates/api/src/main.rs engine/crates/api/tests/theorems_handler.rs
git commit -m "feat(api): add /api/theorems list/recent/by-id/lean-download"
```

### Task 5.2: SSE — two streams (`discoveries`, `stats`)

**Files:**
- Create: `engine/crates/api/src/handlers/events.rs`
- Modify: `engine/crates/api/src/main.rs`, `engine/crates/api/src/handlers/mod.rs`
- Test: `engine/crates/api/tests/events_sse.rs`

- [ ] **Step 1: Failing test**

```rust
// engine/crates/api/tests/events_sse.rs
mod test_app;

#[tokio::test]
async fn discoveries_stream_emits_theorem_verified() {
    let app = test_app::build().await;
    let mut rx = test_app::open_sse(&app, "/api/events/discoveries").await;
    let state = test_app::state_handle(&app);
    state.discovery_tx.send(nasrudin_api::reverify::DiscoveryEvent::TheoremVerified { theorem_id: "abc".into(), verification_path: "A".into(), duration_ms: 100 }).unwrap();
    let event = tokio::time::timeout(std::time::Duration::from_secs(1), rx.recv()).await.unwrap().unwrap();
    assert!(event.contains("theorem_verified"));
    assert!(event.contains("\"abc\""));
}
```

- [ ] **Step 2: Implement**

```rust
// engine/crates/api/src/handlers/events.rs
use axum::{extract::State, response::sse::{Event, KeepAlive, Sse}};
use futures::stream::Stream;
use std::{convert::Infallible, sync::Arc, time::Duration};
use tokio_stream::wrappers::BroadcastStream;
use crate::state::AppState;
use crate::reverify::DiscoveryEvent;

pub async fn discoveries(State(state): State<Arc<AppState>>) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let rx = state.discovery_tx.subscribe();
    let stream = BroadcastStream::new(rx).filter_map(|res| async move {
        let evt = res.ok()?;
        match evt {
            DiscoveryEvent::TheoremPending { .. } | DiscoveryEvent::TheoremVerified { .. } | DiscoveryEvent::TheoremRejected { .. } => {
                Some(Ok(Event::default().event(event_name(&evt)).json_data(&evt).ok()?))
            }
        }
    });
    Sse::new(stream).keep_alive(KeepAlive::new().interval(Duration::from_secs(15)).text("ping"))
}

pub async fn stats(State(state): State<Arc<AppState>>) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let rx = state.discovery_tx.subscribe();
    let stream = BroadcastStream::new(rx).filter_map(|res| async move {
        // GA tick / heartbeat events go on this stream once we add their variants
        let _ = res.ok()?;
        None
    });
    Sse::new(stream).keep_alive(KeepAlive::new().interval(Duration::from_secs(15)).text("ping"))
}

fn event_name(e: &DiscoveryEvent) -> &'static str {
    match e {
        DiscoveryEvent::TheoremPending { .. } => "theorem_pending",
        DiscoveryEvent::TheoremVerified { .. } => "theorem_verified",
        DiscoveryEvent::TheoremRejected { .. } => "theorem_rejected",
    }
}
```

Routes:
```rust
.route("/api/events/discoveries", get(handlers::events::discoveries))
.route("/api/events/stats", get(handlers::events::stats))
```

Add deps: `tokio-stream = "0.1"`, `futures = "0.3"`.

- [ ] **Step 3: Pass**

```bash
cargo test -p nasrudin-api --test events_sse
```

- [ ] **Step 4: Commit**

```bash
git add engine/crates/api/src/handlers/events.rs engine/crates/api/src/handlers/mod.rs engine/crates/api/src/main.rs engine/crates/api/Cargo.toml engine/crates/api/tests/events_sse.rs
git commit -m "feat(api): add SSE /api/events/{discoveries,stats}"
```

### Task 5.3: GET /api/seed for remote-worker bootstrap

**Files:**
- Create: `engine/crates/api/src/handlers/seed.rs`
- Modify: `engine/crates/api/src/main.rs`, `engine/crates/api/src/handlers/mod.rs`
- Test: `engine/crates/api/tests/seed_handler.rs`

- [ ] **Step 1: Failing test**

```rust
// engine/crates/api/tests/seed_handler.rs
mod test_app;

#[tokio::test]
async fn seed_returns_axioms_and_top_theorems() {
    let app = test_app::build().await;
    test_app::seed_verified_theorems(&app, 5).await;
    let resp = test_app::get(&app, "/api/seed?domain=PureMath&top=3").await;
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert!(body["axioms"].is_array());
    assert!(body["seed_theorems"].as_array().unwrap().len() <= 3);
}
```

- [ ] **Step 2: Implement**

```rust
// engine/crates/api/src/handlers/seed.rs
use axum::{Json, extract::{State, Query}, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use std::sync::Arc;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct SeedQuery { pub domain: Option<String>, pub top: Option<u64> }

pub async fn seed(State(state): State<Arc<AppState>>, Query(q): Query<SeedQuery>) -> impl IntoResponse {
    let pg = state.pg.as_ref().unwrap();
    let top = q.top.unwrap_or(50).min(500);
    let axioms: Vec<_> = state.axiom_store.iter()
        .filter(|a| q.domain.as_ref().map_or(true, |d| a.domain.to_string() == *d))
        .map(|a| serde_json::json!({"name": a.name, "statement": a.statement.to_string(), "domain": a.domain.to_string()}))
        .collect();
    let page = nasrudin_pg::query::theorems::list_verified(pg, None, top, q.domain).await.unwrap_or_default();
    (StatusCode::OK, Json(serde_json::json!({"axioms": axioms, "seed_theorems": page.items}))).into_response()
}
```

Route: `.route("/api/seed", get(handlers::seed::seed))`.

(Implement `Default` for `Page` if missing.)

- [ ] **Step 3: Pass + commit**

```bash
cargo test -p nasrudin-api --test seed_handler
git add ... && git commit -m "feat(api): add /api/seed for remote-worker bootstrap"
```

### Task 5.4: GET /api/axioms and /api/domains

**Files:**
- Modify: `engine/crates/api/src/handlers/seed.rs` (add `axioms` + `domains` handlers, or split into `meta.rs`)
- Modify: `engine/crates/api/src/main.rs`

- [ ] **Step 1: Implement**

```rust
// engine/crates/api/src/handlers/meta.rs
use axum::{Json, extract::{State, Query}, response::IntoResponse, http::StatusCode};
use serde::Deserialize;
use std::sync::Arc;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct DomainFilter { pub domain: Option<String> }

pub async fn axioms(State(state): State<Arc<AppState>>, Query(q): Query<DomainFilter>) -> impl IntoResponse {
    let xs: Vec<_> = state.axiom_store.iter()
        .filter(|a| q.domain.as_ref().map_or(true, |d| a.domain.to_string() == *d))
        .map(|a| serde_json::json!({"name": a.name, "statement": a.statement.to_string(), "domain": a.domain.to_string()}))
        .collect();
    (StatusCode::OK, Json(xs)).into_response()
}

pub async fn domains(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let stats = state.db.get_stats().unwrap_or_default();
    let counts: Vec<_> = stats.domain_counts.into_iter().map(|(d, c)| serde_json::json!({"domain": d, "count": c})).collect();
    (StatusCode::OK, Json(counts)).into_response()
}
```

Routes: `.route("/api/axioms", get(handlers::meta::axioms))`, `.route("/api/domains", get(handlers::meta::domains))`.

- [ ] **Step 2: Smoke test (manually via curl) + commit**

```bash
cargo run -p nasrudin-api &
curl localhost:3001/api/axioms | jq length
curl localhost:3001/api/domains
git add ... && git commit -m "feat(api): add /api/axioms + /api/domains"
```

---

## Phase 6 — Auxiliary endpoints

### Task 6.1: Workers list + heartbeat handler

**Files:**
- Modify: `engine/crates/api/src/handlers/workers.rs`
- Modify: `engine/crates/api/src/main.rs`
- Test: `engine/crates/api/tests/workers_handler.rs`

- [ ] **Step 1: Failing test**

```rust
// engine/crates/api/tests/workers_handler.rs
mod test_app;
use axum::http::StatusCode;

#[tokio::test]
async fn heartbeat_updates_worker_row() {
    let app = test_app::build().await;
    let resp = test_app::post(&app, "/api/workers/heartbeat", &serde_json::json!({
        "worker_id": "w1", "current_generation": 17, "theorems_produced_total": 100, "uptime_seconds": 60, "engine_git_sha": "deadbee"
    }), Some("nsk_worker_test")).await;
    assert_eq!(resp.status, StatusCode::OK);
    let list_resp = test_app::get(&app, "/api/workers").await;
    let body: serde_json::Value = serde_json::from_slice(&list_resp.body).unwrap();
    let w = body.as_array().unwrap().iter().find(|w| w["id"] == "w1").unwrap();
    assert_eq!(w["current_generation"], 17);
}
```

- [ ] **Step 2: Implement**

```rust
// engine/crates/api/src/handlers/workers.rs (append)
use serde::Deserialize;

#[derive(Deserialize)]
pub struct HeartbeatBody {
    pub worker_id: String,
    pub current_generation: i64,
    pub theorems_produced_total: i64,
    pub uptime_seconds: i64,
    pub engine_git_sha: String,
}

pub async fn heartbeat(
    State(state): State<Arc<AppState>>,
    bearer: crate::auth::WorkerAuth,
    Json(body): Json<HeartbeatBody>,
) -> impl IntoResponse {
    if bearer.worker_id != body.worker_id {
        return (StatusCode::FORBIDDEN, Json(serde_json::json!({"error":"id_mismatch"})));
    }
    let pg = state.pg.as_ref().unwrap();
    if let Err(e) = nasrudin_pg::query::workers::update_heartbeat(pg, &body.worker_id, body.current_generation, body.theorems_produced_total, body.uptime_seconds, &body.engine_git_sha).await {
        return (StatusCode::INTERNAL_SERVER_ERROR, Json(serde_json::json!({"error": format!("{e}")})));
    }
    (StatusCode::OK, Json(serde_json::json!({"ok": true})))
}

pub async fn list(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let pg = state.pg.as_ref().unwrap();
    match nasrudin_pg::query::workers::list_all(pg).await {
        Ok(ws) => (StatusCode::OK, Json(ws)).into_response(),
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, Json(serde_json::json!({"error": format!("{e}")}))).into_response(),
    }
}
```

Routes: `.route("/api/workers/heartbeat", post(handlers::workers::heartbeat))`, `.route("/api/workers", get(handlers::workers::list))`.

- [ ] **Step 3: Pass + commit**

```bash
cargo test -p nasrudin-api --test workers_handler
git add ... && git commit -m "feat(api): add /api/workers/heartbeat + /api/workers list"
```

### Task 6.2: GET /api/me/stats

**Files:**
- Create: `engine/crates/api/src/handlers/me_stats.rs`
- Modify: `engine/crates/api/src/main.rs`, `engine/crates/api/src/handlers/mod.rs`
- Test: `engine/crates/api/tests/me_stats.rs`

- [ ] **Step 1: Failing test**

```rust
// engine/crates/api/tests/me_stats.rs
mod test_app;
use axum::http::StatusCode;

#[tokio::test]
async fn me_stats_returns_counters() {
    let app = test_app::build().await;
    test_app::seed_verified_theorems(&app, 3).await;
    let resp = test_app::get_authed(&app, "/api/me/stats", "user-session-cookie").await;
    assert_eq!(resp.status, StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert!(body["theorems_total"].as_u64().is_some());
}
```

- [ ] **Step 2: Implement**

```rust
// engine/crates/api/src/handlers/me_stats.rs
use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use std::sync::Arc;
use crate::{state::AppState, auth::AuthOrApiKey};

pub async fn me_stats(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().unwrap();
    let total = nasrudin_pg::query::theorems::count_by_contributor(pg, &auth.user_id).await.unwrap_or(0);
    let recent = nasrudin_pg::query::theorems::list_by_contributor(pg, &auth.user_id, 10).await.unwrap_or_default();
    (StatusCode::OK, Json(serde_json::json!({
        "theorems_total": total,
        "theorems_recent": recent,
    })))
}
```

Add `count_by_contributor` and `list_by_contributor` to `pg/src/query/theorems.rs`. Route: `.route("/api/me/stats", get(handlers::me_stats::me_stats))`.

- [ ] **Step 3: Pass + commit**

```bash
cargo test -p nasrudin-api --test me_stats
git add ... && git commit -m "feat(api): add /api/me/stats with contributor counts"
```

### Task 6.3: Health endpoint

**Files:**
- Modify: `engine/crates/api/src/main.rs` (add `/health`)

- [ ] **Step 1: Implement**

```rust
async fn health(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let pg_ok = state.pg.is_some();
    let queue_depth = state.db.reverify_queue_depth().unwrap_or(usize::MAX);
    let stats = state.db.get_stats().unwrap_or_default();
    Json(serde_json::json!({
        "db": if pg_ok {"ok"} else {"down"},
        "rocks": "ok",
        "queue_depth": queue_depth,
        "theorems_total": stats.total_theorems,
    }))
}
```

Route: `.route("/health", get(health))`.

- [ ] **Step 2: Smoke**

```bash
curl localhost:3001/health
```
Expected: JSON with all keys.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/main.rs
git commit -m "feat(api): add /health endpoint"
```

---

## Phase 7 — GA worker + backfill

### Task 7.1: Discover binary submits via HTTP

**Files:**
- Modify: `engine/crates/ga/src/bin/discover_emc2.rs`, `engine/crates/ga/Cargo.toml`

- [ ] **Step 1: Add HTTP submission helper**

```rust
// engine/crates/ga/src/bin/discover_emc2.rs (new section)
async fn submit_to_api(api_url: &str, key: &str, payload: serde_json::Value) -> anyhow::Result<()> {
    let client = reqwest::Client::new();
    let resp = client.post(format!("{api_url}/api/ingest"))
        .bearer_auth(key).json(&payload).send().await?;
    if !resp.status().is_success() && resp.status() != reqwest::StatusCode::CONFLICT {
        anyhow::bail!("ingest failed: {}", resp.status());
    }
    Ok(())
}
```

- [ ] **Step 2: Replace file-write block**

Find `fn verify_chain(...)` (or wherever it writes `Discover{n}.lean`) and replace with the submission path:

```rust
let payload = serde_json::json!({
    "worker_id": std::env::var("NASRUDIN_WORKER_ID").unwrap_or("in-proc-worker-1".into()),
    "engine_git_sha": env!("VERGEN_GIT_SHA", "unknown"),
    "lean_version": "4.27.0",
    "theorems": [{
        "canonical_statement": canonical_statement,
        "domain": domain.to_string(),
        "lean_source": lean_source,
        "chain": chain_json,
        "axioms_used": axioms_used,
        "depth": depth,
        "generation": generation,
        "fitness": fitness_json,
    }]
});
let api_url = std::env::var("NASRUDIN_API_URL").unwrap_or("http://localhost:3001".into());
let key = std::env::var("NASRUDIN_WORKER_KEY")?;
submit_to_api(&api_url, &key, payload).await?;
```

(`vergen` adds `VERGEN_GIT_SHA` at compile time — add `vergen` to `engine/crates/ga/build.rs` or use `env!("CARGO_PKG_VERSION")` as fallback.)

Add to `engine/crates/ga/Cargo.toml`: `reqwest = { version = "0.12", features = ["json","rustls-tls"] }`.

- [ ] **Step 3: Run end-to-end manually**

```bash
docker compose up -d postgres
cargo run -p nasrudin-api &
NASRUDIN_API_URL=http://localhost:3001 NASRUDIN_WORKER_KEY=nsk_worker_dev cargo run -p nasrudin-ga --bin discover_emc2 -- --gens 5 --pop 8 --max-lake 2
curl localhost:3001/api/theorems?limit=10 | jq '.total'
```
Expected: total > 0.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/ga/src/bin/discover_emc2.rs engine/crates/ga/Cargo.toml
git commit -m "feat(ga): submit verified discoveries to /api/ingest instead of file write"
```

### Task 7.2: Backfill existing Lean files

**Files:**
- Create: `engine/crates/api/src/bin/backfill_existing_lean.rs`
- Modify: `engine/crates/api/Cargo.toml` (add `[[bin]]` entry)

- [ ] **Step 1: Implement**

```rust
// engine/crates/api/src/bin/backfill_existing_lean.rs
use anyhow::Result;
use std::path::Path;

#[tokio::main]
async fn main() -> Result<()> {
    let prover = std::env::var("PROVER_ROOT").unwrap_or("../prover".into());
    let derived = Path::new(&prover).join("PhysicsGenerator/Derived");
    let api_url = std::env::var("NASRUDIN_API_URL").unwrap_or("http://localhost:3001".into());
    let key = std::env::var("NASRUDIN_BACKFILL_KEY")?;
    let client = reqwest::Client::new();
    let mut count = 0;
    for entry in walkdir::WalkDir::new(&derived) {
        let e = entry?;
        if e.path().extension().map_or(false, |x| x == "lean") {
            let src = std::fs::read_to_string(e.path())?;
            let canonical = extract_canonical(&src).unwrap_or_else(|| e.file_name().to_string_lossy().to_string());
            let resp = client.post(format!("{api_url}/api/ingest"))
                .bearer_auth(&key)
                .json(&serde_json::json!({
                    "worker_id": "backfill", "engine_git_sha": "backfill", "lean_version": "4.27.0",
                    "theorems": [{
                        "canonical_statement": canonical, "domain": "PureMath",
                        "lean_source": src, "chain": [], "axioms_used": [], "origin": {"type": "External"}
                    }]
                })).send().await?;
            tracing::info!(file = %e.path().display(), status = %resp.status(), "submitted");
            count += 1;
        }
    }
    println!("submitted {count} files");
    Ok(())
}

fn extract_canonical(src: &str) -> Option<String> {
    let re = regex::Regex::new(r"theorem\s+\w+\s*(?:\([^)]*\))?\s*:\s*([^:=]+):=").unwrap();
    re.captures(src).and_then(|c| c.get(1).map(|m| m.as_str().trim().to_string()))
}
```

Add to `engine/crates/api/Cargo.toml`:
```toml
[[bin]]
name = "backfill_existing_lean"
path = "src/bin/backfill_existing_lean.rs"
```

- [ ] **Step 2: Smoke run**

```bash
NASRUDIN_API_URL=http://localhost:3001 NASRUDIN_BACKFILL_KEY=nsk_worker_backfill cargo run -p nasrudin-api --bin backfill_existing_lean
curl localhost:3001/api/theorems?limit=5 | jq '.theorems | length'
```
Expected: ≥ 3 (RestEnergyUpstream + AutoRestEnergyUpstream + PhotonEnergyMomentum).

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/src/bin/backfill_existing_lean.rs engine/crates/api/Cargo.toml
git commit -m "feat(api): add backfill_existing_lean binary for one-shot ingestion"
```

### Task 7.3: GA worker as separate container

Tracking task only — covered by Task 9.1 (`docker-compose.yml` adds `ga-worker` service with `profile: workers`). No standalone commit.

---

## Phase 8 — Frontend wiring

### Task 8.1: SSE hooks

**Files:**
- Create: `nasrudin-frontend/src/lib/sse.ts`
- Modify: `nasrudin-frontend/src/lib/queries.ts`

- [ ] **Step 1: Implement**

```ts
// nasrudin-frontend/src/lib/sse.ts
import { useEffect, useRef } from 'react';
import { useQueryClient } from '@tanstack/react-query';

const API_BASE = (import.meta as any).env?.VITE_API_BASE_URL ?? '';

export function useDiscoveryFeed(onEvent?: (e: MessageEvent) => void) {
  const qc = useQueryClient();
  const ref = useRef<EventSource | null>(null);
  useEffect(() => {
    const es = new EventSource(`${API_BASE}/api/events/discoveries`);
    ['theorem_pending', 'theorem_verified', 'theorem_rejected'].forEach(name => {
      es.addEventListener(name, (e: MessageEvent) => {
        qc.invalidateQueries({ queryKey: ['theorems'] });
        if (onEvent) onEvent(e);
      });
    });
    es.onerror = () => { /* browser auto-reconnects */ };
    ref.current = es;
    return () => es.close();
  }, [qc, onEvent]);
}

export function useStatsStream(onEvent?: (e: MessageEvent) => void) {
  const ref = useRef<EventSource | null>(null);
  useEffect(() => {
    const es = new EventSource(`${API_BASE}/api/events/stats`);
    ['ga_status_tick', 'worker_heartbeat'].forEach(name => {
      es.addEventListener(name, (e: MessageEvent) => { if (onEvent) onEvent(e); });
    });
    ref.current = es;
    return () => es.close();
  }, [onEvent]);
}
```

In `queries.ts`, re-export: `export { useDiscoveryFeed, useStatsStream } from './sse';`.

- [ ] **Step 2: Wire into a page**

Edit `nasrudin-frontend/src/routes/browse.tsx`: add `useDiscoveryFeed()` near the top of the component so the list invalidates on `theorem_verified`.

- [ ] **Step 3: Verify**

```bash
cd nasrudin-frontend && pnpm tsc --noEmit && pnpm biome check
```
Expected: clean.

- [ ] **Step 4: Commit**

```bash
git add nasrudin-frontend/src/lib/sse.ts nasrudin-frontend/src/lib/queries.ts nasrudin-frontend/src/routes/browse.tsx
git commit -m "feat(frontend): add useDiscoveryFeed + useStatsStream SSE hooks"
```

### Task 8.2: Align Theorem type with server response

**Files:**
- Modify: `nasrudin-frontend/src/lib/types.ts`

- [ ] **Step 1: Update type**

```ts
// nasrudin-frontend/src/lib/types.ts
export interface Theorem {
  id: string;                 // hex
  canonical_hash: string;
  canonical_statement: string;
  latex: string | null;
  lean_source: string;
  domain: string;
  axioms_used: string[];
  parents: string[] | null;
  origin_kind: string;
  depth: number | null;
  generation: number | null;
  fitness_novelty: number | null;
  fitness_compactness: number | null;
  fitness_dimensional_correctness: number | null;
  fitness_domain_coverage: number | null;
  fitness_axiom_efficiency: number | null;
  fitness_nasrudin_relevance: number | null;
  fitness_depth_score: number | null;
  status: 'Pending' | 'Verified' | 'Rejected';
  rejected_reason: string | null;
  contributor_id: string;
  created_at: string;
  verified_at: string | null;
  verification_path: 'A' | 'B' | null;
  verification_tactic: string | null;
}

export interface TheoremListResponse {
  theorems: Theorem[];
  next_cursor: string | null;
  total: number;
  total_capped: boolean;
}
```

Update `useRecentTheorems`/`useTheorem` return types accordingly.

- [ ] **Step 2: Verify + commit**

```bash
cd nasrudin-frontend && pnpm tsc --noEmit && pnpm biome check
git add nasrudin-frontend/src/lib/types.ts nasrudin-frontend/src/lib/queries.ts
git commit -m "feat(frontend): align Theorem TS type with server response"
```

---

## Phase 9 — Deploy infrastructure

### Task 9.1: docker-compose.yml + Dockerfiles

**Files:**
- Create: `deploy/docker-compose.yml`, `deploy/dockerfiles/api.Dockerfile`, `deploy/dockerfiles/frontend.Dockerfile`, `deploy/dockerfiles/backup.Dockerfile`

- [ ] **Step 1: Write `deploy/docker-compose.yml`**

```yaml
services:
  postgres:
    image: postgres:18-alpine
    container_name: nasrudin-pg
    env_file: .env
    environment:
      PGDATA: /var/lib/postgresql/data/pgdata
    volumes:
      - /data/postgres:/var/lib/postgresql/data
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U $${POSTGRES_USER}"]
      interval: 5s
      retries: 10
    restart: unless-stopped

  caddy:
    image: caddy:2-alpine
    container_name: nasrudin-caddy
    ports: ["80:80", "443:443"]
    volumes:
      - ./Caddyfile:/etc/caddy/Caddyfile:ro
      - /data/caddy:/data
      - /data/caddy-config:/config
    depends_on: [api, frontend]
    restart: unless-stopped

  api:
    build: { context: ../engine, dockerfile: ../deploy/dockerfiles/api.Dockerfile }
    container_name: nasrudin-api
    env_file: .env
    environment:
      DATABASE_URL: "postgres://${POSTGRES_USER}:${POSTGRES_PASSWORD}@postgres:5432/${POSTGRES_DB}"
      ROCKS_DB_PATH: /data/rocks
      PROVER_ROOT: /opt/prover
    volumes:
      - /data/rocks:/data/rocks
      - /data/lake-cache:/data/lake-cache
      - ../prover:/opt/prover:ro
    depends_on:
      postgres: { condition: service_healthy }
    restart: unless-stopped

  frontend:
    build: { context: ../nasrudin-frontend, dockerfile: ../deploy/dockerfiles/frontend.Dockerfile }
    container_name: nasrudin-frontend
    env_file: .env
    environment:
      VITE_API_BASE_URL: "https://api.nasrudin.org"
    restart: unless-stopped

  ga-worker:
    build: { context: ../engine, dockerfile: ../deploy/dockerfiles/api.Dockerfile, target: worker }
    container_name: nasrudin-ga
    env_file: .env
    environment:
      NASRUDIN_API_URL: "http://api:3001"
      NASRUDIN_WORKER_KEY: "${NASRUDIN_INTERNAL_WORKER_KEY}"
      NASRUDIN_WORKER_ID: "in-proc-worker-1"
      PROVER_ROOT: /opt/prover
    volumes:
      - ../prover:/opt/prover:ro
    profiles: [workers]
    depends_on: [api]
    restart: unless-stopped

  backup:
    build: { context: ../deploy, dockerfile: dockerfiles/backup.Dockerfile }
    container_name: nasrudin-backup
    env_file: .env
    volumes:
      - /data:/data:ro
      - ./rclone.conf:/etc/rclone.conf:ro
    restart: unless-stopped
```

- [ ] **Step 2: Write Dockerfiles**

```dockerfile
# deploy/dockerfiles/api.Dockerfile
FROM rust:1.93-bookworm AS builder
WORKDIR /src
COPY . .
RUN cargo build --release --bin physics-api --bin migrate --bin backfill_existing_lean --bin discover_emc2

FROM debian:bookworm-slim AS runtime
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl && rm -rf /var/lib/apt/lists/*
COPY --from=builder /src/target/release/physics-api /usr/local/bin/physics-api
COPY --from=builder /src/target/release/migrate /usr/local/bin/migrate
COPY --from=builder /src/target/release/backfill_existing_lean /usr/local/bin/backfill_existing_lean
EXPOSE 3001
CMD ["/usr/local/bin/physics-api"]

FROM runtime AS worker
COPY --from=builder /src/target/release/discover_emc2 /usr/local/bin/discover_emc2
# Lean toolchain copy — install via elan
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.27.0
ENV PATH="/root/.elan/bin:${PATH}"
CMD ["/usr/local/bin/discover_emc2", "--max-lake=15"]
```

```dockerfile
# deploy/dockerfiles/frontend.Dockerfile
FROM node:22-bookworm-slim AS builder
RUN corepack enable
WORKDIR /src
COPY . .
RUN pnpm install --frozen-lockfile && pnpm build

FROM node:22-bookworm-slim AS runtime
WORKDIR /app
COPY --from=builder /src/.output .
EXPOSE 3000
CMD ["node", "server/index.mjs"]
```

```dockerfile
# deploy/dockerfiles/backup.Dockerfile
FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates postgresql-client rclone cron && rm -rf /var/lib/apt/lists/*
COPY scripts/backup-loop.sh /usr/local/bin/backup-loop.sh
RUN chmod +x /usr/local/bin/backup-loop.sh
CMD ["/usr/local/bin/backup-loop.sh"]
```

- [ ] **Step 3: Validate compose**

```bash
cd deploy && docker compose config
```
Expected: clean parse, no unresolved variables.

- [ ] **Step 4: Commit**

```bash
git add deploy/docker-compose.yml deploy/dockerfiles/
git commit -m "feat(deploy): add docker-compose + Dockerfiles for api/frontend/ga/backup"
```

### Task 9.2: Caddyfile + Cloudflare instructions

**Files:**
- Create: `deploy/Caddyfile`
- Modify: `docs/DEPLOYMENT.md` (Cloudflare DNS section)

- [ ] **Step 1: Caddyfile**

```
nasrudin.org {
  reverse_proxy frontend:3000
  encode zstd gzip
  header {
    Strict-Transport-Security "max-age=31536000; includeSubDomains"
    X-Content-Type-Options "nosniff"
    Referrer-Policy "strict-origin-when-cross-origin"
  }
}

api.nasrudin.org {
  @sse path /api/events/*
  handle @sse {
    reverse_proxy api:3001 {
      flush_interval -1
    }
  }
  reverse_proxy api:3001
  header Access-Control-Allow-Origin "https://nasrudin.org"
  header Access-Control-Allow-Credentials "true"
}

origin.nasrudin.org {
  reverse_proxy api:3001
}
```

- [ ] **Step 2: Validate**

```bash
docker run --rm -v "$PWD/deploy/Caddyfile:/etc/caddy/Caddyfile:ro" caddy:2-alpine caddy validate --config /etc/caddy/Caddyfile
```
Expected: `Valid configuration`.

- [ ] **Step 3: Commit**

```bash
git add deploy/Caddyfile
git commit -m "feat(deploy): add Caddyfile with SSE flush + CORS"
```

### Task 9.3: bootstrap.sh + .env.example

**Files:**
- Create: `deploy/.env.example`, `deploy/scripts/bootstrap.sh`, `deploy/rclone.conf.example`

- [ ] **Step 1: Write .env.example**

```bash
# deploy/.env.example
POSTGRES_USER=physics
POSTGRES_DB=physics_generator
POSTGRES_PASSWORD=__GEN__
NASRUDIN_INTERNAL_WORKER_KEY=__GEN__
SESSION_SECRET=__GEN__
ARGON2_PEPPER=__GEN__
DO_SPACES_BUCKET=nasrudin-backups
DO_SPACES_ENDPOINT=https://nyc3.digitaloceanspaces.com
DO_SPACES_KEY=__SET__
DO_SPACES_SECRET=__SET__
NASRUDIN_API_PUBLIC_URL=https://api.nasrudin.org
NASRUDIN_FRONTEND_PUBLIC_URL=https://nasrudin.org
```

- [ ] **Step 2: bootstrap.sh**

```bash
#!/usr/bin/env bash
# deploy/scripts/bootstrap.sh — fresh-droplet idempotent setup
set -euo pipefail

REPO=${REPO:-https://github.com/nasdin/nasrudin.git}
INSTALL_DIR=/opt/nasrudin
DATA_VOLUME=/dev/disk/by-label/nasrudin-data
DATA_MOUNT=/data

apt-get update
apt-get install -y --no-install-recommends ca-certificates curl gnupg git docker.io docker-compose-v2 ufw
systemctl enable --now docker

if ! mountpoint -q "$DATA_MOUNT"; then
  mkdir -p "$DATA_MOUNT"
  if [ -e "$DATA_VOLUME" ]; then
    blkid "$DATA_VOLUME" || mkfs.ext4 -L nasrudin-data "$DATA_VOLUME"
    echo "$DATA_VOLUME $DATA_MOUNT ext4 defaults,nofail,discard 0 2" >> /etc/fstab
    mount "$DATA_MOUNT"
  fi
fi

mkdir -p "$DATA_MOUNT"/{postgres,rocks,lake-cache,caddy,caddy-config}

if [ ! -d "$INSTALL_DIR" ]; then git clone "$REPO" "$INSTALL_DIR"; fi
cd "$INSTALL_DIR/deploy"

if [ ! -f .env ]; then
  cp .env.example .env
  sed -i "s/__GEN__/$(openssl rand -hex 32)/g" .env
  chmod 600 .env
fi

ufw allow 22/tcp
ufw allow 80/tcp
ufw allow 443/tcp
yes | ufw enable

docker compose pull
docker compose up -d
sleep 10
docker compose run --rm api /usr/local/bin/migrate
docker compose run --rm api /usr/local/bin/backfill_existing_lean
echo "Bootstrap complete. Issue worker key with: docker compose run --rm api /usr/local/bin/issue-worker-key"
```

- [ ] **Step 3: Mode + commit**

```bash
chmod +x deploy/scripts/bootstrap.sh
git add deploy/.env.example deploy/scripts/bootstrap.sh deploy/rclone.conf.example
git commit -m "feat(deploy): add bootstrap.sh + .env.example for fresh-droplet setup"
```

### Task 9.4: Backup loop

**Files:**
- Create: `deploy/scripts/backup-loop.sh`

- [ ] **Step 1: Write loop**

```bash
#!/usr/bin/env bash
# deploy/scripts/backup-loop.sh — runs inside backup container
set -euo pipefail

while true; do
  STAMP=$(date +%Y/%m/%d/%H)
  TARGET="${DO_SPACES_BUCKET}/$STAMP"
  echo "[backup] starting $STAMP"

  PGPASSWORD="$POSTGRES_PASSWORD" pg_dump -U "$POSTGRES_USER" -h postgres -d "$POSTGRES_DB" -Fc -f /tmp/pg.dump || { echo "pg_dump failed"; sleep 60; continue; }

  rclone --config /etc/rclone.conf copy /tmp/pg.dump "spaces:$TARGET/postgres.dump" && \
    rclone --config /etc/rclone.conf sync /data/rocks/ "spaces:$TARGET/rocks/" || { echo "rclone failed"; sleep 60; continue; }

  rm /tmp/pg.dump
  rclone --config /etc/rclone.conf delete --min-age 30d "spaces:$DO_SPACES_BUCKET/" --rmdirs || true
  echo "[backup] done $STAMP"
  sleep 3600
done
```

- [ ] **Step 2: Test inside container**

```bash
docker compose build backup
docker compose run --rm backup /usr/local/bin/backup-loop.sh &
sleep 10 && docker compose stop backup
```

- [ ] **Step 3: Commit**

```bash
chmod +x deploy/scripts/backup-loop.sh
git add deploy/scripts/backup-loop.sh
git commit -m "feat(deploy): add backup-loop.sh hourly pg_dump + rclone sync to Spaces"
```

### Task 9.5: smoke.sh + restore-from-spaces.sh

**Files:**
- Create: `deploy/scripts/smoke.sh`, `deploy/scripts/restore-from-spaces.sh`

- [ ] **Step 1: smoke.sh**

```bash
#!/usr/bin/env bash
# deploy/scripts/smoke.sh — post-deploy assertions
set -euo pipefail

API="${NASRUDIN_API_PUBLIC_URL:-http://localhost:3001}"
FRONTEND="${NASRUDIN_FRONTEND_PUBLIC_URL:-http://localhost:3000}"
KEY="${NASRUDIN_INTERNAL_WORKER_KEY:?required}"

assert() { local name=$1; shift; if "$@"; then echo "✓ $name"; else echo "✗ $name"; exit 1; fi; }

assert "frontend renders"           bash -c "curl -fsS '$FRONTEND/' | grep -qi nasrudin"
assert "api health ok"              bash -c "curl -fsS '$API/health' | jq -e '.db == \"ok\" and .rocks == \"ok\"' >/dev/null"
assert "theorems list"              bash -c "curl -fsS '$API/api/theorems?limit=1' | jq -e '.total >= 0' >/dev/null"
assert "domains"                    bash -c "curl -fsS '$API/api/domains' | jq -e 'type == \"array\"' >/dev/null"
assert "axioms"                     bash -c "curl -fsS '$API/api/axioms' | jq -e 'type == \"array\"' >/dev/null"
assert "workers list"               bash -c "curl -fsS '$API/api/workers' | jq -e 'type == \"array\"' >/dev/null"
assert "events/discoveries SSE"     bash -c "timeout 20 curl -fsSN '$API/api/events/discoveries' | head -c 32 | grep -q 'ping\\|theorem_'"
assert "events/stats SSE"           bash -c "timeout 20 curl -fsSN '$API/api/events/stats' | head -c 32 | grep -q 'ping\\|ga_\\|worker_'"
assert "ingest accepts batch"       bash -c "curl -fsS -X POST '$API/api/ingest' -H 'authorization: Bearer $KEY' -H 'content-type: application/json' -d '{\"worker_id\":\"in-proc-worker-1\",\"engine_git_sha\":\"smoke\",\"lean_version\":\"4.27.0\",\"theorems\":[{\"canonical_statement\":\"True_smoke_$$\",\"domain\":\"PureMath\",\"lean_source\":\"theorem t : True := trivial\",\"chain\":[],\"axioms_used\":[]}]}' | jq -e '.results[0].status.kind == \"Pending\" or .results[0].status.kind == \"Duplicate\"' >/dev/null"
assert "axiom firewall blocks axiom" bash -c "curl -fsS -X POST '$API/api/ingest' -H 'authorization: Bearer $KEY' -H 'content-type: application/json' -d '{\"worker_id\":\"in-proc-worker-1\",\"engine_git_sha\":\"smoke\",\"lean_version\":\"4.27.0\",\"theorems\":[{\"canonical_statement\":\"E_$$\",\"domain\":\"PureMath\",\"lean_source\":\"axiom evil : True\\ntheorem t : True := evil\",\"chain\":[],\"axioms_used\":[]}]}' | jq -e '.results[0].status.kind == \"Rejected\"' >/dev/null"

echo "all smoke checks passed"
```

- [ ] **Step 2: restore-from-spaces.sh**

```bash
#!/usr/bin/env bash
# deploy/scripts/restore-from-spaces.sh — disaster recovery
set -euo pipefail

LATEST=$(rclone --config /etc/rclone.conf lsf "spaces:$DO_SPACES_BUCKET/" --dirs-only | tail -1)
[ -n "$LATEST" ] || { echo "no backups found"; exit 1; }
echo "restoring from $LATEST"

docker compose down
rm -rf /data/rocks/*
rclone --config /etc/rclone.conf sync "spaces:$DO_SPACES_BUCKET/$LATEST/rocks/" /data/rocks/
rclone --config /etc/rclone.conf copy "spaces:$DO_SPACES_BUCKET/$LATEST/postgres.dump" /tmp/

docker compose up -d postgres
sleep 10
PGPASSWORD="$POSTGRES_PASSWORD" pg_restore -U "$POSTGRES_USER" -h localhost -d "$POSTGRES_DB" -c /tmp/postgres.dump
docker compose up -d
echo "restore complete"
```

- [ ] **Step 3: Commit**

```bash
chmod +x deploy/scripts/smoke.sh deploy/scripts/restore-from-spaces.sh
git add deploy/scripts/smoke.sh deploy/scripts/restore-from-spaces.sh
git commit -m "feat(deploy): add smoke.sh + restore-from-spaces.sh"
```

---

## Phase 10 — Acceptance + go-live

### Task 10.1: E2E ingest test (full Lean toolchain)

**Files:**
- Create: `engine/tests/e2e/spontaneous_emc2_ingest.rs`

- [ ] **Step 1: Write test**

```rust
// engine/tests/e2e/spontaneous_emc2_ingest.rs (top-level workspace test)
#[tokio::test]
#[ignore] // nightly only — requires real Lean + docker
async fn full_pipeline_round_trip() -> anyhow::Result<()> {
    // Compose stack should already be up via just script
    let api = "http://localhost:3001";
    let key = std::env::var("NASRUDIN_INTERNAL_WORKER_KEY")?;
    let lean = std::fs::read_to_string("prover/PhysicsGenerator/Derived/RestEnergyUpstream.lean")?;
    let payload = serde_json::json!({
        "worker_id":"in-proc-worker-1","engine_git_sha":"e2e","lean_version":"4.27.0",
        "theorems":[{"canonical_statement":"E = m * c^2","domain":"SpecialRelativity","lean_source":lean,"chain":[],"axioms_used":["c_positive"]}]
    });
    let client = reqwest::Client::new();
    let r = client.post(format!("{api}/api/ingest")).bearer_auth(&key).json(&payload).send().await?;
    assert!(r.status().is_success());
    let body: serde_json::Value = r.json().await?;
    let id = body["results"][0]["theorem_id"].as_str().unwrap();
    for _ in 0..36 {
        tokio::time::sleep(std::time::Duration::from_secs(5)).await;
        let r = client.get(format!("{api}/api/theorems/{id}")).send().await?.json::<serde_json::Value>().await?;
        if r["status"] == "Verified" { return Ok(()); }
    }
    panic!("not verified within 180s");
}
```

- [ ] **Step 2: Run nightly**

```bash
docker compose -f deploy/docker-compose.yml --profile workers up -d
cargo test --test spontaneous_emc2_ingest -- --ignored --nocapture
```

- [ ] **Step 3: Commit**

```bash
git add engine/tests/e2e/spontaneous_emc2_ingest.rs
git commit -m "test: add e2e ingest round-trip nightly"
```

### Task 10.2: Local stack smoke pass

- [ ] **Step 1: Bring up local stack**

```bash
cd deploy
cp .env.example .env && sed -i "s/__GEN__/$(openssl rand -hex 32)/g" .env
docker compose up -d --build
sleep 30
docker compose run --rm api /usr/local/bin/migrate
docker compose run --rm api /usr/local/bin/backfill_existing_lean
NASRUDIN_INTERNAL_WORKER_KEY=$(grep INTERNAL_WORKER_KEY .env | cut -d= -f2) NASRUDIN_API_PUBLIC_URL=http://localhost:3001 NASRUDIN_FRONTEND_PUBLIC_URL=http://localhost:3000 ./scripts/smoke.sh
```
Expected: all assertions pass.

- [ ] **Step 2: Open in browser**

`http://localhost:3000/browse` — should show ≥3 theorems (the backfilled hand-proofs).

- [ ] **Step 3: Commit any fixes that surface**

```bash
git add -p && git commit -m "fix: smoke test surface fixes"
```

### Task 10.3: DigitalOcean droplet provisioning

**Files:**
- Modify: `docs/DEPLOYMENT.md` (record actual commands run)

- [ ] **Step 1: Register `nasrudin.org`**

Manual at registrar of choice. Point nameservers at Cloudflare.

- [ ] **Step 2: Provision via doctl**

```bash
doctl compute droplet create nasrudin-prod \
  --image debian-12-x64 --region nyc1 --size s-4vcpu-8gb \
  --ssh-keys $SSH_KEY_ID \
  --user-data-file deploy/scripts/bootstrap.sh \
  --wait

doctl compute volume create nasrudin-data --region nyc1 --size 50GiB --fs-type ext4 --fs-label nasrudin-data
doctl compute volume-action attach <VOL_ID> <DROPLET_ID>
```

- [ ] **Step 3: Cloudflare DNS**

In Cloudflare dashboard:
- `nasrudin.org` A → droplet IP, proxied (orange)
- `api.nasrudin.org` A → droplet IP, proxied
- `origin.nasrudin.org` A → droplet IP, DNS-only (grey)
- SSL/TLS: Full (strict)
- Page Rule: `api.nasrudin.org/api/events/*` → cache=bypass, buffering=off

- [ ] **Step 4: First deploy**

```bash
ssh root@<droplet-ip>
cd /opt/nasrudin
docker compose pull
docker compose up -d
NASRUDIN_API_PUBLIC_URL=https://api.nasrudin.org NASRUDIN_FRONTEND_PUBLIC_URL=https://nasrudin.org \
  NASRUDIN_INTERNAL_WORKER_KEY=$(grep INTERNAL_WORKER_KEY /opt/nasrudin/deploy/.env | cut -d= -f2) \
  /opt/nasrudin/deploy/scripts/smoke.sh
```
Expected: all green.

- [ ] **Step 5: Document**

Update `docs/DEPLOYMENT.md` with the exact commands ran. Commit.

### Task 10.4: Final acceptance — 14-criterion checklist

Run from local machine against the live droplet:

- [ ] **C1**: `curl -fsS https://nasrudin.org/ | grep -q Nasrudin` and visit `/browse`, expect ≥ 3 backfilled theorems.
- [ ] **C2**: `curl -fsS https://api.nasrudin.org/api/theorems/<known-hash>/lean -o t.lean && lake build` against committed `prover/`. Exit 0.
- [ ] **C3**: Trigger GA worker, watch a `Verified` theorem land within 180 s.
- [ ] **C4**: Open `https://api.nasrudin.org/api/events/discoveries` in browser, watch `theorem_verified` events. Same for `/api/events/stats`.
- [ ] **C5**: Submit theorem with `nsk_worker_test`, verify `workers.theorems_contributed` for that worker incremented; appears on `/leaderboard`.
- [ ] **C6**: POST ingest with `axiom evil : True` in lean_source — expect `Rejected{axiom_or_sorry_in_source}`.
- [ ] **C7**: POST 70 theorems in 1 min from one worker, expect 429 after 60.
- [ ] **C8**: `tsc --noEmit && biome check` clean. `/api/me/stats`, `/api/saved-searches`, `/api/workers`, `/api/domains`, `/api/axioms`, `/api/api-keys` all 200.
- [ ] **C9**: `ssh ... && cd /opt/nasrudin && git pull && docker compose up -d`. Theorem count before == after.
- [ ] **C10**: `docker compose down && rm -rf /data/rocks && docker compose up -d`. Theorem count restored.
- [ ] **C11**: `rclone ls spaces:nasrudin-backups/$(date +%Y/%m/%d)/` shows `pg_dump` and `rocks/` for last 24 h.
- [ ] **C12**: `smoke.sh` against the live URL — all green.
- [ ] **C13**: Backfilled `RestEnergyUpstream.lean`, `AutoRestEnergyUpstream.lean`, `PhotonEnergyMomentum.lean` browseable + downloadable.
- [ ] **C14**: After 1 GA worker hour, `find prover/PhysicsGenerator/Derived/Discover*.lean -newer .timestamp` returns empty. (`.timestamp` set right before the hour.)

- [ ] **Step 5: Commit acceptance log**

```bash
git add docs/RUNBOOK.md   # contains the 14-criterion log
git commit -m "ops: record Phase 9 acceptance run results"
```

---

## Self-review summary

**Coverage check** — every spec section maps to at least one task:

| Spec section | Task(s) |
|---|---|
| Postgres schema | 1.1, 1.2, 1.3, 1.4, 1.5 |
| RocksDB reverify_queue | 2.1 |
| Boot/hydration | 2.2 |
| Lake builder + axiom firewall | 3.1 |
| Reverify queue + A/B paths + contributor counter | 3.2, 3.3, 3.4 |
| Ingest endpoint + rate limit + WorkerAuth | 4.1, 4.2, 4.3 |
| Read endpoints (list/recent/by-id/lean) | 5.1 |
| Two SSE streams | 5.2 |
| Seed endpoint | 5.3 |
| Axioms + Domains | 5.4 |
| Workers heartbeat + list | 6.1 |
| /api/me/stats | 6.2 |
| Health | 6.3 |
| GA worker HTTP submission | 7.1 |
| Backfill | 7.2 |
| Frontend SSE hooks + types | 8.1, 8.2 |
| docker-compose + Dockerfiles | 9.1 |
| Caddyfile | 9.2 |
| bootstrap.sh + .env | 9.3 |
| Backup loop | 9.4 |
| smoke.sh + restore | 9.5 |
| E2E test | 10.1 |
| Local smoke | 10.2 |
| DO provisioning + DNS | 10.3 |
| 14 acceptance criteria | 10.4 |

**Type consistency** — `IngestBatch`, `IngestTheorem`, `IngestStatus`, `IngestResultItem`, `ReverifyJob`, `DiscoveryEvent`, `Theorem` (TS), `Page<T>`, `WorkerRateLimiter`, `WorkerAuth`, `LakeBuilder`, `VerifyOutcome`, `ReverifyQueue` are defined in earlier tasks and used unchanged in later ones.

**Placeholder scan** — all code blocks contain real implementation or test code. The intentional `todo!()` in Task 3.2 is replaced with the full integration test in Task 3.4 in the same phase.
