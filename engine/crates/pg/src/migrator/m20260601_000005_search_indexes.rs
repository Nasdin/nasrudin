//! Search indexes for the discovery layer.
//!
//! Adds:
//!   * `theorems.canonical_ac_hash` (binary 8) — AC-canonical hash, separate
//!     from the existing `canonical_hash` so syntactic identity is preserved
//!     and we can do "did the corpus already prove this conjecture?" lookups
//!     in O(1).
//!   * GIN index on `axioms_used` — `axioms_used @> ARRAY[...]` containment
//!     queries for "give me everything derivable from these axioms".
//!   * GIN index on `dimension` — exact dimensional match.
//!   * Composite B-tree on `(domain, depth)` — the most common combined
//!     filter for the candidate query.
//!
//! Backfill of `canonical_ac_hash` runs out-of-band via
//! `engine/crates/api/src/bin/backfill_ac_hash.rs` (idempotent UPSERT).
//! This migration adds the column nullable; once 100% backfilled, a follow-up
//! migration can tighten to NOT NULL.

use sea_orm_migration::prelude::*;
use sea_orm_migration::sea_orm::ConnectionTrait;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Theorems::Table)
                    .add_column(
                        ColumnDef::new(Theorems::CanonicalAcHash)
                            .binary_len(8)
                            .null(),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_theorems_canonical_ac_hash")
                    .table(Theorems::Table)
                    .col(Theorems::CanonicalAcHash)
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_theorems_domain_depth")
                    .table(Theorems::Table)
                    .col(Theorems::Domain)
                    .col(Theorems::Depth)
                    .to_owned(),
            )
            .await?;

        // GIN indexes for array containment. Sea-ORM's index builder doesn't
        // express USING GIN, so emit raw SQL.
        let conn = manager.get_connection();
        conn.execute_unprepared(
            "CREATE INDEX IF NOT EXISTS idx_theorems_axioms_used_gin ON theorems USING GIN (axioms_used)",
        )
        .await?;
        conn.execute_unprepared(
            "CREATE INDEX IF NOT EXISTS idx_theorems_dimension_gin ON theorems USING GIN (dimension)",
        )
        .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();
        conn.execute_unprepared("DROP INDEX IF EXISTS idx_theorems_dimension_gin")
            .await?;
        conn.execute_unprepared("DROP INDEX IF EXISTS idx_theorems_axioms_used_gin")
            .await?;

        manager
            .drop_index(
                Index::drop()
                    .name("idx_theorems_domain_depth")
                    .table(Theorems::Table)
                    .to_owned(),
            )
            .await?;
        manager
            .drop_index(
                Index::drop()
                    .name("idx_theorems_canonical_ac_hash")
                    .table(Theorems::Table)
                    .to_owned(),
            )
            .await?;
        manager
            .alter_table(
                Table::alter()
                    .table(Theorems::Table)
                    .drop_column(Theorems::CanonicalAcHash)
                    .to_owned(),
            )
            .await?;
        Ok(())
    }
}

#[derive(DeriveIden)]
enum Theorems {
    Table,
    CanonicalAcHash,
    Domain,
    Depth,
}
