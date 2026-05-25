//! Expression index on `theorems.origin_payload->'Imported'->>'source'`
//! so the `/api/resolve/{qualifier}` endpoint can find the theorem
//! imported from a given Lean qualifier in sub-millisecond time without
//! scanning the full table.
//!
//! Imported PhysLean / Mathlib rows store the original Lean identifier
//! under `origin_payload.Imported.source`. The "Built from" panel on the
//! theorem detail page does one resolve-per-dependency on render, so
//! every theorem detail view triggers ~5–15 of these lookups — without
//! the index, each one is a sequential scan over 30 k+ rows.
//!
//! The index is partial — only rows where the JSONB path actually
//! resolves to a string are stored, keeping the index small. GA-derived
//! theorems whose `origin_payload` is `{ "Crossover": {...} }` etc. are
//! excluded by the `IS NOT NULL` predicate.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let db = manager.get_connection();
        db.execute_unprepared(
            r#"CREATE INDEX IF NOT EXISTS theorems_imported_source_idx
                 ON theorems ((origin_payload->'Imported'->>'source'))
                 WHERE (origin_payload->'Imported'->>'source') IS NOT NULL"#,
        )
        .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let db = manager.get_connection();
        db.execute_unprepared("DROP INDEX IF EXISTS theorems_imported_source_idx")
            .await?;
        Ok(())
    }
}
