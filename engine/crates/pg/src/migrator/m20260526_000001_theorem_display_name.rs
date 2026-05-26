//! Add `display_name` + `description` columns to `theorems`, plus a GIN
//! tsvector index over their concatenation so /api/search can match free
//! text against either field in sub-millisecond time at corpus scale.
//!
//! The columns are NULL for backfilled / imported rows. The LLM-naming
//! hook on the verify path populates them async; the `/api/admin/theorems/
//! backfill_names` admin endpoint walks the long tail.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let db = manager.get_connection();
        db.execute_unprepared(
            r#"ALTER TABLE theorems
                 ADD COLUMN IF NOT EXISTS display_name TEXT NULL,
                 ADD COLUMN IF NOT EXISTS description TEXT NULL"#,
        )
        .await?;
        db.execute_unprepared(
            r#"CREATE INDEX IF NOT EXISTS theorems_display_name_idx
                 ON theorems USING gin (to_tsvector(
                   'english',
                   coalesce(display_name, '') || ' ' || coalesce(description, '')
                 ))"#,
        )
        .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let db = manager.get_connection();
        db.execute_unprepared("DROP INDEX IF EXISTS theorems_display_name_idx")
            .await?;
        db.execute_unprepared(
            "ALTER TABLE theorems \
             DROP COLUMN IF EXISTS display_name, \
             DROP COLUMN IF EXISTS description",
        )
        .await?;
        Ok(())
    }
}
