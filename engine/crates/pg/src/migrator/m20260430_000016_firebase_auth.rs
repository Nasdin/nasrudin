//! Migrate `users` to Firebase-shaped identity:
//!   - DELETE all rows (none in production today; cascades to dependents).
//!   - DROP password_hash, github_id, github_login (no longer used).
//!   - ADD firebase_uid TEXT NOT NULL UNIQUE.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();

        // 1. Wipe — there are no production accounts. CASCADE clears every
        //    dependent row (api_keys, workers, saved_searches, etc.).
        conn.execute_unprepared("DELETE FROM users").await?;

        // 2. Drop github_id unique index from m20260430_000014.
        conn.execute_unprepared("DROP INDEX IF EXISTS users_github_id_unique")
            .await?;

        // 3. Drop columns.
        conn.execute_unprepared("ALTER TABLE users DROP COLUMN IF EXISTS password_hash")
            .await?;
        conn.execute_unprepared("ALTER TABLE users DROP COLUMN IF EXISTS github_id")
            .await?;
        conn.execute_unprepared("ALTER TABLE users DROP COLUMN IF EXISTS github_login")
            .await?;

        // 4. Add firebase_uid + unique index.
        conn.execute_unprepared("ALTER TABLE users ADD COLUMN firebase_uid TEXT NOT NULL UNIQUE")
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();
        conn.execute_unprepared("ALTER TABLE users DROP COLUMN IF EXISTS firebase_uid")
            .await?;
        // Restore the columns dropped in `up`. Defaults match the original
        // schema; rows can't be reconstructed so password_hash is left NULL.
        conn.execute_unprepared("ALTER TABLE users ADD COLUMN password_hash TEXT")
            .await?;
        conn.execute_unprepared("ALTER TABLE users ADD COLUMN github_id BIGINT")
            .await?;
        conn.execute_unprepared("ALTER TABLE users ADD COLUMN github_login TEXT")
            .await?;
        conn.execute_unprepared("CREATE UNIQUE INDEX users_github_id_unique ON users (github_id)")
            .await?;
        Ok(())
    }
}
