//! Defense-in-depth at the DB level: the `users_last_admin_guard`
//! trigger refuses to set `is_admin=FALSE` on the only remaining admin
//! row. Application-level checks in `RequireAdmin` also prevent the
//! self-demote case; this trigger covers SQL-direct edits and
//! out-of-band tools.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared(
                r#"
            CREATE OR REPLACE FUNCTION prevent_last_admin_demotion() RETURNS TRIGGER AS $func$
            BEGIN
                IF OLD.is_admin = TRUE AND NEW.is_admin = FALSE THEN
                    IF (SELECT count(*) FROM users WHERE is_admin = TRUE AND id != OLD.id) = 0 THEN
                        RAISE EXCEPTION 'cannot demote last admin' USING ERRCODE = 'P0001';
                    END IF;
                END IF;
                RETURN NEW;
            END;
            $func$ LANGUAGE plpgsql;

            DROP TRIGGER IF EXISTS users_last_admin_guard ON users;
            CREATE TRIGGER users_last_admin_guard
                BEFORE UPDATE ON users
                FOR EACH ROW WHEN (OLD.is_admin = TRUE AND NEW.is_admin = FALSE)
                EXECUTE FUNCTION prevent_last_admin_demotion();
            "#,
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .get_connection()
            .execute_unprepared(
                "DROP TRIGGER IF EXISTS users_last_admin_guard ON users; \
                 DROP FUNCTION IF EXISTS prevent_last_admin_demotion();",
            )
            .await?;
        Ok(())
    }
}
