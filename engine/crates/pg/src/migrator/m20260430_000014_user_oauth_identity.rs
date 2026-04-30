//! Adds OAuth identity columns to `users` and drops the NOT NULL on
//! `password_hash` so OAuth-only accounts can exist without a password.
//!
//! `github_id` is the canonical link key (GitHub's user ID is immutable);
//! `github_login` is stored for display only and may change over time.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        // 1. Add github_id (UNIQUE, NULL).
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .add_column_if_not_exists(
                        ColumnDef::new(Users::GithubId).big_integer().null(),
                    )
                    .to_owned(),
            )
            .await?;

        // 2. Add github_login (TEXT, NULL).
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .add_column_if_not_exists(
                        ColumnDef::new(Users::GithubLogin).text().null(),
                    )
                    .to_owned(),
            )
            .await?;

        // 3. Unique partial index on github_id (multiple NULLs are fine in PG).
        manager
            .create_index(
                Index::create()
                    .name("users_github_id_unique")
                    .table(Users::Table)
                    .col(Users::GithubId)
                    .unique()
                    .to_owned(),
            )
            .await?;

        // 4. Drop NOT NULL on password_hash. SeaQuery's column-modify path is
        //    awkward on Postgres; use raw SQL.
        manager
            .get_connection()
            .execute_unprepared("ALTER TABLE users ALTER COLUMN password_hash DROP NOT NULL")
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        // Reverse order: re-add NOT NULL first (will fail if any OAuth-only
        // rows exist — that's intentional, the operator must clean up first).
        manager
            .get_connection()
            .execute_unprepared("ALTER TABLE users ALTER COLUMN password_hash SET NOT NULL")
            .await?;

        manager
            .drop_index(
                Index::drop()
                    .name("users_github_id_unique")
                    .table(Users::Table)
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .drop_column(Users::GithubLogin)
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .drop_column(Users::GithubId)
                    .to_owned(),
            )
            .await?;
        Ok(())
    }
}

#[derive(DeriveIden)]
enum Users {
    Table,
    GithubId,
    GithubLogin,
}
