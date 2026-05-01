//! `theorems.user_email` column.
//!
//! Stores the email of the user who owns the worker that contributed
//! the theorem. This allows theorems to display both the worker's
//! pseudonym (contributor_id) and the user's email for proper
//! attribution in the contributor leaderboard.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Theorems::Table)
                    .add_column_if_not_exists(
                        ColumnDef::new(Theorems::UserEmail)
                            .text()
                            .null(),
                    )
                    .to_owned(),
            )
            .await
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Theorems::Table)
                    .drop_column(Theorems::UserEmail)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum Theorems {
    Table,
    UserEmail,
}
