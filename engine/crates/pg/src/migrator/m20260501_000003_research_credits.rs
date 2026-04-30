//! `users.research_credits` — the $19/mo Researcher tier ledger.
//!
//! Each Researcher plan grants N credits per cycle; one credit is
//! debited atomically when a user creates a paid `conjecture_jobs` row
//! (POST /api/research/jobs). On cancel-before-progress or
//! `budget_exhausted` with zero verified results, the credit is
//! refunded. Anything with a partial result keeps the credit (corpus
//! growth under user attribution).

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .add_column_if_not_exists(
                        ColumnDef::new(Users::ResearchCredits)
                            .integer()
                            .not_null()
                            .default(0),
                    )
                    .to_owned(),
            )
            .await
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .drop_column(Users::ResearchCredits)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum Users {
    Table,
    ResearchCredits,
}
