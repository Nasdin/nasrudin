//! `theorems.worker_verified` column (P-Task 12).
//!
//! The worker locally lake-built the theorem before submitting. When
//! true, the reverify drain treats chain-replay success (sybil check)
//! as sufficient to flip the row directly to LakeVerified — no
//! separate lake-promotion step needed. The theorem is immediately
//! available as a peer-axiom in /api/seed.
//!
//! Lazy lake-build on `/api/theorems/{id}/lean` download remains
//! the defense-in-depth check: re-runs lake against the stored
//! Lean source. On disagreement: cascade-reject + worker reputation
//! tank.

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
                        ColumnDef::new(Theorems::WorkerVerified)
                            .boolean()
                            .not_null()
                            .default(false),
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
                    .drop_column(Theorems::WorkerVerified)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum Theorems {
    Table,
    WorkerVerified,
}
