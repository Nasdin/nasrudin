//! Theorems gain trust state captured at ingest time so the reverify
//! drain can decide whether to bypass the redundant `lake build`
//! confirmation.
//!
//! - `worker_trusted` — whether the submitting worker resolved as trusted
//!   per `crates/api/src/trust.rs::resolve` at ingest time. Snapshotted
//!   on the row so trust changes don't retroactively alter pending rows.
//! - `worker_spot_check_rate` — the resolved 1-in-N rate at ingest time;
//!   NULL means "use env default at process_one time".
//!
//! Both columns are NULL/false for pre-migration rows; reverify falls
//! back to the existing path (always promote) for those.

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
                        ColumnDef::new(Theorems::WorkerTrusted)
                            .boolean()
                            .not_null()
                            .default(false),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(Theorems::WorkerSpotCheckRate)
                            .integer()
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
                    .drop_column(Theorems::WorkerTrusted)
                    .drop_column(Theorems::WorkerSpotCheckRate)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum Theorems {
    Table,
    WorkerTrusted,
    WorkerSpotCheckRate,
}
