//! Per-job elastic slot allocation.
//!
//! Adds `conjecture_jobs.allocated_slots` (int, default 4). The
//! `/api/jobs/claim` handler stamps this from the worker's reported
//! `available_lake_slots` so the heartbeat sanity-cap math (consumed
//! delta ≤ 2 × wallclock_h × slots_held) is grounded in the slots
//! actually committed to *this* job, not a fixed cluster-wide
//! constant. Default 4 matches the legacy fixed-allocation behaviour
//! for any rows the server hasn't claimed yet.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(ConjectureJobs::Table)
                    .add_column_if_not_exists(
                        ColumnDef::new(ConjectureJobs::AllocatedSlots)
                            .integer()
                            .not_null()
                            .default(4),
                    )
                    .to_owned(),
            )
            .await
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(ConjectureJobs::Table)
                    .drop_column(ConjectureJobs::AllocatedSlots)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum ConjectureJobs {
    Table,
    AllocatedSlots,
}
