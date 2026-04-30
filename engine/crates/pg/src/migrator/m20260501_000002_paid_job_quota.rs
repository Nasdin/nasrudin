//! Paid Researcher quota + slice priority columns on `conjecture_jobs`.
//!
//! `lake_slot_hours_quota` (default 96 = 4 slots × 24h) is the hard
//! ceiling on lake-build work the cluster will spend on this conjecture.
//! `lake_slot_hours_consumed` is debited each heartbeat (server-capped
//! at `2 × wallclock_h × slots_held` to defeat lying workers). When
//! consumed ≥ quota the claim is released as `budget_exhausted`.
//!
//! `slice_priority` orders the queue (highest first); 5 is the default
//! free-tier baseline, leaving 6–9 for elevated tiers. `tier` records
//! which plan owns the job ("researcher" today; future expansion).
//! Compound index on (state, slice_priority DESC, created_at ASC) keeps
//! the FOR UPDATE SKIP LOCKED claim path index-only.

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
                        ColumnDef::new(ConjectureJobs::LakeSlotHoursQuota)
                            .integer()
                            .not_null()
                            .default(96),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(ConjectureJobs::LakeSlotHoursConsumed)
                            .float()
                            .not_null()
                            .default(0.0),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(ConjectureJobs::SlicePriority)
                            .integer()
                            .not_null()
                            .default(5),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(ConjectureJobs::Tier)
                            .text()
                            .not_null()
                            .default("researcher"),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_conjecture_jobs_queue")
                    .table(ConjectureJobs::Table)
                    .col(ConjectureJobs::State)
                    .col(ConjectureJobs::SlicePriority)
                    .col(ConjectureJobs::CreatedAt)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(
                Index::drop()
                    .name("idx_conjecture_jobs_queue")
                    .table(ConjectureJobs::Table)
                    .to_owned(),
            )
            .await
            .ok();
        manager
            .alter_table(
                Table::alter()
                    .table(ConjectureJobs::Table)
                    .drop_column(ConjectureJobs::Tier)
                    .drop_column(ConjectureJobs::SlicePriority)
                    .drop_column(ConjectureJobs::LakeSlotHoursConsumed)
                    .drop_column(ConjectureJobs::LakeSlotHoursQuota)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum ConjectureJobs {
    Table,
    State,
    CreatedAt,
    LakeSlotHoursQuota,
    LakeSlotHoursConsumed,
    SlicePriority,
    Tier,
}
