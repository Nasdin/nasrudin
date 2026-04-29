//! Reputation + spot-check counters on the `workers` table (P-Task 5).
//!
//! The platform exposes self-service worker keys to thousands of school
//! volunteers. Existing defenses (chain firewall, axiom/sorry preflight,
//! per-worker rate limit) catch most cheating, but a worker that submits
//! Lean source which passes preflight yet fails lake-build is the gap.
//!
//! Reputation is an exponential moving average over lake-promotion
//! outcomes for chains the worker submitted: 0.99 × prev + 0.01 × (1 if
//! pass else 0). Starts at 1.0 (presumption of innocence). Ingest gates
//! on the score so a worker who consistently submits bogus chains gets
//! progressively throttled and eventually auto-revoked.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .add_column_if_not_exists(
                        ColumnDef::new(Workers::ReputationScore)
                            .float()
                            .not_null()
                            .default(1.0),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(Workers::SpotCheckPassCount)
                            .integer()
                            .not_null()
                            .default(0),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(Workers::SpotCheckFailCount)
                            .integer()
                            .not_null()
                            .default(0),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(Workers::AutoRevokedAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_workers_reputation")
                    .table(Workers::Table)
                    .col(Workers::ReputationScore)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(
                Index::drop()
                    .name("idx_workers_reputation")
                    .table(Workers::Table)
                    .to_owned(),
            )
            .await
            .ok();
        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .drop_column(Workers::ReputationScore)
                    .drop_column(Workers::SpotCheckPassCount)
                    .drop_column(Workers::SpotCheckFailCount)
                    .drop_column(Workers::AutoRevokedAt)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum Workers {
    Table,
    ReputationScore,
    SpotCheckPassCount,
    SpotCheckFailCount,
    AutoRevokedAt,
}
