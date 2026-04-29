//! Audit log for user-triggered "Verify with Lake" actions (P-Task 4).
//!
//! Every call to `POST /api/theorems/{id}/verify` writes one row.
//! Used for ops visibility and abuse detection (a user mass-clicking
//! verify on every theorem trips the rate limit, but the audit table
//! is the long-term record).

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ManualVerifications::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ManualVerifications::Id)
                            .big_integer()
                            .not_null()
                            .auto_increment()
                            .primary_key(),
                    )
                    .col(
                        ColumnDef::new(ManualVerifications::ActorId)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ManualVerifications::TheoremId)
                            .binary()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ManualVerifications::RequestedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(
                        ColumnDef::new(ManualVerifications::Result)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ManualVerifications::DurationMs)
                            .integer()
                            .not_null()
                            .default(0),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_manual_verifications_actor")
                    .table(ManualVerifications::Table)
                    .col(ManualVerifications::ActorId)
                    .col(ManualVerifications::RequestedAt)
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_manual_verifications_theorem")
                    .table(ManualVerifications::Table)
                    .col(ManualVerifications::TheoremId)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(ManualVerifications::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ManualVerifications {
    Table,
    Id,
    ActorId,
    TheoremId,
    RequestedAt,
    Result,
    DurationMs,
}
