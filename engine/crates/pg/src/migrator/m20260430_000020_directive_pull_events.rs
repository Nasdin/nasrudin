//! `directive_pull_events` — raw event log for the per-cluster
//! directive bandit. Every reward observation INSERTs a row here in
//! addition to updating the running aggregate in
//! `cluster_directive_arms`. This separation lets us replay the
//! event stream for offline policy training (LinUCB / contextual
//! bandits / value networks) without losing the running
//! aggregates the live UCB1 selection depends on.
//!
//! Retention: 30 days; older rows can be archived or deleted via a
//! cron similar to the cluster_reports purge.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(DirectivePullEvents::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(DirectivePullEvents::Id)
                            .big_integer()
                            .not_null()
                            .auto_increment()
                            .primary_key(),
                    )
                    .col(
                        ColumnDef::new(DirectivePullEvents::IslandDomain)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(DirectivePullEvents::Action)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(DirectivePullEvents::StrengthBucket)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(DirectivePullEvents::MultiplierChoice)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(DirectivePullEvents::Reward)
                            .double()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(DirectivePullEvents::ReceivedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_directive_events_recent")
                    .table(DirectivePullEvents::Table)
                    .col(DirectivePullEvents::IslandDomain)
                    .col(DirectivePullEvents::Action)
                    .col((DirectivePullEvents::ReceivedAt, IndexOrder::Desc))
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(Index::drop().name("idx_directive_events_recent").to_owned())
            .await
            .ok();
        manager
            .drop_table(Table::drop().table(DirectivePullEvents::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum DirectivePullEvents {
    Table,
    Id,
    IslandDomain,
    Action,
    StrengthBucket,
    MultiplierChoice,
    Reward,
    ReceivedAt,
}
