//! `cluster_bandit_arms` — UCB1 arm state for "how many clusters per
//! island" decisions. Composite primary key (island_domain, k_value).
//!
//! Updated each cycle by the steerer with the previous chunk's reward.
//! Survives restarts so the bandit doesn't cold-start every deploy.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterBanditArms::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterBanditArms::IslandDomain)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::KValue)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::Pulls)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::TotalReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::LastReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterBanditArms::UpdatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .primary_key(
                        Index::create()
                            .col(ClusterBanditArms::IslandDomain)
                            .col(ClusterBanditArms::KValue),
                    )
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(ClusterBanditArms::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterBanditArms {
    Table,
    IslandDomain,
    KValue,
    Pulls,
    TotalReward,
    LastReward,
    UpdatedAt,
}
