//! `cluster_directive_arms` — UCB1 arm state for per-cluster directive
//! multipliers. PK is the 4-tuple (island_domain, action, strength_bucket,
//! multiplier_choice). 6 islands × 4 actions × 5 buckets × 5 choices = 600
//! rows materialised at API boot.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterDirectiveArms::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::IslandDomain)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::Action)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::StrengthBucket)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::MultiplierChoice)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::Pulls)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::TotalReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::LastReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveArms::UpdatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .primary_key(
                        Index::create()
                            .col(ClusterDirectiveArms::IslandDomain)
                            .col(ClusterDirectiveArms::Action)
                            .col(ClusterDirectiveArms::StrengthBucket)
                            .col(ClusterDirectiveArms::MultiplierChoice),
                    )
                    .check(
                        Expr::col(ClusterDirectiveArms::Action)
                            .is_in(["boost", "exploit", "diversify", "kill"]),
                    )
                    .check(Expr::col(ClusterDirectiveArms::StrengthBucket).between(0, 4))
                    .check(Expr::col(ClusterDirectiveArms::MultiplierChoice).between(0, 4))
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_directive_arms_slot")
                    .table(ClusterDirectiveArms::Table)
                    .col(ClusterDirectiveArms::IslandDomain)
                    .col(ClusterDirectiveArms::Action)
                    .col(ClusterDirectiveArms::StrengthBucket)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(Index::drop().name("idx_directive_arms_slot").to_owned())
            .await
            .ok();
        manager
            .drop_table(
                Table::drop()
                    .table(ClusterDirectiveArms::Table)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterDirectiveArms {
    Table,
    IslandDomain,
    Action,
    StrengthBucket,
    MultiplierChoice,
    Pulls,
    TotalReward,
    LastReward,
    UpdatedAt,
}
