//! `cluster_compute_arms` — UCB1 arm state for the compute-scaling
//! bandit. Composite primary key (island_domain, strength_bucket,
//! multiplier_choice). Workers UCB1-select a population_size /
//! generations multiplier when the LLM emits a compute_directive,
//! letting the system spend MORE compute on islands where extra
//! exploration translates to discoveries — AlphaProof-style
//! test-time-compute scaling at the steering layer.
//!
//! 6 islands × 5 strength buckets × 5 multiplier choices = 150 rows
//! materialised at API boot.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterComputeArms::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterComputeArms::IslandDomain)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeArms::StrengthBucket)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeArms::MultiplierChoice)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeArms::Pulls)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeArms::TotalReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeArms::LastReward)
                            .double()
                            .not_null()
                            .default(0.0),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeArms::UpdatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .primary_key(
                        Index::create()
                            .col(ClusterComputeArms::IslandDomain)
                            .col(ClusterComputeArms::StrengthBucket)
                            .col(ClusterComputeArms::MultiplierChoice),
                    )
                    .check(Expr::col(ClusterComputeArms::StrengthBucket).between(0, 4))
                    .check(Expr::col(ClusterComputeArms::MultiplierChoice).between(0, 4))
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(
                Table::drop()
                    .table(ClusterComputeArms::Table)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterComputeArms {
    Table,
    IslandDomain,
    StrengthBucket,
    MultiplierChoice,
    Pulls,
    TotalReward,
    LastReward,
    UpdatedAt,
}
