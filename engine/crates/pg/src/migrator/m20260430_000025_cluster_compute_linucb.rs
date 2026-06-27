//! `cluster_compute_linucb` — per-island LinUCB sufficient
//! statistics for the compute-scaling bandit. Mirrors
//! `cluster_directive_linucb` minus the action dimension since
//! compute is a single global knob, not per-action.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterComputeLinucb::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterComputeLinucb::IslandDomain)
                            .text()
                            .not_null()
                            .primary_key(),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeLinucb::AMatrix)
                            .array(ColumnType::Double)
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeLinucb::BVector)
                            .array(ColumnType::Double)
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeLinucb::Pulls)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .col(
                        ColumnDef::new(ClusterComputeLinucb::UpdatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(ClusterComputeLinucb::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterComputeLinucb {
    Table,
    IslandDomain,
    AMatrix,
    BVector,
    Pulls,
    UpdatedAt,
}
