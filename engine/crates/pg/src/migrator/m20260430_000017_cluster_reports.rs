//! `cluster_reports` — per-chunk cluster summaries pushed by workers.
//!
//! Each worker computes K-means inside each domain island at the end
//! of every chunk and POSTs a `ClusterSummary` per cluster. The API
//! steerer reads recent rows to compute UCB1 reward and to populate
//! the LLM prompt. Retention: 7 days (cron deletes older rows; the
//! bandit arms hold the long-running statistics).

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterReports::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterReports::Id)
                            .big_integer()
                            .not_null()
                            .auto_increment()
                            .primary_key(),
                    )
                    .col(ColumnDef::new(ClusterReports::WorkerId).uuid().not_null())
                    .col(
                        ColumnDef::new(ClusterReports::ChunkIndex)
                            .big_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::KUsed)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::IslandDomain)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::ClusterId)
                            .small_integer()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::Summary)
                            .json_binary()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterReports::ReceivedAt)
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
                    .name("idx_cluster_reports_recent")
                    .table(ClusterReports::Table)
                    .col(ClusterReports::IslandDomain)
                    .col((ClusterReports::ReceivedAt, IndexOrder::Desc))
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_cluster_reports_chunk")
                    .table(ClusterReports::Table)
                    .col(ClusterReports::WorkerId)
                    .col(ClusterReports::ChunkIndex)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(
                Index::drop()
                    .name("idx_cluster_reports_recent")
                    .to_owned(),
            )
            .await
            .ok();
        manager
            .drop_index(
                Index::drop()
                    .name("idx_cluster_reports_chunk")
                    .to_owned(),
            )
            .await
            .ok();
        manager
            .drop_table(Table::drop().table(ClusterReports::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterReports {
    Table,
    Id,
    WorkerId,
    ChunkIndex,
    KUsed,
    IslandDomain,
    ClusterId,
    Summary,
    ReceivedAt,
}
