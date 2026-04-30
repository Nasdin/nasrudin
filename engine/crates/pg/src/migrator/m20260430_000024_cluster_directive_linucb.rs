//! `cluster_directive_linucb` — sufficient statistics for the
//! online contextual bandit (LinUCB) layered on top of the discrete
//! UCB1 arms. One row per (island_domain, action). Each row stores
//! the ridge-regression sufficient statistics A (6×6) and b (6×1)
//! for predicting reward from features [1, s, s², c, c², s·c]
//! where `s` ∈ [0,1] is the LLM-emitted strength and `c` ∈ [0,1]
//! is the normalised multiplier_choice.
//!
//! All math is pure CPU (hand-coded 6×6 matrix ops in
//! `physics_api::steerer::directive_bandit`). No GPU, no offline
//! pipeline, no scheduled training job — every directive_feedback
//! POST applies a rank-1 update inline.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterDirectiveLinucb::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterDirectiveLinucb::IslandDomain)
                            .text()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveLinucb::Action)
                            .text()
                            .not_null(),
                    )
                    // 6×6 = 36 doubles, flat-packed row-major.
                    .col(
                        ColumnDef::new(ClusterDirectiveLinucb::AMatrix)
                            .array(ColumnType::Double)
                            .not_null(),
                    )
                    // 6 doubles.
                    .col(
                        ColumnDef::new(ClusterDirectiveLinucb::BVector)
                            .array(ColumnType::Double)
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveLinucb::Pulls)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .col(
                        ColumnDef::new(ClusterDirectiveLinucb::UpdatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .primary_key(
                        Index::create()
                            .col(ClusterDirectiveLinucb::IslandDomain)
                            .col(ClusterDirectiveLinucb::Action),
                    )
                    .check(
                        Expr::col(ClusterDirectiveLinucb::Action)
                            .is_in(["boost", "exploit", "diversify", "kill"]),
                    )
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(
                Table::drop()
                    .table(ClusterDirectiveLinucb::Table)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterDirectiveLinucb {
    Table,
    IslandDomain,
    Action,
    AMatrix,
    BVector,
    Pulls,
    UpdatedAt,
}
