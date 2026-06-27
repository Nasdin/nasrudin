//! Per-cycle history table for the LLM-driven cluster steerer.
//!
//! Each row captures one steering cycle: the prompt context (history +
//! demand), the model's response (`config_json`), and the post-cycle
//! outcome (`outcome_json`) populated when the next cycle closes this
//! one. `validation_failed=true` means the model's reply did not parse
//! or did not satisfy the SteeringConfig schema; the cycle then reuses
//! the last-known-good config and records that fact here.
//!
//! `scope` is constrained to "B" (paid jobs running, mutation knobs
//! locked) or "C" (full LLM authority). Indexed on `started_at` because
//! every read path (history fetch, admin recent listing) is newest-first.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ClusterSteering::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ClusterSteering::Id)
                            .uuid()
                            .not_null()
                            .primary_key(),
                    )
                    .col(
                        ColumnDef::new(ClusterSteering::StartedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(
                        ColumnDef::new(ClusterSteering::EndedAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .col(ColumnDef::new(ClusterSteering::Scope).text().not_null())
                    .col(
                        ColumnDef::new(ClusterSteering::ConfigJson)
                            .json_binary()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ClusterSteering::OutcomeJson)
                            .json_binary()
                            .null(),
                    )
                    .col(
                        ColumnDef::new(ClusterSteering::ValidationFailed)
                            .boolean()
                            .not_null()
                            .default(false),
                    )
                    .col(ColumnDef::new(ClusterSteering::ModelId).text().not_null())
                    .col(
                        ColumnDef::new(ClusterSteering::PromptTokens)
                            .integer()
                            .null(),
                    )
                    .col(
                        ColumnDef::new(ClusterSteering::CompletionTokens)
                            .integer()
                            .null(),
                    )
                    .check(Expr::col(ClusterSteering::Scope).is_in(["B", "C"]))
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_cluster_steering_started_at")
                    .table(ClusterSteering::Table)
                    .col(ClusterSteering::StartedAt)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(
                Index::drop()
                    .name("idx_cluster_steering_started_at")
                    .table(ClusterSteering::Table)
                    .to_owned(),
            )
            .await
            .ok();
        manager
            .drop_table(Table::drop().table(ClusterSteering::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ClusterSteering {
    Table,
    Id,
    StartedAt,
    EndedAt,
    Scope,
    ConfigJson,
    OutcomeJson,
    ValidationFailed,
    ModelId,
    PromptTokens,
    CompletionTokens,
}
