//! `llm_proposed_targets` — durable record of LLM-proposed
//! self-curriculum targets. Each `SoftTarget` the LLM emits with a
//! stable `target_id` is INSERTed here so the LLM can reason about
//! the curriculum across more than 10-cycle history; the GA can
//! filter "open" targets to bias exploration; analytics can ask
//! "which targets get proved most often?".
//!
//! Status lifecycle: `open` → `proving` → `proved` | `abandoned`.
//! Transitions are LLM-driven via `target_status_updates` in
//! subsequent SteeringConfigs — no automatic semantic matching;
//! the LLM judges whether its own target was achieved by inspecting
//! recent verified theorems in the next cycle's prompt.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(LlmProposedTargets::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(LlmProposedTargets::TargetId)
                            .text()
                            .not_null()
                            .primary_key(),
                    )
                    .col(ColumnDef::new(LlmProposedTargets::Latex).text().not_null())
                    .col(ColumnDef::new(LlmProposedTargets::Domain).text().not_null())
                    .col(
                        ColumnDef::new(LlmProposedTargets::Weight)
                            .double()
                            .not_null()
                            .default(0.5),
                    )
                    .col(
                        ColumnDef::new(LlmProposedTargets::Status)
                            .text()
                            .not_null()
                            .default("open"),
                    )
                    .col(
                        ColumnDef::new(LlmProposedTargets::ProposedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(
                        ColumnDef::new(LlmProposedTargets::UpdatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .check(Expr::col(LlmProposedTargets::Status).is_in([
                        "open",
                        "proving",
                        "proved",
                        "abandoned",
                    ]))
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_llm_proposed_targets_status")
                    .table(LlmProposedTargets::Table)
                    .col(LlmProposedTargets::Status)
                    .col((LlmProposedTargets::ProposedAt, IndexOrder::Desc))
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(
                Index::drop()
                    .name("idx_llm_proposed_targets_status")
                    .to_owned(),
            )
            .await
            .ok();
        manager
            .drop_table(Table::drop().table(LlmProposedTargets::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum LlmProposedTargets {
    Table,
    TargetId,
    Latex,
    Domain,
    Weight,
    Status,
    ProposedAt,
    UpdatedAt,
}
