//! Per-API-key trust override + spot-check rate.
//!
//! Both NULL by default — the trust resolver falls back to the owning
//! user's flags when either is unset. Set `trust_override = TRUE` to
//! force a specific worker key into the trust-bypass path even when
//! the user is not blanket-trusted; set to `FALSE` to lock a key out
//! of bypass even when the user is trusted.

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(ApiKeys::Table)
                    .add_column_if_not_exists(
                        ColumnDef::new(ApiKeys::TrustOverride).boolean().null(),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(ApiKeys::SpotCheckRate).integer().null(),
                    )
                    .to_owned(),
            )
            .await
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(ApiKeys::Table)
                    .drop_column(ApiKeys::TrustOverride)
                    .drop_column(ApiKeys::SpotCheckRate)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum ApiKeys {
    Table,
    TrustOverride,
    SpotCheckRate,
}
