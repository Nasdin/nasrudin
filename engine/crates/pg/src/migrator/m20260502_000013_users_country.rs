//! `users.country_code` column — ISO 3166-1 alpha-2 (e.g. "US", "GB").
//!
//! Surfaced on the public `/api/workers` endpoint so the Workers page can
//! show a flag / country alongside each worker. Null when the user hasn't
//! set it (default) and for anonymous workers (no user account at all).

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .add_column_if_not_exists(ColumnDef::new(Users::CountryCode).char_len(2).null())
                    .to_owned(),
            )
            .await
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .drop_column(Users::CountryCode)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum Users {
    Table,
    CountryCode,
}
