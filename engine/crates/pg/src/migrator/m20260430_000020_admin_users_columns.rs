//! Admin-panel user flags: is_admin, is_trusted, optional spot_check_rate.
//!
//! `spot_check_rate`: NULL = use env default (TRUSTED_SPOT_CHECK_RATE);
//! 0 = pure trust (never lake-promote); 1 = check every (effectively
//! untrusted); N>1 = 1-in-N. The fallback chain is
//! `api_keys.spot_check_rate → users.spot_check_rate → env default`.

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
                    .add_column_if_not_exists(
                        ColumnDef::new(Users::IsAdmin)
                            .boolean()
                            .not_null()
                            .default(false),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(Users::IsTrusted)
                            .boolean()
                            .not_null()
                            .default(false),
                    )
                    .add_column_if_not_exists(
                        ColumnDef::new(Users::SpotCheckRate).integer().null(),
                    )
                    .to_owned(),
            )
            .await
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .drop_column(Users::IsAdmin)
                    .drop_column(Users::IsTrusted)
                    .drop_column(Users::SpotCheckRate)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum Users {
    Table,
    IsAdmin,
    IsTrusted,
    SpotCheckRate,
}
