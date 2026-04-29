use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ApiUsageDaily::Table)
                    .if_not_exists()
                    .col(ColumnDef::new(ApiUsageDaily::UserId).uuid().not_null())
                    .col(ColumnDef::new(ApiUsageDaily::Day).date().not_null())
                    .col(
                        ColumnDef::new(ApiUsageDaily::RequestCount)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .primary_key(
                        Index::create()
                            .col(ApiUsageDaily::UserId)
                            .col(ApiUsageDaily::Day),
                    )
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(ApiUsageDaily::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ApiUsageDaily {
    Table,
    UserId,
    Day,
    RequestCount,
}
