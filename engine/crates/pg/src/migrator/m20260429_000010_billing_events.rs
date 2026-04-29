use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(BillingEvents::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(BillingEvents::Id)
                            .uuid()
                            .not_null()
                            .primary_key()
                            .default(Expr::cust("gen_random_uuid()")),
                    )
                    .col(
                        ColumnDef::new(BillingEvents::StripeEventId)
                            .text()
                            .not_null()
                            .unique_key(),
                    )
                    .col(ColumnDef::new(BillingEvents::EventType).text().not_null())
                    .col(
                        ColumnDef::new(BillingEvents::Payload)
                            .json_binary()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(BillingEvents::ReceivedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(
                        ColumnDef::new(BillingEvents::ProcessedAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .col(ColumnDef::new(BillingEvents::ProcessError).text().null())
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(BillingEvents::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum BillingEvents {
    Table,
    Id,
    StripeEventId,
    EventType,
    Payload,
    ReceivedAt,
    ProcessedAt,
    ProcessError,
}
