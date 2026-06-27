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
                    .add_column(
                        ColumnDef::new(Users::PlanTier)
                            .text()
                            .not_null()
                            .default("free"),
                    )
                    .add_column(ColumnDef::new(Users::StripeCustomerId).text().null())
                    .add_column(ColumnDef::new(Users::StripeSubscriptionId).text().null())
                    .add_column(
                        ColumnDef::new(Users::CurrentPeriodEnd)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .add_column(
                        ColumnDef::new(Users::PlanCycleStart)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_users_stripe_customer_id")
                    .table(Users::Table)
                    .col(Users::StripeCustomerId)
                    .unique()
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(
                Index::drop()
                    .name("idx_users_stripe_customer_id")
                    .to_owned(),
            )
            .await?;
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .drop_column(Users::PlanCycleStart)
                    .drop_column(Users::CurrentPeriodEnd)
                    .drop_column(Users::StripeSubscriptionId)
                    .drop_column(Users::StripeCustomerId)
                    .drop_column(Users::PlanTier)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum Users {
    Table,
    PlanTier,
    StripeCustomerId,
    StripeSubscriptionId,
    CurrentPeriodEnd,
    PlanCycleStart,
}
