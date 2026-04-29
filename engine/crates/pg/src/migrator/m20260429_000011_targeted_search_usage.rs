use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(TargetedSearchUsage::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(TargetedSearchUsage::Id)
                            .uuid()
                            .not_null()
                            .primary_key()
                            .default(Expr::cust("gen_random_uuid()")),
                    )
                    .col(
                        ColumnDef::new(TargetedSearchUsage::UserId)
                            .uuid()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(TargetedSearchUsage::ConjectureJobId)
                            .uuid()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(TargetedSearchUsage::PeriodStart)
                            .timestamp_with_time_zone()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(TargetedSearchUsage::CreatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_tsu_user")
                            .from(TargetedSearchUsage::Table, TargetedSearchUsage::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;
        manager
            .create_index(
                Index::create()
                    .name("idx_tsu_user_period")
                    .table(TargetedSearchUsage::Table)
                    .col(TargetedSearchUsage::UserId)
                    .col(TargetedSearchUsage::PeriodStart)
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(
                Table::drop()
                    .table(TargetedSearchUsage::Table)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum TargetedSearchUsage {
    Table,
    Id,
    UserId,
    ConjectureJobId,
    PeriodStart,
    CreatedAt,
}

#[derive(DeriveIden)]
enum Users {
    Table,
    Id,
}
