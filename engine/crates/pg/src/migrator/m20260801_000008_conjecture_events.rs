use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ConjectureEvents::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ConjectureEvents::Id)
                            .big_integer()
                            .not_null()
                            .auto_increment()
                            .primary_key(),
                    )
                    .col(ColumnDef::new(ConjectureEvents::JobId).uuid().not_null())
                    .col(ColumnDef::new(ConjectureEvents::Kind).text().not_null())
                    .col(
                        ColumnDef::new(ConjectureEvents::Payload)
                            .json_binary()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(ConjectureEvents::At)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_conjecture_events_job_id")
                            .from(ConjectureEvents::Table, ConjectureEvents::JobId)
                            .to(ConjectureJobs::Table, ConjectureJobs::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_conjecture_events_job")
                    .table(ConjectureEvents::Table)
                    .col(ConjectureEvents::JobId)
                    .col(ConjectureEvents::Id)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(ConjectureEvents::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ConjectureEvents {
    Table,
    Id,
    JobId,
    Kind,
    Payload,
    At,
}

#[derive(DeriveIden)]
enum ConjectureJobs {
    Table,
    Id,
}
