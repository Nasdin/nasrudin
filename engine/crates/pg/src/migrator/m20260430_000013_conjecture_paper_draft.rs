use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(ConjectureJobs::Table)
                    .add_column(ColumnDef::new(ConjectureJobs::PaperDraft).text().null())
                    .to_owned(),
            )
            .await
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(ConjectureJobs::Table)
                    .drop_column(ConjectureJobs::PaperDraft)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum ConjectureJobs {
    Table,
    PaperDraft,
}
