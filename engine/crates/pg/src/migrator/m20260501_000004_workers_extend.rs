use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .add_column(
                        ColumnDef::new(Workers::LastHeartbeatAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .add_column(
                        ColumnDef::new(Workers::LastContributionAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .add_column(
                        ColumnDef::new(Workers::CurrentGeneration)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .add_column(
                        ColumnDef::new(Workers::TheoremsProducedTotal)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .add_column(
                        ColumnDef::new(Workers::UptimeSeconds)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .add_column(ColumnDef::new(Workers::EngineGitSha).text().null())
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .drop_column(Workers::EngineGitSha)
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .drop_column(Workers::UptimeSeconds)
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .drop_column(Workers::TheoremsProducedTotal)
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .drop_column(Workers::CurrentGeneration)
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .drop_column(Workers::LastContributionAt)
                    .to_owned(),
            )
            .await?;

        manager
            .alter_table(
                Table::alter()
                    .table(Workers::Table)
                    .drop_column(Workers::LastHeartbeatAt)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }
}

#[derive(DeriveIden)]
enum Workers {
    Table,
    LastHeartbeatAt,
    LastContributionAt,
    CurrentGeneration,
    TheoremsProducedTotal,
    UptimeSeconds,
    EngineGitSha,
}
