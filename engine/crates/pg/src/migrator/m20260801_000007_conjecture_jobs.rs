use sea_orm_migration::prelude::*;
use sea_orm_migration::sea_orm::ConnectionTrait;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ConjectureJobs::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(ConjectureJobs::Id)
                            .uuid()
                            .not_null()
                            .primary_key()
                            .default(Expr::cust("gen_random_uuid()")),
                    )
                    .col(ColumnDef::new(ConjectureJobs::OwnerId).uuid().not_null())
                    .col(ColumnDef::new(ConjectureJobs::State).text().not_null())
                    .col(ColumnDef::new(ConjectureJobs::Outcome).text().null())
                    .col(ColumnDef::new(ConjectureJobs::Hunch).text().not_null())
                    .col(ColumnDef::new(ConjectureJobs::DomainHint).text().null())
                    .col(ColumnDef::new(ConjectureJobs::Provider).text().not_null())
                    .col(ColumnDef::new(ConjectureJobs::Model).text().not_null())
                    .col(
                        ColumnDef::new(ConjectureJobs::Suggestions)
                            .json_binary()
                            .null(),
                    )
                    .col(ColumnDef::new(ConjectureJobs::ChosenIndex).integer().null())
                    .col(ColumnDef::new(ConjectureJobs::Seed).json_binary().null())
                    .col(
                        ColumnDef::new(ConjectureJobs::Budget)
                            .json_binary()
                            .not_null(),
                    )
                    .col(ColumnDef::new(ConjectureJobs::ClaimedBy).text().null())
                    .col(
                        ColumnDef::new(ConjectureJobs::ClaimedAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .col(
                        ColumnDef::new(ConjectureJobs::LeaseExpiresAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .col(
                        ColumnDef::new(ConjectureJobs::LastHeartbeatAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .col(
                        ColumnDef::new(ConjectureJobs::CandidatesAttempted)
                            .integer()
                            .not_null()
                            .default(0),
                    )
                    .col(
                        ColumnDef::new(ConjectureJobs::CandidatesVerified)
                            .integer()
                            .not_null()
                            .default(0),
                    )
                    .col(
                        ColumnDef::new(ConjectureJobs::VerifiedTheoremIds)
                            .array(ColumnType::Binary(8))
                            .null(),
                    )
                    .col(
                        ColumnDef::new(ConjectureJobs::CreatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(
                        ColumnDef::new(ConjectureJobs::CompletedAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_conjecture_jobs_owner_id")
                            .from(ConjectureJobs::Table, ConjectureJobs::OwnerId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        // Owner-scoped lookups (`/api/me/conjectures` listing).
        manager
            .create_index(
                Index::create()
                    .name("idx_conjecture_jobs_owner")
                    .table(ConjectureJobs::Table)
                    .col(ConjectureJobs::OwnerId)
                    .col(ConjectureJobs::CreatedAt)
                    .to_owned(),
            )
            .await?;

        // Partial index for the worker claim path (Phase E).
        // Sea-ORM's index builder doesn't express WHERE clauses, so emit raw SQL.
        let conn = manager.get_connection();
        conn.execute_unprepared(
            "CREATE INDEX IF NOT EXISTS idx_conjecture_jobs_queueable \
             ON conjecture_jobs (created_at) \
             WHERE state = 'QueuedForWorker' AND claimed_by IS NULL",
        )
        .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();
        conn.execute_unprepared("DROP INDEX IF EXISTS idx_conjecture_jobs_queueable")
            .await?;
        manager
            .drop_table(Table::drop().table(ConjectureJobs::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ConjectureJobs {
    Table,
    Id,
    OwnerId,
    State,
    Outcome,
    Hunch,
    DomainHint,
    Provider,
    Model,
    Suggestions,
    ChosenIndex,
    Seed,
    Budget,
    ClaimedBy,
    ClaimedAt,
    LeaseExpiresAt,
    LastHeartbeatAt,
    CandidatesAttempted,
    CandidatesVerified,
    VerifiedTheoremIds,
    CreatedAt,
    CompletedAt,
}

#[derive(DeriveIden)]
enum Users {
    Table,
    Id,
}
