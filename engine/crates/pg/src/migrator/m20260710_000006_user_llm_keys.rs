use sea_orm_migration::{prelude::*, schema::*};

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(UserLlmKeys::Table)
                    .if_not_exists()
                    .col(uuid(UserLlmKeys::UserId).not_null())
                    .col(string(UserLlmKeys::Provider).not_null())
                    .col(blob(UserLlmKeys::EncryptedKey).not_null())
                    .col(string(UserLlmKeys::KeyHint).not_null())
                    .col(
                        timestamp_with_time_zone(UserLlmKeys::CreatedAt)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(timestamp_with_time_zone_null(UserLlmKeys::LastUsedAt))
                    .primary_key(
                        Index::create()
                            .col(UserLlmKeys::UserId)
                            .col(UserLlmKeys::Provider),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_user_llm_keys_user_id")
                            .from(UserLlmKeys::Table, UserLlmKeys::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(UserLlmKeys::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum UserLlmKeys {
    Table,
    UserId,
    Provider,
    EncryptedKey,
    KeyHint,
    CreatedAt,
    LastUsedAt,
}

#[derive(DeriveIden)]
enum Users {
    Table,
    Id,
}
