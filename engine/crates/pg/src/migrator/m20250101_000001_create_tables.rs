use sea_orm_migration::{prelude::*, schema::*};

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        // 1. users
        manager
            .create_table(
                Table::create()
                    .table(Users::Table)
                    .if_not_exists()
                    .col(uuid(Users::Id).primary_key())
                    .col(string_uniq(Users::Email).not_null())
                    .col(text(Users::PasswordHash).not_null())
                    .col(string_null(Users::DisplayName))
                    .col(
                        timestamp_with_time_zone(Users::CreatedAt)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .to_owned(),
            )
            .await?;

        // 2. sessions
        manager
            .create_table(
                Table::create()
                    .table(Sessions::Table)
                    .if_not_exists()
                    .col(uuid(Sessions::Id).primary_key())
                    .col(uuid(Sessions::UserId).not_null())
                    .col(string_uniq(Sessions::Token).not_null())
                    .col(timestamp_with_time_zone(Sessions::ExpiresAt).not_null())
                    .col(
                        timestamp_with_time_zone(Sessions::CreatedAt)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_sessions_user_id")
                            .from(Sessions::Table, Sessions::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        // 3. saved_searches
        manager
            .create_table(
                Table::create()
                    .table(SavedSearches::Table)
                    .if_not_exists()
                    .col(uuid(SavedSearches::Id).primary_key())
                    .col(uuid(SavedSearches::UserId).not_null())
                    .col(text(SavedSearches::Latex).not_null())
                    .col(string_null(SavedSearches::Label))
                    .col(
                        timestamp_with_time_zone(SavedSearches::CreatedAt)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_saved_searches_user_id")
                            .from(SavedSearches::Table, SavedSearches::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        // 4. user_preferences
        manager
            .create_table(
                Table::create()
                    .table(UserPreferences::Table)
                    .if_not_exists()
                    .col(uuid(UserPreferences::UserId).primary_key())
                    .col(
                        json_binary(UserPreferences::Preferences)
                            .not_null()
                            .default(Expr::val("{}")),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_user_preferences_user_id")
                            .from(UserPreferences::Table, UserPreferences::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        // 5. workers
        manager
            .create_table(
                Table::create()
                    .table(Workers::Table)
                    .if_not_exists()
                    .col(text(Workers::Id).primary_key())
                    .col(string_null(Workers::Name))
                    .col(string_null(Workers::Host))
                    .col(
                        timestamp_with_time_zone(Workers::LastSeen)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(big_integer(Workers::TheoremsContributed).not_null().default(0))
                    .col(text(Workers::Status).not_null().default("inactive"))
                    .to_owned(),
            )
            .await?;

        // Indexes for common query patterns
        manager
            .create_index(
                Index::create()
                    .name("idx_sessions_user_id")
                    .table(Sessions::Table)
                    .col(Sessions::UserId)
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_sessions_token")
                    .table(Sessions::Table)
                    .col(Sessions::Token)
                    .unique()
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_saved_searches_user_id")
                    .table(SavedSearches::Table)
                    .col(SavedSearches::UserId)
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_workers_status")
                    .table(Workers::Table)
                    .col(Workers::Status)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(Workers::Table).to_owned())
            .await?;
        manager
            .drop_table(Table::drop().table(UserPreferences::Table).to_owned())
            .await?;
        manager
            .drop_table(Table::drop().table(SavedSearches::Table).to_owned())
            .await?;
        manager
            .drop_table(Table::drop().table(Sessions::Table).to_owned())
            .await?;
        manager
            .drop_table(Table::drop().table(Users::Table).to_owned())
            .await?;
        Ok(())
    }
}

#[derive(DeriveIden)]
enum Users {
    Table,
    Id,
    Email,
    PasswordHash,
    DisplayName,
    CreatedAt,
}

#[derive(DeriveIden)]
enum Sessions {
    Table,
    Id,
    UserId,
    Token,
    ExpiresAt,
    CreatedAt,
}

#[derive(DeriveIden)]
enum SavedSearches {
    Table,
    Id,
    UserId,
    Latex,
    Label,
    CreatedAt,
}

#[derive(DeriveIden)]
enum UserPreferences {
    Table,
    UserId,
    Preferences,
}

#[derive(DeriveIden)]
enum Workers {
    Table,
    Id,
    Name,
    Host,
    LastSeen,
    TheoremsContributed,
    Status,
}
