//! Personal library — saved theorems, optional folders, and inline notes.
//!
//! Backs the pricing claims:
//!   Free: "Save up to 50 theorems" — enforced via `PlanTier::library_max`
//!     in the API handler before insert.
//!   Researcher+: "Unlimited library, folders, private notes" — same handler
//!     allows arbitrary count.
//!
//! Notes:
//! - `theorem_id` is `bytea` to match `theorems.id` (8-byte hash).
//! - Composite PK (user_id, theorem_id) prevents duplicate saves.
//! - `folder_id` ON DELETE SET NULL — deleting a folder leaves theorems
//!   in the "ungrouped" state rather than removing them.

use sea_orm_migration::{prelude::*, schema::*};

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(LibraryFolders::Table)
                    .if_not_exists()
                    .col(uuid(LibraryFolders::Id).not_null().primary_key())
                    .col(uuid(LibraryFolders::UserId).not_null())
                    .col(string(LibraryFolders::Name).not_null())
                    .col(string_null(LibraryFolders::Color))
                    .col(
                        timestamp_with_time_zone(LibraryFolders::CreatedAt)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(
                        timestamp_with_time_zone(LibraryFolders::UpdatedAt)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_library_folders_user_id")
                            .from(LibraryFolders::Table, LibraryFolders::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_library_folders_user_name_unique")
                    .table(LibraryFolders::Table)
                    .col(LibraryFolders::UserId)
                    .col(LibraryFolders::Name)
                    .unique()
                    .to_owned(),
            )
            .await?;

        manager
            .create_table(
                Table::create()
                    .table(UserSavedTheorems::Table)
                    .if_not_exists()
                    .col(uuid(UserSavedTheorems::UserId).not_null())
                    .col(blob(UserSavedTheorems::TheoremId).not_null())
                    .col(
                        timestamp_with_time_zone(UserSavedTheorems::SavedAt)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(uuid_null(UserSavedTheorems::FolderId))
                    .col(text_null(UserSavedTheorems::Note))
                    .col(string_null(UserSavedTheorems::Label))
                    .primary_key(
                        Index::create()
                            .col(UserSavedTheorems::UserId)
                            .col(UserSavedTheorems::TheoremId),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_user_saved_theorems_user_id")
                            .from(UserSavedTheorems::Table, UserSavedTheorems::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_user_saved_theorems_folder_id")
                            .from(UserSavedTheorems::Table, UserSavedTheorems::FolderId)
                            .to(LibraryFolders::Table, LibraryFolders::Id)
                            .on_delete(ForeignKeyAction::SetNull),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_user_saved_theorems_user_saved_at")
                    .table(UserSavedTheorems::Table)
                    .col(UserSavedTheorems::UserId)
                    .col((UserSavedTheorems::SavedAt, IndexOrder::Desc))
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_user_saved_theorems_folder")
                    .table(UserSavedTheorems::Table)
                    .col(UserSavedTheorems::FolderId)
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(UserSavedTheorems::Table).to_owned())
            .await?;
        manager
            .drop_table(Table::drop().table(LibraryFolders::Table).to_owned())
            .await?;
        Ok(())
    }
}

#[derive(DeriveIden)]
enum LibraryFolders {
    Table,
    Id,
    UserId,
    Name,
    Color,
    CreatedAt,
    UpdatedAt,
}

#[derive(DeriveIden)]
enum UserSavedTheorems {
    Table,
    UserId,
    TheoremId,
    SavedAt,
    FolderId,
    Note,
    Label,
}

#[derive(DeriveIden)]
enum Users {
    Table,
    Id,
}
