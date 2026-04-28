use sea_orm_migration::prelude::*;

mod m20250101_000001_create_tables;
mod m20260428_000002_api_keys;
mod m20260501_000003_theorems;

pub struct Migrator;

#[async_trait::async_trait]
impl MigratorTrait for Migrator {
    fn migrations() -> Vec<Box<dyn MigrationTrait>> {
        vec![
            Box::new(m20250101_000001_create_tables::Migration),
            Box::new(m20260428_000002_api_keys::Migration),
            Box::new(m20260501_000003_theorems::Migration),
        ]
    }
}
