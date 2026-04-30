use sea_orm_migration::prelude::*;

mod m20250101_000001_create_tables;
mod m20260428_000002_api_keys;
mod m20260501_000003_theorems;
mod m20260501_000004_workers_extend;
mod m20260601_000005_search_indexes;
mod m20260710_000006_user_llm_keys;
mod m20260801_000007_conjecture_jobs;
mod m20260801_000008_conjecture_events;
mod m20260429_000009_billing;
mod m20260429_000010_billing_events;
mod m20260429_000011_targeted_search_usage;
mod m20260429_000012_api_usage_daily;
mod m20260901_000009_manual_verifications;
mod m20260901_000010_worker_reputation;
mod m20260901_000011_worker_verified;
mod m20260430_000013_conjecture_paper_draft;
mod m20260501_000001_cluster_steering;
mod m20260501_000002_paid_job_quota;
mod m20260501_000003_research_credits;

pub struct Migrator;

#[async_trait::async_trait]
impl MigratorTrait for Migrator {
    fn migrations() -> Vec<Box<dyn MigrationTrait>> {
        vec![
            Box::new(m20250101_000001_create_tables::Migration),
            Box::new(m20260428_000002_api_keys::Migration),
            Box::new(m20260501_000003_theorems::Migration),
            Box::new(m20260501_000004_workers_extend::Migration),
            Box::new(m20260601_000005_search_indexes::Migration),
            Box::new(m20260710_000006_user_llm_keys::Migration),
            Box::new(m20260801_000007_conjecture_jobs::Migration),
            Box::new(m20260801_000008_conjecture_events::Migration),
            Box::new(m20260429_000009_billing::Migration),
            Box::new(m20260429_000010_billing_events::Migration),
            Box::new(m20260429_000011_targeted_search_usage::Migration),
            Box::new(m20260429_000012_api_usage_daily::Migration),
            Box::new(m20260901_000009_manual_verifications::Migration),
            Box::new(m20260901_000010_worker_reputation::Migration),
            Box::new(m20260901_000011_worker_verified::Migration),
            Box::new(m20260430_000013_conjecture_paper_draft::Migration),
            Box::new(m20260501_000001_cluster_steering::Migration),
            Box::new(m20260501_000002_paid_job_quota::Migration),
            Box::new(m20260501_000003_research_credits::Migration),
        ]
    }
}
