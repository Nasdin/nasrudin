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
mod m20260901_000012_theorem_user_email;
mod m20260502_000013_users_country;
mod m20260430_000013_conjecture_paper_draft;
mod m20260501_000001_cluster_steering;
mod m20260501_000002_paid_job_quota;
mod m20260501_000003_research_credits;
mod m20260501_000004_paid_job_allocated_slots;
mod m20260430_000014_user_oauth_identity;
mod m20260430_000015_library;
mod m20260430_000016_firebase_auth;
mod m20260430_000020_admin_users_columns;
mod m20260430_000021_admin_api_keys_columns;
mod m20260430_000022_admin_audit_log;
mod m20260430_000023_impersonation_sessions;
mod m20260430_000024_email_outbox;
mod m20260430_000025_refund_records;
mod m20260430_000026_bulk_runs;
mod m20260430_000027_last_admin_trigger;
mod m20260430_000017_cluster_reports;
mod m20260430_000018_cluster_bandit_arms;
mod m20260430_000019_cluster_directive_arms;
mod m20260430_000020_directive_pull_events;
mod m20260430_000021_cluster_compute_arms;
mod m20260430_000022_expand_directive_arm_choices;
mod m20260430_000023_llm_proposed_targets;
mod m20260430_000024_cluster_directive_linucb;
mod m20260430_000025_cluster_compute_linucb;
mod m20260430_000028_theorems_trust_state;
mod m20260430_000029_drop_email_outbox;
mod m20260501_000020_query_optimization_indexes;
mod m20260430_000030_user_sponsorships;

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
            Box::new(m20260901_000012_theorem_user_email::Migration),
            Box::new(m20260502_000013_users_country::Migration),
            Box::new(m20260430_000013_conjecture_paper_draft::Migration),
            Box::new(m20260501_000001_cluster_steering::Migration),
            Box::new(m20260501_000002_paid_job_quota::Migration),
            Box::new(m20260501_000003_research_credits::Migration),
            Box::new(m20260501_000004_paid_job_allocated_slots::Migration),
            Box::new(m20260430_000014_user_oauth_identity::Migration),
            Box::new(m20260430_000015_library::Migration),
            Box::new(m20260430_000016_firebase_auth::Migration),
            Box::new(m20260430_000020_admin_users_columns::Migration),
            Box::new(m20260430_000021_admin_api_keys_columns::Migration),
            Box::new(m20260430_000022_admin_audit_log::Migration),
            Box::new(m20260430_000023_impersonation_sessions::Migration),
            Box::new(m20260430_000024_email_outbox::Migration),
            Box::new(m20260430_000025_refund_records::Migration),
            Box::new(m20260430_000026_bulk_runs::Migration),
            Box::new(m20260430_000027_last_admin_trigger::Migration),
            Box::new(m20260430_000017_cluster_reports::Migration),
            Box::new(m20260430_000018_cluster_bandit_arms::Migration),
            Box::new(m20260430_000019_cluster_directive_arms::Migration),
            Box::new(m20260430_000020_directive_pull_events::Migration),
            Box::new(m20260430_000021_cluster_compute_arms::Migration),
            Box::new(m20260430_000022_expand_directive_arm_choices::Migration),
            Box::new(m20260430_000023_llm_proposed_targets::Migration),
            Box::new(m20260430_000024_cluster_directive_linucb::Migration),
            Box::new(m20260430_000025_cluster_compute_linucb::Migration),
            Box::new(m20260430_000028_theorems_trust_state::Migration),
            Box::new(m20260430_000029_drop_email_outbox::Migration),
            Box::new(m20260430_000030_user_sponsorships::Migration),
            Box::new(m20260501_000020_query_optimization_indexes::Migration),
        ]
    }
}
