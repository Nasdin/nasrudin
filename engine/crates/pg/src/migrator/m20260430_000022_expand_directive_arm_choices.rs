//! Allow `multiplier_choice` ∈ [0, 8] on the directive bandit so the
//! online-expansion mechanism can materialise arms past the initial
//! 5-choice range when a slot's outer choice dominates. The original
//! check constraint capped at 4; the new constraint allows 8 — the
//! bandit module materialises 5..=8 lazily via `expand_dominant_arms`.
//!
//! Same applies to `cluster_compute_arms` — its outer choice (3.0×)
//! can dominate and we want room to expand. (Boost / exploit are
//! already at the GA's hard cap on mutation_rate / elitism, so
//! expansion there mostly probes the GA's saturation envelope; for
//! diversify / kill / compute, expansion is genuinely useful.)

use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();
        // Drop and recreate the multiplier_choice range checks. Names
        // are PostgreSQL-default (`<table>_check<N>`); the
        // multiplier_choice check is the third one (after action and
        // strength_bucket) on cluster_directive_arms, and the second
        // on cluster_compute_arms. Use IF EXISTS so this migration
        // is idempotent across environments where the auto-name
        // differs.
        for sql in [
            "ALTER TABLE cluster_directive_arms \
             DROP CONSTRAINT IF EXISTS cluster_directive_arms_check2",
            "ALTER TABLE cluster_directive_arms \
             ADD CONSTRAINT cluster_directive_arms_choice_range_v2 \
             CHECK (multiplier_choice BETWEEN 0 AND 8)",
            "ALTER TABLE cluster_compute_arms \
             DROP CONSTRAINT IF EXISTS cluster_compute_arms_check1",
            "ALTER TABLE cluster_compute_arms \
             ADD CONSTRAINT cluster_compute_arms_choice_range_v2 \
             CHECK (multiplier_choice BETWEEN 0 AND 8)",
        ] {
            conn.execute_unprepared(sql).await?;
        }
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        let conn = manager.get_connection();
        for sql in [
            "ALTER TABLE cluster_directive_arms \
             DROP CONSTRAINT IF EXISTS cluster_directive_arms_choice_range_v2",
            "ALTER TABLE cluster_compute_arms \
             DROP CONSTRAINT IF EXISTS cluster_compute_arms_choice_range_v2",
        ] {
            let _ = conn.execute_unprepared(sql).await;
        }
        Ok(())
    }
}
