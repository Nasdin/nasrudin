//! Frozen audit action taxonomy + the `perform_audited` invariant helper.
//!
//! The audit log is only useful if every admin mutation writes a row.
//! We enforce this with a single helper, `perform_audited`, that:
//! 1. Validates the reason (≥ 10 chars).
//! 2. Opens a transaction (via `sea_orm::TransactionTrait::transaction`).
//! 3. Runs the mutation closure inside the txn.
//! 4. INSERTs the audit row inside the same txn.
//! 5. Commits.
//!
//! If the mutation closure errors, the entire txn rolls back — the
//! audit log entry is not committed. PRs that add admin endpoints
//! bypassing this helper should be rejected at code review.

use std::future::Future;
use std::net::IpAddr;
use std::pin::Pin;

use nasrudin_pg::sea_orm::{
    DatabaseConnection, DatabaseTransaction, DbErr, TransactionError, TransactionTrait,
};
use uuid::Uuid;

/// Frozen action codes. Add new codes by appending; never rename or
/// repurpose existing ones (downstream metrics + dashboards assume
/// stability).
pub mod actions {
    pub const SET_IS_ADMIN: &str = "SET_IS_ADMIN";
    pub const SET_IS_TRUSTED: &str = "SET_IS_TRUSTED";
    pub const SET_SPOT_CHECK_RATE: &str = "SET_SPOT_CHECK_RATE";
    pub const SET_KEY_TRUST: &str = "SET_KEY_TRUST";
    pub const SET_PLAN_TIER: &str = "SET_PLAN_TIER";
    pub const ADJUST_CREDITS: &str = "ADJUST_CREDITS";
    pub const REVOKE_API_KEY: &str = "REVOKE_API_KEY";
    pub const REFUND_INITIATED: &str = "REFUND_INITIATED";
    pub const REFUND_SUCCEEDED: &str = "REFUND_SUCCEEDED";
    pub const REFUND_FAILED: &str = "REFUND_FAILED";
    pub const IMPERSONATE_START: &str = "IMPERSONATE_START";
    pub const IMPERSONATE_END: &str = "IMPERSONATE_END";
    pub const IMPERSONATE_FORCE_END: &str = "IMPERSONATE_FORCE_END";
    pub const IMPERSONATED_ACTION: &str = "IMPERSONATED_ACTION";
    pub const CANCEL_JOB: &str = "CANCEL_JOB";
    pub const RELOAD_CORPUS: &str = "RELOAD_CORPUS";
    pub const FORCE_STEERING: &str = "FORCE_STEERING";
    pub const QUEUE_EMAIL: &str = "QUEUE_EMAIL";
    pub const RETRY_EMAIL: &str = "RETRY_EMAIL";
    pub const BULK_RUN_START: &str = "BULK_RUN_START";
    pub const BULK_RUN_COMPLETE: &str = "BULK_RUN_COMPLETE";
    pub const AUTO_REVOKE_WORKER: &str = "AUTO_REVOKE_WORKER";
}

/// Hardcoded UUID used as `actor_user_id` for system-driven audit rows
/// (refund reconciler, auto-revoke, impersonation expiry tick). The
/// `deploy/scripts/admin-bootstrap.sh` script INSERTs a `users` row
/// with this id and `email='system@nasrudin.org'` so the foreign-key
/// constraint is satisfied.
pub const SYSTEM_ACTOR_ID: Uuid = Uuid::from_u128(0x0000_0000_0000_0000_0000_0000_0000_0001);

/// Captured request metadata for audit rows. Optional fields are best-
/// effort and tolerate proxies that strip them.
#[derive(Clone, Debug, Default)]
pub struct RequestMeta {
    pub ip: Option<IpAddr>,
    pub user_agent: Option<String>,
}

/// Marker that the actor was acting *as* `target_user_id` via
/// impersonation. Carries the original admin id forward for the audit
/// row so the trail still ties back to the human.
#[derive(Clone, Debug)]
pub struct ImpersonationCtx {
    pub session_id: Uuid,
    pub original_admin_id: Uuid,
}

#[derive(Debug, thiserror::Error)]
pub enum AuditError {
    #[error("reason must be at least 10 characters")]
    ReasonTooShort,
    #[error("db: {0}")]
    Db(#[from] DbErr),
}

/// Run a mutation transactionally with an audit-log row.
///
/// `mutate` runs inside the same txn as the audit insert, returning
/// `(result, after_value_json)`. Both succeed-or-fail atomically.
///
/// The closure signature uses `Pin<Box<dyn Future + Send + 'c>>` to
/// match `sea_orm::TransactionTrait::transaction` and avoid the
/// well-known borrow-checker dance with `&'a DatabaseTransaction` in
/// the return type.
#[allow(clippy::too_many_arguments)]
pub async fn perform_audited<T, F>(
    pg: &DatabaseConnection,
    actor: &crate::auth::AuthUser,
    impersonation: Option<ImpersonationCtx>,
    req_meta: RequestMeta,
    target_user_id: Option<Uuid>,
    action: &'static str,
    reason: String,
    before_value: serde_json::Value,
    mutate: F,
) -> Result<T, AuditError>
where
    F: for<'c> FnOnce(
            &'c DatabaseTransaction,
        ) -> Pin<
            Box<dyn Future<Output = Result<(T, serde_json::Value), DbErr>> + Send + 'c>,
        > + Send
        + 'static,
    T: Send + 'static,
{
    if reason.trim().chars().count() < 10 {
        return Err(AuditError::ReasonTooShort);
    }

    let actor_id = actor.id;
    let impersonating = impersonation.as_ref().map(|i| i.original_admin_id);
    let ip = req_meta.ip;
    let ua = req_meta.user_agent.clone();

    let result: Result<T, TransactionError<DbErr>> = pg
        .transaction::<_, T, DbErr>(move |txn| {
            Box::pin(async move {
                let (out, after_value) = mutate(txn).await?;
                nasrudin_pg::query::admin_audit_log::insert(
                    txn,
                    actor_id,
                    target_user_id,
                    impersonating,
                    action,
                    Some(before_value),
                    Some(after_value),
                    reason,
                    ip,
                    ua,
                )
                .await?;
                Ok(out)
            })
        })
        .await;

    match result {
        Ok(out) => Ok(out),
        Err(TransactionError::Connection(e)) => Err(AuditError::Db(e)),
        Err(TransactionError::Transaction(e)) => Err(AuditError::Db(e)),
    }
}
