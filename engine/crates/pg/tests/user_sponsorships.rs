//! Integration tests for the user_sponsorships query layer.
//! Skipped if DATABASE_URL is not set.

use chrono::{Duration, Utc};
use nasrudin_pg::{PgConfig, connect_and_migrate, query};
use uuid::Uuid;

async fn db() -> Option<sea_orm::DatabaseConnection> {
    let url = std::env::var("DATABASE_URL").ok()?;
    Some(connect_and_migrate(&PgConfig::new(&url)).await.unwrap())
}

async fn make_user(db: &sea_orm::DatabaseConnection) -> uuid::Uuid {
    let unique = Uuid::new_v4();
    query::users::create_firebase_user(
        db,
        &format!("fb_spon_{}", unique.simple()),
        &format!("spon-{unique}@example.test"),
        None,
    )
    .await
    .unwrap()
    .id
}

#[tokio::test]
async fn upsert_subscription_idempotent() {
    let Some(db) = db().await else { return };
    let user_id = make_user(&db).await;
    let sub_id = format!("sub_test_{}", Uuid::new_v4().simple());
    let started = Utc::now() - Duration::days(7);

    // First upsert.
    query::user_sponsorships::upsert_subscription(
        &db,
        user_id,
        &sub_id,
        Some("sponsor_25"),
        Some(2500),
        "active",
        started,
        Some("evt_initial"),
    )
    .await
    .unwrap();

    // Second upsert with new amount + status — must update in place,
    // NOT create a duplicate row.
    query::user_sponsorships::upsert_subscription(
        &db,
        user_id,
        &sub_id,
        Some("sponsor_100"),
        Some(10000),
        "active",
        started,
        Some("evt_followup"),
    )
    .await
    .unwrap();

    let rows = query::user_sponsorships::list_for_user(&db, user_id)
        .await
        .unwrap();
    let mine: Vec<_> = rows
        .into_iter()
        .filter(|r| r.stripe_subscription_id.as_deref() == Some(sub_id.as_str()))
        .collect();
    assert_eq!(mine.len(), 1, "upsert must not duplicate");
    assert_eq!(mine[0].tier.as_deref(), Some("sponsor_100"));
    assert_eq!(mine[0].amount_cents, Some(10000));

    let _ = query::users::delete_user(&db, user_id).await;
}

#[tokio::test]
async fn upsert_one_time_idempotent_on_charge_id() {
    let Some(db) = db().await else { return };
    let user_id = make_user(&db).await;
    let charge_id = format!("ch_test_{}", Uuid::new_v4().simple());
    let started = Utc::now();

    query::user_sponsorships::upsert_one_time(
        &db,
        user_id,
        &charge_id,
        Some("sponsor_open"),
        4200,
        started,
        Some("evt_one_time_a"),
    )
    .await
    .unwrap();

    // Replay same charge_id — must be a no-op.
    query::user_sponsorships::upsert_one_time(
        &db,
        user_id,
        &charge_id,
        Some("sponsor_open"),
        9999,
        started,
        Some("evt_one_time_b"),
    )
    .await
    .unwrap();

    let rows = query::user_sponsorships::list_for_user(&db, user_id)
        .await
        .unwrap();
    let mine: Vec<_> = rows
        .into_iter()
        .filter(|r| r.stripe_charge_id.as_deref() == Some(charge_id.as_str()))
        .collect();
    assert_eq!(mine.len(), 1);
    // First-write-wins on conflict do nothing.
    assert_eq!(mine[0].amount_cents, Some(4200));

    let _ = query::users::delete_user(&db, user_id).await;
}

#[tokio::test]
async fn webhook_idempotency_via_event_id() {
    let Some(db) = db().await else { return };
    let user_id = make_user(&db).await;
    let charge_id = format!("ch_evt_{}", Uuid::new_v4().simple());
    let evt_id = format!("evt_{}", Uuid::new_v4().simple());

    // First processing — should mark the event as seen.
    assert!(
        !query::user_sponsorships::event_already_processed(&db, &evt_id)
            .await
            .unwrap()
    );
    query::user_sponsorships::upsert_one_time(
        &db,
        user_id,
        &charge_id,
        Some("sponsor_open"),
        500,
        Utc::now(),
        Some(&evt_id),
    )
    .await
    .unwrap();

    // Second time the same event lands, the helper sees it.
    assert!(
        query::user_sponsorships::event_already_processed(&db, &evt_id)
            .await
            .unwrap()
    );

    // Even attempting a fresh charge with the same event_id keeps a
    // single row — the partial unique index on stripe_event_id
    // refuses the duplicate. (We use a different charge id so the
    // primary uniqueness path doesn't kick in first.)
    let other_charge = format!("ch_evt_other_{}", Uuid::new_v4().simple());
    let dup = query::user_sponsorships::upsert_one_time(
        &db,
        user_id,
        &other_charge,
        Some("sponsor_open"),
        700,
        Utc::now(),
        Some(&evt_id),
    )
    .await;
    assert!(dup.is_err(), "duplicate event_id must be rejected");

    let _ = query::users::delete_user(&db, user_id).await;
}

#[tokio::test]
async fn mark_canceled_sets_status_and_timestamp() {
    let Some(db) = db().await else { return };
    let user_id = make_user(&db).await;
    let sub_id = format!("sub_cancel_{}", Uuid::new_v4().simple());
    let started = Utc::now() - Duration::days(30);

    query::user_sponsorships::upsert_subscription(
        &db,
        user_id,
        &sub_id,
        Some("sponsor_5"),
        Some(500),
        "active",
        started,
        Some("evt_active"),
    )
    .await
    .unwrap();

    let canceled_at = Utc::now();
    query::user_sponsorships::mark_canceled(&db, &sub_id, canceled_at)
        .await
        .unwrap();

    let rows = query::user_sponsorships::list_for_user(&db, user_id)
        .await
        .unwrap();
    let mine = rows
        .into_iter()
        .find(|r| r.stripe_subscription_id.as_deref() == Some(sub_id.as_str()))
        .unwrap();
    assert_eq!(mine.status, "canceled");
    assert!(mine.canceled_at.is_some());

    let _ = query::users::delete_user(&db, user_id).await;
}

#[tokio::test]
async fn summary_reports_active_subscription_and_donations() {
    let Some(db) = db().await else { return };
    let user_id = make_user(&db).await;

    // One active subscription.
    let sub_id = format!("sub_sum_{}", Uuid::new_v4().simple());
    query::user_sponsorships::upsert_subscription(
        &db,
        user_id,
        &sub_id,
        Some("sponsor_25"),
        Some(2500),
        "active",
        Utc::now() - Duration::days(60),
        Some("evt_sum_sub"),
    )
    .await
    .unwrap();

    // Two one-time donations.
    let ch_a = format!("ch_sum_a_{}", Uuid::new_v4().simple());
    let ch_b = format!("ch_sum_b_{}", Uuid::new_v4().simple());
    query::user_sponsorships::upsert_one_time(
        &db,
        user_id,
        &ch_a,
        Some("sponsor_open"),
        1500,
        Utc::now() - Duration::days(45),
        Some("evt_sum_a"),
    )
    .await
    .unwrap();
    query::user_sponsorships::upsert_one_time(
        &db,
        user_id,
        &ch_b,
        Some("sponsor_open"),
        2000,
        Utc::now() - Duration::days(2),
        Some("evt_sum_b"),
    )
    .await
    .unwrap();

    let summary = query::user_sponsorships::summary_for_user(&db, user_id)
        .await
        .unwrap();
    let active = summary
        .active_subscription
        .as_ref()
        .expect("active subscription present");
    assert_eq!(active.tier.as_deref(), Some("sponsor_25"));
    assert_eq!(active.amount_cents, Some(2500));
    assert_eq!(summary.donation_count, 2);
    // Subscription contributes its per-interval price (2500) + 2 donations (1500 + 2000) = 6000
    assert_eq!(summary.lifetime_total_cents, 6000);
    assert!(summary.first_supported_at.is_some());
    assert!(summary.latest_supported_at.is_some());
    assert!(summary.first_supported_at <= summary.latest_supported_at);

    let _ = query::users::delete_user(&db, user_id).await;
}

#[tokio::test]
async fn summary_zeros_for_user_without_history() {
    let Some(db) = db().await else { return };
    let user_id = make_user(&db).await;

    let summary = query::user_sponsorships::summary_for_user(&db, user_id)
        .await
        .unwrap();
    assert!(summary.active_subscription.is_none());
    assert_eq!(summary.lifetime_total_cents, 0);
    assert_eq!(summary.donation_count, 0);
    assert!(summary.first_supported_at.is_none());

    let _ = query::users::delete_user(&db, user_id).await;
}
