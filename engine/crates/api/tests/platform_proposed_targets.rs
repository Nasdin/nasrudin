//! Integration tests for `platform_targets::enqueue_proposed_targets`.
//!
//! Exercises the DB-touching path (sentinel-user upsert, dedup
//! against existing tier='platform' rows, ActiveModel insert) that
//! the pure-logic unit tests in `platform_targets::tests` can't
//! reach. Gracefully skips when TEST_DATABASE_URL is unset, matching
//! the pattern used by every other integration test in this crate.

mod test_app;

use sea_orm::{ColumnTrait, EntityTrait, PaginatorTrait, QueryFilter};

use nasrudin_pg::entity::conjecture_jobs;
use physics_api::platform_targets::enqueue_proposed_targets;
use physics_api::steerer::schema::ProposedTarget;

const TEST_MODEL: &str = "kimi-k2.6";

async fn count_platform_rows(
    pg: &sea_orm::DatabaseConnection,
    hunch: &str,
) -> u64 {
    conjecture_jobs::Entity::find()
        .filter(conjecture_jobs::Column::Tier.eq("platform"))
        .filter(conjecture_jobs::Column::Hunch.eq(hunch))
        .count(pg)
        .await
        .unwrap()
}

#[tokio::test]
async fn enqueue_accepts_two_well_formed_targets() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };
    let targets = vec![
        ProposedTarget {
            hunch: "P V = n R T".into(),
            domain_hint: "thermodynamics".into(),
            rationale: "ideal gas law not in queue".into(),
        },
        ProposedTarget {
            hunch: r"\Phi = L I".into(),
            domain_hint: "electromagnetism".into(),
            rationale: "magnetic flux through inductor".into(),
        },
    ];

    let (accepted, dropped) = enqueue_proposed_targets(&app.pg, &targets, TEST_MODEL).await;
    assert_eq!(accepted, 2);
    assert_eq!(dropped, 0);

    assert_eq!(count_platform_rows(&app.pg, "P V = n R T").await, 1);
    assert_eq!(count_platform_rows(&app.pg, r"\Phi = L I").await, 1);

    let row = conjecture_jobs::Entity::find()
        .filter(conjecture_jobs::Column::Tier.eq("platform"))
        .filter(conjecture_jobs::Column::Hunch.eq("P V = n R T"))
        .one(&app.pg)
        .await
        .unwrap()
        .expect("row should exist");
    assert_eq!(row.provider, "steerer-proposed");
    assert_eq!(row.model, TEST_MODEL);
    assert_eq!(row.slice_priority, 2);
    assert_eq!(row.state, "queued");
}

#[tokio::test]
async fn enqueue_dedupes_against_existing_platform_hunch() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };

    // Pre-seed the curated platform queue (E=mc² lives there at
    // priority=3). The steerer must NOT add a second row with the
    // same hunch.
    physics_api::platform_targets::ensure_platform_targets(&app.pg).await;
    let before = count_platform_rows(&app.pg, "E = m * c^2").await;
    assert_eq!(before, 1, "curated platform target should be seeded once");

    let targets = vec![ProposedTarget {
        hunch: "E = m * c^2".into(),
        domain_hint: "special_relativity".into(),
        rationale: "duplicate".into(),
    }];
    let (accepted, dropped) = enqueue_proposed_targets(&app.pg, &targets, TEST_MODEL).await;
    assert_eq!(accepted, 0);
    assert_eq!(dropped, 1);

    let after = count_platform_rows(&app.pg, "E = m * c^2").await;
    assert_eq!(after, 1, "no duplicate row should have been inserted");
}

#[tokio::test]
async fn enqueue_drops_malformed_and_keeps_well_formed() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };

    let targets = vec![
        ProposedTarget {
            hunch: "{ broken LaTeX [".into(),
            domain_hint: "pure_math".into(),
            rationale: "garbage hunch".into(),
        },
        ProposedTarget {
            hunch: "x = y + z".into(),
            domain_hint: "made_up_domain".into(),
            rationale: "unknown domain".into(),
        },
        ProposedTarget {
            hunch: "E = m c^2".into(),
            domain_hint: "special_relativity".into(),
            rationale: "forbidden headline".into(),
        },
        ProposedTarget {
            hunch: "P V = n R T".into(),
            domain_hint: "thermodynamics".into(),
            rationale: "the only valid one".into(),
        },
    ];

    let (accepted, dropped) = enqueue_proposed_targets(&app.pg, &targets, TEST_MODEL).await;
    assert_eq!(accepted, 1, "only the ideal-gas hunch should survive");
    assert_eq!(dropped, 3, "three bad entries should drop with warns");

    assert_eq!(count_platform_rows(&app.pg, "P V = n R T").await, 1);
    assert_eq!(count_platform_rows(&app.pg, "E = m c^2").await, 0);
    assert_eq!(count_platform_rows(&app.pg, "{ broken LaTeX [").await, 0);
}

#[tokio::test]
async fn enqueue_empty_slice_is_noop() {
    let Some(app) = test_app::build().await else {
        eprintln!("skipping: TEST_DATABASE_URL unavailable");
        return;
    };
    let (accepted, dropped) = enqueue_proposed_targets(&app.pg, &[], TEST_MODEL).await;
    assert_eq!(accepted, 0);
    assert_eq!(dropped, 0);
}
