//! Read/upsert helpers for the compute-bandit LinUCB sufficient-
//! statistics table. Same shape as cluster_directive_linucb but
//! keyed only on island_domain.

use crate::entity::cluster_compute_linucb::*;
use chrono::Utc;
use sea_orm::*;

pub const FEATURE_DIM: usize = 6;

pub async fn ensure_row(
    db: &DatabaseConnection,
    island_domain: &str,
    lambda: f64,
) -> Result<(), DbErr> {
    let exists = Entity::find_by_id(island_domain.to_string()).one(db).await?;
    if exists.is_some() {
        return Ok(());
    }
    let mut a = vec![0.0; FEATURE_DIM * FEATURE_DIM];
    for i in 0..FEATURE_DIM {
        a[i * FEATURE_DIM + i] = lambda;
    }
    let am = ActiveModel {
        island_domain: Set(island_domain.into()),
        a_matrix: Set(a),
        b_vector: Set(vec![0.0; FEATURE_DIM]),
        pulls: Set(0),
        updated_at: Set(Utc::now().fixed_offset()),
    };
    Entity::insert(am).exec(db).await?;
    Ok(())
}

pub async fn get(
    db: &DatabaseConnection,
    island_domain: &str,
) -> Result<Option<Model>, DbErr> {
    Entity::find_by_id(island_domain.to_string()).one(db).await
}

pub async fn snapshot_all(db: &DatabaseConnection) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .order_by_asc(Column::IslandDomain)
        .all(db)
        .await
}

pub async fn save_update(
    db: &DatabaseConnection,
    island_domain: &str,
    a_matrix: Vec<f64>,
    b_vector: Vec<f64>,
    new_pulls: i64,
) -> Result<(), DbErr> {
    let arm = Entity::find_by_id(island_domain.to_string()).one(db).await?;
    let mut am: ActiveModel = match arm {
        Some(m) => m.into(),
        None => ActiveModel {
            island_domain: Set(island_domain.into()),
            a_matrix: Set(a_matrix.clone()),
            b_vector: Set(b_vector.clone()),
            pulls: Set(0),
            updated_at: Set(Utc::now().fixed_offset()),
        },
    };
    am.a_matrix = Set(a_matrix);
    am.b_vector = Set(b_vector);
    am.pulls = Set(new_pulls);
    am.updated_at = Set(Utc::now().fixed_offset());
    am.save(db).await?;
    Ok(())
}
