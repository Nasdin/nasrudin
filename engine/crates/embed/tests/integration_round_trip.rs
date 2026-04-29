//! Build → save → checksum → reopen → nearest. No model download
//! (synthetic 384-dim vectors), so this can run in CI.

use nasrudin_core::TheoremId;
use nasrudin_embed::{compute_index_checksum, EmbeddingIndex, IndexBuilder, EMBED_DIM};
use tempfile::tempdir;

fn id(n: u8) -> TheoremId {
    [n, 0, 0, 0, 0, 0, 0, 0]
}

fn unit_vec(seed: u8) -> Vec<f32> {
    let mut v = vec![0.0f32; EMBED_DIM as usize];
    v[0] = 1.0 - 0.01 * (seed as f32);
    v[1] = 0.01 * (seed as f32);
    let n: f32 = v.iter().map(|x| x * x).sum::<f32>().sqrt();
    for x in &mut v {
        *x /= n;
    }
    v
}

#[test]
fn round_trip_via_builder_and_open() {
    let dir = tempdir().unwrap();
    let p = dir.path().join("corpus.embed");
    let rows: Vec<(TheoremId, Vec<f32>)> = (0u8..5).map(|i| (id(i), unit_vec(i))).collect();
    let mut b = IndexBuilder::new();
    b.rows = rows.clone();
    b.save(&p).unwrap();

    // Checksum is stable across reads.
    let cs1 = compute_index_checksum(&p).unwrap();
    let cs2 = compute_index_checksum(&p).unwrap();
    assert_eq!(cs1, cs2);

    let idx = EmbeddingIndex::open(&p).unwrap();
    assert_eq!(idx.len(), 5);

    // Querying with the seed=0 vector returns id=0 first.
    let hits = idx.nearest(&unit_vec(0), 5);
    assert!(!hits.is_empty());
    assert_eq!(hits[0].theorem_id, id(0));
}

#[test]
fn open_rejects_truncated_file() {
    let dir = tempdir().unwrap();
    let p = dir.path().join("corpus.embed");
    std::fs::write(&p, vec![0u8; 16]).unwrap();
    assert!(EmbeddingIndex::open(&p).is_err());
}

#[test]
fn nearest_zero_k_returns_empty() {
    let dir = tempdir().unwrap();
    let p = dir.path().join("corpus.embed");
    let rows: Vec<(TheoremId, Vec<f32>)> = vec![(id(1), unit_vec(0))];
    let mut b = IndexBuilder::new();
    b.rows = rows;
    b.save(&p).unwrap();
    let idx = EmbeddingIndex::open(&p).unwrap();
    assert!(idx.nearest(&unit_vec(0), 0).is_empty());
}
