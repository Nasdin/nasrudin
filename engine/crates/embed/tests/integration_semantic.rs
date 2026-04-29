//! End-to-end: build an index from 3 synthetic theorems with
//! different topics, embed an "energy" hunch, confirm the
//! energy-themed theorem is closer than the fluid-themed one.
//!
//! `#[ignore]` because the model download is ~130 MB. Run with
//! `cargo test -p nasrudin-embed --test integration_semantic -- --ignored`.

use nasrudin_core::TheoremId;
use nasrudin_embed::{EmbeddingIndex, Embedder, IndexBuilder};
use tempfile::tempdir;

fn id(n: u8) -> TheoremId {
    [n, 0, 0, 0, 0, 0, 0, 0]
}

#[test]
#[ignore]
fn energy_hunch_picks_energy_theorem_over_fluid() {
    if std::env::var("NASRUDIN_SKIP_EMBED_DOWNLOAD").is_ok() {
        return;
    }
    let embedder = Embedder::new().expect("model init");
    let texts = vec![
        (
            id(1),
            "rest energy equals mass times speed of light squared (E = m c^2)".to_string(),
        ),
        (
            id(2),
            "kinetic energy equals one half mass velocity squared".to_string(),
        ),
        (
            id(3),
            "Bernoulli's principle relates pressure and fluid velocity".to_string(),
        ),
    ];
    let mut b = IndexBuilder::new();
    b.add_batch(&embedder, texts, 8).unwrap();
    let dir = tempdir().unwrap();
    let p = dir.path().join("corpus.embed");
    b.save(&p).unwrap();

    let index = EmbeddingIndex::open(&p).unwrap();
    let hits = index
        .nearest_text(&embedder, "How does energy relate to mass?", 3)
        .unwrap();
    assert!(!hits.is_empty());
    assert!(
        hits[0].theorem_id == id(1) || hits[0].theorem_id == id(2),
        "expected energy theorem, got {:?}",
        hits[0].theorem_id
    );
    if let Some(fluid_pos) = hits.iter().position(|h| h.theorem_id == id(3)) {
        assert!(fluid_pos > 0, "fluid theorem should not rank first");
    }
}

#[test]
#[ignore]
fn deterministic_index_built_twice_returns_same_top_hit() {
    if std::env::var("NASRUDIN_SKIP_EMBED_DOWNLOAD").is_ok() {
        return;
    }
    let embedder = Embedder::new().expect("model init");
    let texts = vec![
        (id(1), "Lorentz transformations".to_string()),
        (id(2), "Maxwell equations in vacuum".to_string()),
    ];
    let dir = tempdir().unwrap();
    let p1 = dir.path().join("a.embed");
    let p2 = dir.path().join("b.embed");

    let mut b1 = IndexBuilder::new();
    b1.add_batch(&embedder, texts.clone(), 8).unwrap();
    b1.save(&p1).unwrap();
    let mut b2 = IndexBuilder::new();
    b2.add_batch(&embedder, texts, 8).unwrap();
    b2.save(&p2).unwrap();

    let i1 = EmbeddingIndex::open(&p1).unwrap();
    let i2 = EmbeddingIndex::open(&p2).unwrap();
    let q = embedder.embed_one("electromagnetic waves").unwrap();
    let h1 = i1.nearest(&q, 1);
    let h2 = i2.nearest(&q, 1);
    assert_eq!(h1[0].theorem_id, h2[0].theorem_id);
}
