//! Text → 384-dim wrapper around `fastembed`.

use std::sync::Mutex;

use anyhow::{Context, Result};
use fastembed::{EmbeddingModel, InitOptions, TextEmbedding};

/// Wraps a fastembed `TextEmbedding`. One instance per process is
/// usually sufficient — model load is ~150 MB resident, ~1 second cold.
///
/// fastembed v5 changed `embed()` to require `&mut self` (the inner ONNX
/// session caches batch buffers). We hold the model behind a `Mutex` so the
/// public API stays `&self` and the type can still be wrapped in `Arc` and
/// shared across handlers. Embed calls are CPU-bound and serialise on the
/// mutex; callers that care about latency should run them on a
/// `tokio::task::spawn_blocking` thread.
pub struct Embedder {
    inner: Mutex<TextEmbedding>,
}

impl Embedder {
    /// Construct using the default model (BGE small en v1.5, 384 dims).
    pub fn new() -> Result<Self> {
        let inner = TextEmbedding::try_new(
            InitOptions::new(EmbeddingModel::BGESmallENV15).with_show_download_progress(false),
        )
        .context("init fastembed BGE small")?;
        Ok(Self {
            inner: Mutex::new(inner),
        })
    }

    /// Embed a single text. Returns a 384-dim vector.
    pub fn embed_one(&self, text: &str) -> Result<Vec<f32>> {
        let mut g = self
            .inner
            .lock()
            .map_err(|_| anyhow::anyhow!("embedder mutex poisoned"))?;
        let mut v = g
            .embed(vec![text.to_string()], None)
            .context("fastembed embed_one")?;
        v.pop().context("fastembed returned empty embed batch")
    }

    /// Embed a batch. Faster than calling `embed_one` per element.
    pub fn embed_batch(&self, texts: Vec<String>) -> Result<Vec<Vec<f32>>> {
        let mut g = self
            .inner
            .lock()
            .map_err(|_| anyhow::anyhow!("embedder mutex poisoned"))?;
        g.embed(texts, None).context("fastembed embed_batch")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Heavy: downloads the model on first run (~130 MB). CI should
    /// either pre-warm `~/.cache/fastembed/` or set
    /// `NASRUDIN_SKIP_EMBED_DOWNLOAD=1` to skip.
    #[test]
    #[ignore]
    fn embed_one_returns_384_dims() {
        if std::env::var("NASRUDIN_SKIP_EMBED_DOWNLOAD").is_ok() {
            return;
        }
        let e = Embedder::new().expect("model init");
        let v = e.embed_one("E equals m c squared").unwrap();
        assert_eq!(v.len(), 384);
    }

    #[test]
    #[ignore]
    fn deterministic_across_calls() {
        if std::env::var("NASRUDIN_SKIP_EMBED_DOWNLOAD").is_ok() {
            return;
        }
        let e = Embedder::new().expect("model init");
        let a = e.embed_one("kinetic energy").unwrap();
        let b = e.embed_one("kinetic energy").unwrap();
        for (x, y) in a.iter().zip(b.iter()) {
            assert!((x - y).abs() < 1e-5, "embeddings should be ~deterministic");
        }
    }
}
