//! Build a fresh `corpus.embed` + `corpus.embed.hnsw` from an
//! iterator of `(TheoremId, source_text)` pairs.

use anyhow::{Context, Result};
use instant_distance::Builder as HnswBuilder;
use nasrudin_core::TheoremId;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::format::{IndexHeader, EMBED_DIM, INDEX_VERSION};
use crate::index::{sidecar_path, CosinePoint};
use crate::model::Embedder;

pub struct IndexBuilder {
    pub rows: Vec<(TheoremId, Vec<f32>)>,
}

impl IndexBuilder {
    pub fn new() -> Self {
        Self { rows: Vec::new() }
    }

    /// Embed `texts` in batches and accumulate `(id, vector)` pairs.
    /// `batch_size` is forwarded to fastembed (recommended: 32 to 128
    /// depending on RAM budget).
    pub fn add_batch(
        &mut self,
        embedder: &Embedder,
        texts: Vec<(TheoremId, String)>,
        batch_size: usize,
    ) -> Result<()> {
        if texts.is_empty() {
            return Ok(());
        }
        for chunk in texts.chunks(batch_size.max(1)) {
            let ids: Vec<TheoremId> = chunk.iter().map(|(id, _)| *id).collect();
            let raw_texts: Vec<String> = chunk.iter().map(|(_, t)| t.clone()).collect();
            let vectors = embedder
                .embed_batch(raw_texts)
                .context("embed batch in builder")?;
            for (id, v) in ids.into_iter().zip(vectors.into_iter()) {
                if v.len() != EMBED_DIM as usize {
                    anyhow::bail!("model returned dim {} != expected {EMBED_DIM}", v.len());
                }
                self.rows.push((id, v));
            }
        }
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Persist `corpus.embed` + `corpus.embed.hnsw`. Existing files at
    /// these paths are overwritten atomically (write to .tmp then
    /// rename).
    pub fn save(&self, main_path: &Path) -> Result<()> {
        write_main(main_path, &self.rows)?;
        write_hnsw_sidecar(main_path, &self.rows)?;
        Ok(())
    }
}

impl Default for IndexBuilder {
    fn default() -> Self {
        Self::new()
    }
}

fn write_main(path: &Path, rows: &[(TheoremId, Vec<f32>)]) -> Result<()> {
    let tmp = with_tmp_suffix(path);
    {
        let f = File::create(&tmp).with_context(|| format!("create {tmp:?}"))?;
        let mut w = BufWriter::new(f);
        let header = IndexHeader {
            version: INDEX_VERSION,
            dim: EMBED_DIM,
            count: u32::try_from(rows.len()).context("count exceeds u32")?,
            built_at_millis: chrono::Utc::now().timestamp_millis(),
        };
        w.write_all(&header.encode())?;
        for (id, v) in rows {
            w.write_all(id)?;
            for f in v {
                w.write_all(&f.to_le_bytes())?;
            }
        }
        w.flush()?;
    }
    std::fs::rename(&tmp, path).context("rename tmp into place")?;
    Ok(())
}

fn write_hnsw_sidecar(main_path: &Path, rows: &[(TheoremId, Vec<f32>)]) -> Result<()> {
    let sidecar = sidecar_path(main_path);
    let tmp = with_tmp_suffix(&sidecar);
    let points: Vec<CosinePoint> = rows.iter().map(|(_, v)| CosinePoint(v.clone())).collect();
    let values: Vec<TheoremId> = rows.iter().map(|(id, _)| *id).collect();
    let hnsw = HnswBuilder::default().build(points, values);
    let bytes = postcard::to_allocvec(&hnsw).context("serialise HNSW")?;
    std::fs::write(&tmp, &bytes).with_context(|| format!("write {tmp:?}"))?;
    std::fs::rename(&tmp, &sidecar).context("rename hnsw tmp into place")?;
    Ok(())
}

fn with_tmp_suffix(p: &Path) -> std::path::PathBuf {
    let mut s = p.as_os_str().to_owned();
    s.push(".tmp");
    std::path::PathBuf::from(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    fn synthetic_vec(seed: u8) -> Vec<f32> {
        let mut v = vec![0.0f32; EMBED_DIM as usize];
        v[0] = (seed as f32) + 1.0;
        v[1] = ((seed as f32) + 1.0) * 0.5;
        let n: f32 = v.iter().map(|x| x * x).sum::<f32>().sqrt();
        for x in &mut v {
            *x /= n;
        }
        v
    }

    #[test]
    fn save_and_reopen_round_trips_record_count() {
        let dir = tempdir().unwrap();
        let p = dir.path().join("corpus.embed");
        let rows: Vec<(TheoremId, Vec<f32>)> = (0u8..3)
            .map(|i| ([i, 0, 0, 0, 0, 0, 0, 0], synthetic_vec(i)))
            .collect();
        let mut b = IndexBuilder::new();
        b.rows = rows.clone();
        b.save(&p).unwrap();
        let idx = crate::index::EmbeddingIndex::open(&p).unwrap();
        assert_eq!(idx.len(), 3);
    }

    #[test]
    fn save_creates_both_main_and_sidecar() {
        let dir = tempdir().unwrap();
        let p = dir.path().join("corpus.embed");
        let rows: Vec<(TheoremId, Vec<f32>)> =
            vec![([1, 0, 0, 0, 0, 0, 0, 0], synthetic_vec(0))];
        let mut b = IndexBuilder::new();
        b.rows = rows;
        b.save(&p).unwrap();
        assert!(p.exists());
        assert!(crate::index::sidecar_path(&p).exists());
    }
}
