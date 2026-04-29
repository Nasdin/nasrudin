// stub — implemented in Task 4
use anyhow::Result;

pub struct Embedder;

impl Embedder {
    pub fn new() -> Result<Self> {
        anyhow::bail!("Embedder::new not yet implemented")
    }
    pub fn embed_one(&self, _text: &str) -> Result<Vec<f32>> {
        anyhow::bail!("Embedder::embed_one not yet implemented")
    }
    pub fn embed_batch(&self, _texts: Vec<String>) -> Result<Vec<Vec<f32>>> {
        anyhow::bail!("Embedder::embed_batch not yet implemented")
    }
}
