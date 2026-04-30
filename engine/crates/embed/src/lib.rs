//! Local-CPU embedding store over the verified-theorem corpus.
//!
//! - [`model`] wraps fastembed for `text -> 384-dim vector`. (feature: `inference`)
//! - [`format`] defines the on-disk `corpus.embed` wire layout.
//! - [`index`] memory-maps a built corpus and exposes `nearest(...)`.
//! - [`builder`] writes a fresh index from a stream of theorems. (feature: `inference`)
//! - [`checksum`] computes a BLAKE3 hash of an index file body for
//!   distribution validation.

pub mod checksum;
pub mod format;
pub mod index;

#[cfg(feature = "inference")]
pub mod builder;
#[cfg(feature = "inference")]
pub mod model;

#[cfg(feature = "inference")]
pub use builder::IndexBuilder;
pub use checksum::{compute_index_checksum, IndexChecksum};
pub use format::{IndexHeader, EMBED_DIM, INDEX_MAGIC, INDEX_VERSION};
pub use index::{EmbeddingIndex, NearestHit};
#[cfg(feature = "inference")]
pub use model::Embedder;
