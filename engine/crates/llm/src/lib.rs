//! BYO LLM router. Provides a `LlmProvider` trait with three
//! first-class implementations (Anthropic, OpenAI, Ollama) plus an
//! AES-256-GCM helper for encrypting bearer tokens at rest.
//!
//! Phase C of `docs/superpowers/specs/2026-04-28-llm-guided-search-design.md`.

pub mod anthropic;
pub mod encryption;
pub mod ollama;
pub mod openai;
pub mod provider;
pub mod registry;

pub use anthropic::AnthropicProvider;
pub use encryption::{decrypt, encrypt, key_hint, EncryptedKey};
pub use ollama::OllamaProvider;
pub use openai::OpenAiProvider;
pub use provider::{
    CompletionRequest, CompletionResponse, LlmError, LlmProvider, ResponseFormat, TokenChunk,
};
// Registry re-export lands in Task 6.
