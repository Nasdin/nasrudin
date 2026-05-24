//! Public surface of the LLM router.

use async_trait::async_trait;
use futures::stream::BoxStream;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionRequest {
    pub model: String,
    pub system_prompt: String,
    pub user_prompt: String,
    pub max_tokens: u32,
    pub temperature: f32,
    #[serde(default)]
    pub stop_sequences: Vec<String>,
    #[serde(default)]
    pub response_format: ResponseFormat,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ResponseFormat {
    #[default]
    Free,
    /// Plain JSON-object output. The model is constrained to emit
    /// syntactically valid JSON, but no schema enforcement — any
    /// shape goes. Maps to OpenAI / Gradient
    /// `response_format: {"type": "json_object"}`. The `schema` field
    /// is currently unused; kept for backwards compat with callers
    /// that pass an empty `{}`. Use `JsonSchema` for strict mode.
    Json {
        schema: serde_json::Value,
    },
    /// Strict JSON Schema mode: the model is constrained to emit
    /// JSON matching `schema` exactly. OpenAI and Gradient/Kimi K2.6
    /// support this via
    /// `response_format: {"type": "json_schema", "json_schema":
    ///   {"name": ..., "strict": true, "schema": ...}}`.
    /// Token-level constrained decoding makes missing required
    /// fields, wrong types, and out-of-enum values impossible —
    /// validation failures shrink to zero for shape errors. Provider
    /// behaviour: OpenAI gpt-4o + Kimi K2.6 enforce; older models
    /// may 400 on unknown response_format and the caller should fall
    /// back to `Json { schema: {} }` with post-hoc validation.
    JsonSchema {
        /// Human-readable schema name (OpenAI requires this).
        name: String,
        /// Full JSON Schema document. Typically derived via the
        /// `schemars` crate at the call site.
        schema: serde_json::Value,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionResponse {
    pub model: String,
    pub text: String,
    pub input_tokens: u32,
    pub output_tokens: u32,
    pub stop_reason: String,
}

/// One streamed chunk. `text` is the incremental delta.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenChunk {
    pub text: String,
    pub finish_reason: Option<String>,
}

#[derive(Debug, Error)]
pub enum LlmError {
    #[error("HTTP {status}: {body}")]
    Http { status: u16, body: String },
    #[error("rate-limited (retry after {retry_after_ms} ms)")]
    RateLimited { retry_after_ms: u64 },
    #[error("auth failed: {0}")]
    Unauthorized(String),
    #[error("model not supported by this provider: {0}")]
    UnsupportedModel(String),
    #[error("response parse failure: {0}")]
    Parse(String),
    #[error("transport: {0}")]
    Transport(#[from] reqwest::Error),
    #[error("other: {0}")]
    Other(String),
}

#[async_trait]
pub trait LlmProvider: Send + Sync {
    /// Stable identifier used in URLs and the `provider` column.
    fn name(&self) -> &'static str;
    /// Models this provider understands. Used for client-side validation.
    fn supported_models(&self) -> &[&'static str];
    /// Single-shot completion.
    async fn complete(&self, req: CompletionRequest) -> Result<CompletionResponse, LlmError>;
    /// Streaming completion.
    async fn stream<'a>(
        &'a self,
        req: CompletionRequest,
    ) -> Result<BoxStream<'a, Result<TokenChunk, LlmError>>, LlmError>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn response_format_default_is_free() {
        let f: ResponseFormat = Default::default();
        assert!(matches!(f, ResponseFormat::Free));
    }

    #[test]
    fn completion_request_round_trips_json() {
        let req = CompletionRequest {
            model: "claude-sonnet-4-6".into(),
            system_prompt: "you are helpful".into(),
            user_prompt: "hello".into(),
            max_tokens: 512,
            temperature: 0.0,
            stop_sequences: vec![],
            response_format: ResponseFormat::Free,
        };
        let json = serde_json::to_string(&req).unwrap();
        let back: CompletionRequest = serde_json::from_str(&json).unwrap();
        assert_eq!(back.model, req.model);
        assert_eq!(back.max_tokens, req.max_tokens);
    }
}
