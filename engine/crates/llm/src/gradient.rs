//! DigitalOcean Gradient inference provider (OpenAI-compatible REST).
//!
//! The Gradient platform exposes an OpenAI-shape Chat Completions
//! endpoint at `https://inference.do-ai.run/v1/chat/completions`. This
//! module is functionally a thin sibling of `openai.rs`, with three
//! deliberate differences that make it a *separate* provider rather
//! than a base-URL override:
//!
//!  1. **Server-owned API key.** The key lives in the daemon's env
//!     (`GRADIENT_API_KEY`), not in the per-user `user_llm_keys` table.
//!     The cluster steerer uses it for an internal control-loop call
//!     and there is no per-user attribution.
//!  2. **Default model is Kimi K2.5** (`kimi-k2.5`), not GPT. K2.5 is
//!     a reasoning model that emits a `reasoning_content` chain of
//!     thought before producing the actual `content`, so callers must
//!     give it a generous `max_tokens` budget (≥4096) when asking for
//!     structured JSON. `supported_models()` reflects the catalog
//!     Gradient currently advertises; `list_models()` queries the live
//!     catalog so the steerer's boot-time check stays accurate.
//!  3. **Lives in its own provider** so the BYO LLM Registry never
//!     accidentally dispatches a user request to the server's key.

use async_trait::async_trait;
use futures::stream::BoxStream;
use serde::{Deserialize, Serialize};

use crate::provider::{
    CompletionRequest, CompletionResponse, LlmError, LlmProvider, ResponseFormat, TokenChunk,
};

const DEFAULT_BASE_URL: &str = "https://inference.do-ai.run";
// Names mirror DigitalOcean Gradient's serverless catalog. The list is
// advisory — `list_models()` queries the live catalog at boot and the
// daemon doesn't hard-reject anything not listed here, so adding a
// model here is purely about giving operators a sane default.
//
// Kimi K2.5 is a reasoning model: it spends tokens on
// `reasoning_content` before producing the actual `content` field, so
// callers should give it a generous `max_tokens` budget (≥4096) when
// asking for structured JSON output.
const SUPPORTED: &[&str] = &[
    "kimi-k2.5",
    "llama3.3-70b-instruct",
    "anthropic-claude-4.6-sonnet",
    "anthropic-claude-haiku-4.5",
    "deepseek-r1-distill-llama-70b",
];

pub struct GradientProvider {
    client: reqwest::Client,
    api_key: String,
    base_url: String,
}

impl GradientProvider {
    pub fn new(api_key: String) -> Self {
        Self {
            client: reqwest::Client::builder()
                .timeout(std::time::Duration::from_secs(60))
                .build()
                .expect("reqwest client"),
            api_key,
            base_url: DEFAULT_BASE_URL.into(),
        }
    }

    /// Construct from the server-owned env key. Returns `Err` when
    /// `GRADIENT_API_KEY` is unset — used by the steerer boot path so
    /// the daemon panics with a clear message rather than starting and
    /// silently failing every cycle.
    pub fn from_env() -> Result<Self, LlmError> {
        let key = std::env::var("GRADIENT_API_KEY").map_err(|_| {
            LlmError::Unauthorized(
                "GRADIENT_API_KEY environment variable is required to boot the cluster steerer; \
                 set it or set STEERER_DISABLED=1"
                    .into(),
            )
        })?;
        let base = std::env::var("GRADIENT_BASE_URL").unwrap_or_else(|_| DEFAULT_BASE_URL.into());
        Ok(Self::new(key).with_base_url(base))
    }

    pub fn with_base_url(mut self, url: impl Into<String>) -> Self {
        self.base_url = url.into();
        self
    }

    /// Query Gradient's `/v1/models` catalog. The steerer calls this at
    /// boot to fail fast if the configured `STEERER_MODEL` isn't
    /// available, rather than discovering the mistake on the first
    /// cycle 10 minutes in.
    pub async fn list_models(&self) -> Result<Vec<String>, LlmError> {
        #[derive(Deserialize)]
        struct M {
            id: String,
        }
        #[derive(Deserialize)]
        struct R {
            data: Vec<M>,
        }
        let url = format!("{}/v1/models", self.base_url);
        let resp = self
            .client
            .get(&url)
            .bearer_auth(&self.api_key)
            .send()
            .await?;
        let status = resp.status();
        if !status.is_success() {
            let body = resp.text().await.unwrap_or_default();
            return Err(LlmError::Http {
                status: status.as_u16(),
                body,
            });
        }
        let r: R = resp.json().await.map_err(|e| LlmError::Parse(e.to_string()))?;
        Ok(r.data.into_iter().map(|m| m.id).collect())
    }
}

#[derive(Serialize)]
struct ChatRequest<'a> {
    model: &'a str,
    messages: Vec<ChatMessage<'a>>,
    max_tokens: u32,
    temperature: f32,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    stop: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    response_format: Option<serde_json::Value>,
}

#[derive(Serialize)]
struct ChatMessage<'a> {
    role: &'a str,
    content: &'a str,
}

#[derive(Deserialize)]
struct ChatResponse {
    #[serde(default)]
    model: String,
    choices: Vec<Choice>,
    #[serde(default)]
    usage: Option<Usage>,
}

#[derive(Deserialize)]
struct Choice {
    message: ChoiceMessage,
    #[serde(default)]
    finish_reason: Option<String>,
}

#[derive(Deserialize)]
struct ChoiceMessage {
    #[serde(default)]
    content: String,
}

#[derive(Deserialize)]
struct Usage {
    #[serde(default)]
    prompt_tokens: u32,
    #[serde(default)]
    completion_tokens: u32,
}

#[async_trait]
impl LlmProvider for GradientProvider {
    fn name(&self) -> &'static str {
        "gradient"
    }

    fn supported_models(&self) -> &[&'static str] {
        SUPPORTED
    }

    async fn complete(&self, req: CompletionRequest) -> Result<CompletionResponse, LlmError> {
        // Unlike openai.rs we do NOT hard-reject unsupported models —
        // Gradient's catalog drifts and the steerer verifies via
        // `list_models()` at boot. If the user passed a typo it will
        // surface as a 400 from the API, which is good enough.
        let response_format = match &req.response_format {
            ResponseFormat::Free => None,
            ResponseFormat::Json { .. } => Some(serde_json::json!({"type": "json_object"})),
            ResponseFormat::JsonSchema { name, schema } => {
                // OpenAI-compatible strict structured outputs. Kimi K2.5
                // and gpt-4o-class models support this; older / smaller
                // models may 400 with "unknown response_format" — caller
                // is responsible for falling back to plain `Json` mode.
                Some(serde_json::json!({
                    "type": "json_schema",
                    "json_schema": {
                        "name": name,
                        "strict": true,
                        "schema": schema,
                    }
                }))
            }
        };
        let body = ChatRequest {
            model: &req.model,
            messages: vec![
                ChatMessage {
                    role: "system",
                    content: &req.system_prompt,
                },
                ChatMessage {
                    role: "user",
                    content: &req.user_prompt,
                },
            ],
            max_tokens: req.max_tokens,
            temperature: req.temperature,
            stop: req.stop_sequences.clone(),
            response_format,
        };
        let url = format!("{}/v1/chat/completions", self.base_url);
        let resp = self
            .client
            .post(&url)
            .bearer_auth(&self.api_key)
            .header("content-type", "application/json")
            .json(&body)
            .send()
            .await?;
        let status = resp.status();
        if !status.is_success() {
            let text = resp.text().await.unwrap_or_default();
            return Err(match status.as_u16() {
                401 | 403 => LlmError::Unauthorized(text),
                429 => LlmError::RateLimited {
                    retry_after_ms: 1000,
                },
                _ => LlmError::Http {
                    status: status.as_u16(),
                    body: text,
                },
            });
        }
        let parsed: ChatResponse = resp
            .json()
            .await
            .map_err(|e| LlmError::Parse(e.to_string()))?;
        let choice = parsed
            .choices
            .into_iter()
            .next()
            .ok_or_else(|| LlmError::Parse("no choices".into()))?;
        let usage = parsed.usage.unwrap_or(Usage {
            prompt_tokens: 0,
            completion_tokens: 0,
        });
        Ok(CompletionResponse {
            model: if parsed.model.is_empty() {
                req.model.clone()
            } else {
                parsed.model
            },
            text: choice.message.content,
            input_tokens: usage.prompt_tokens,
            output_tokens: usage.completion_tokens,
            stop_reason: choice.finish_reason.unwrap_or_else(|| "stop".into()),
        })
    }

    async fn stream<'a>(
        &'a self,
        _req: CompletionRequest,
    ) -> Result<BoxStream<'a, Result<TokenChunk, LlmError>>, LlmError> {
        Err(LlmError::Other(
            "stream not implemented for Gradient (steerer is one-shot)".into(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn provider_name_is_gradient() {
        let p = GradientProvider::new("test".into());
        assert_eq!(p.name(), "gradient");
    }

    #[test]
    fn supports_kimi_k2() {
        let p = GradientProvider::new("test".into());
        assert!(p.supported_models().contains(&"kimi-k2.5"));
    }

    #[test]
    fn from_env_errs_when_unset() {
        // Snapshot whatever value is present so we don't poison
        // a co-running test in the same process.
        let prior = std::env::var("GRADIENT_API_KEY").ok();
        // Safety: tests in this file run single-threaded by virtue of
        // the env mutation. `cargo test` defaults to multi-threaded but
        // these three tests don't race because each saves+restores.
        unsafe {
            std::env::remove_var("GRADIENT_API_KEY");
        }
        let r = GradientProvider::from_env();
        if let Some(v) = prior {
            unsafe {
                std::env::set_var("GRADIENT_API_KEY", v);
            }
        }
        assert!(matches!(r, Err(LlmError::Unauthorized(_))));
    }
}
