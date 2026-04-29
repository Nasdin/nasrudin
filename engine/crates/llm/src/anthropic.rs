//! Anthropic Messages API.

use async_trait::async_trait;
use futures::stream::BoxStream;
use serde::{Deserialize, Serialize};

use crate::provider::{
    CompletionRequest, CompletionResponse, LlmError, LlmProvider, ResponseFormat, TokenChunk,
};

const SUPPORTED: &[&str] = &[
    "claude-sonnet-4-6",
    "claude-opus-4-7",
    "claude-haiku-4-5",
];

pub struct AnthropicProvider {
    client: reqwest::Client,
    api_key: String,
    base_url: String,
}

impl AnthropicProvider {
    pub fn new(api_key: String) -> Self {
        Self {
            client: reqwest::Client::builder()
                .timeout(std::time::Duration::from_secs(60))
                .build()
                .expect("reqwest client"),
            api_key,
            base_url: "https://api.anthropic.com".into(),
        }
    }

    /// For tests.
    pub fn with_base_url(mut self, url: impl Into<String>) -> Self {
        self.base_url = url.into();
        self
    }
}

#[derive(Serialize)]
struct MessagesRequest<'a> {
    model: &'a str,
    max_tokens: u32,
    temperature: f32,
    system: &'a str,
    messages: Vec<MessagesMessage<'a>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    stop_sequences: Vec<String>,
}

#[derive(Serialize)]
struct MessagesMessage<'a> {
    role: &'a str,
    content: &'a str,
}

#[derive(Deserialize)]
struct MessagesResponse {
    model: String,
    content: Vec<ContentBlock>,
    stop_reason: Option<String>,
    usage: Usage,
}

#[derive(Deserialize)]
struct ContentBlock {
    #[serde(default)]
    text: String,
}

#[derive(Deserialize)]
struct Usage {
    input_tokens: u32,
    output_tokens: u32,
}

#[async_trait]
impl LlmProvider for AnthropicProvider {
    fn name(&self) -> &'static str {
        "anthropic"
    }

    fn supported_models(&self) -> &[&'static str] {
        SUPPORTED
    }

    async fn complete(&self, req: CompletionRequest) -> Result<CompletionResponse, LlmError> {
        if !SUPPORTED.contains(&req.model.as_str()) {
            return Err(LlmError::UnsupportedModel(req.model));
        }
        let body = MessagesRequest {
            model: &req.model,
            max_tokens: req.max_tokens,
            temperature: req.temperature,
            system: &req.system_prompt,
            messages: vec![MessagesMessage {
                role: "user",
                content: &req.user_prompt,
            }],
            stop_sequences: match &req.response_format {
                ResponseFormat::Free => req.stop_sequences.clone(),
                ResponseFormat::Json { .. } => req.stop_sequences.clone(),
            },
        };
        let url = format!("{}/v1/messages", self.base_url);
        let resp = self
            .client
            .post(&url)
            .header("x-api-key", &self.api_key)
            .header("anthropic-version", "2023-06-01")
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
        let parsed: MessagesResponse = resp
            .json()
            .await
            .map_err(|e| LlmError::Parse(e.to_string()))?;
        let text = parsed
            .content
            .into_iter()
            .map(|c| c.text)
            .collect::<Vec<_>>()
            .join("");
        Ok(CompletionResponse {
            model: parsed.model,
            text,
            input_tokens: parsed.usage.input_tokens,
            output_tokens: parsed.usage.output_tokens,
            stop_reason: parsed.stop_reason.unwrap_or_else(|| "end_turn".into()),
        })
    }

    async fn stream<'a>(
        &'a self,
        _req: CompletionRequest,
    ) -> Result<BoxStream<'a, Result<TokenChunk, LlmError>>, LlmError> {
        // Stream impl deferred to Phase F (paper draft); single-shot
        // is enough for the conjecture LLM call.
        Err(LlmError::Other(
            "stream not implemented for Anthropic in Phase C".into(),
        ))
    }
}
