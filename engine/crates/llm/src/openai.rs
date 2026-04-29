//! OpenAI Chat Completions API.

use async_trait::async_trait;
use futures::stream::BoxStream;
use serde::{Deserialize, Serialize};

use crate::provider::{
    CompletionRequest, CompletionResponse, LlmError, LlmProvider, ResponseFormat, TokenChunk,
};

const SUPPORTED: &[&str] = &["gpt-4o", "gpt-4o-mini", "o1", "o1-mini"];

pub struct OpenAiProvider {
    client: reqwest::Client,
    api_key: String,
    base_url: String,
}

impl OpenAiProvider {
    pub fn new(api_key: String) -> Self {
        Self {
            client: reqwest::Client::builder()
                .timeout(std::time::Duration::from_secs(60))
                .build()
                .expect("reqwest client"),
            api_key,
            base_url: "https://api.openai.com".into(),
        }
    }

    pub fn with_base_url(mut self, url: impl Into<String>) -> Self {
        self.base_url = url.into();
        self
    }
}

#[derive(Serialize)]
struct ChatRequest<'a> {
    model: &'a str,
    messages: Vec<ChatMessage<'a>>,
    max_completion_tokens: u32,
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
    model: String,
    choices: Vec<Choice>,
    usage: Usage,
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
    prompt_tokens: u32,
    completion_tokens: u32,
}

#[async_trait]
impl LlmProvider for OpenAiProvider {
    fn name(&self) -> &'static str {
        "openai"
    }

    fn supported_models(&self) -> &[&'static str] {
        SUPPORTED
    }

    async fn complete(&self, req: CompletionRequest) -> Result<CompletionResponse, LlmError> {
        if !SUPPORTED.contains(&req.model.as_str()) {
            return Err(LlmError::UnsupportedModel(req.model));
        }
        let response_format = match &req.response_format {
            ResponseFormat::Free => None,
            ResponseFormat::Json { .. } => Some(serde_json::json!({"type": "json_object"})),
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
            max_completion_tokens: req.max_tokens,
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
        Ok(CompletionResponse {
            model: parsed.model,
            text: choice.message.content,
            input_tokens: parsed.usage.prompt_tokens,
            output_tokens: parsed.usage.completion_tokens,
            stop_reason: choice.finish_reason.unwrap_or_else(|| "stop".into()),
        })
    }

    async fn stream<'a>(
        &'a self,
        _req: CompletionRequest,
    ) -> Result<BoxStream<'a, Result<TokenChunk, LlmError>>, LlmError> {
        Err(LlmError::Other(
            "stream not implemented for OpenAI in Phase C".into(),
        ))
    }
}
