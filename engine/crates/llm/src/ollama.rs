//! Ollama local HTTP provider (default localhost:11434).
//!
//! Unlike Anthropic / OpenAI this provider doesn't require a key —
//! `api_key` on the user_llm_keys row is optional for `ollama` and
//! ignored if present. The model list is open: any model the user
//! has pulled locally works, so `supported_models` returns an empty
//! slice and `complete` does not pre-validate.

use async_trait::async_trait;
use futures::stream::BoxStream;
use serde::{Deserialize, Serialize};

use crate::provider::{
    CompletionRequest, CompletionResponse, LlmError, LlmProvider, ResponseFormat, TokenChunk,
};

pub struct OllamaProvider {
    client: reqwest::Client,
    base_url: String,
}

impl OllamaProvider {
    pub fn new() -> Self {
        Self::with_base_url("http://localhost:11434")
    }

    pub fn with_base_url(url: impl Into<String>) -> Self {
        Self {
            client: reqwest::Client::builder()
                .timeout(std::time::Duration::from_secs(60))
                .build()
                .expect("reqwest client"),
            base_url: url.into(),
        }
    }
}

impl Default for OllamaProvider {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Serialize)]
struct GenerateRequest<'a> {
    model: &'a str,
    prompt: String,
    system: &'a str,
    stream: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    format: Option<&'a str>,
    options: GenerateOptions,
}

#[derive(Serialize)]
struct GenerateOptions {
    temperature: f32,
    num_predict: u32,
    stop: Vec<String>,
}

#[derive(Deserialize)]
struct GenerateResponse {
    model: String,
    response: String,
    #[serde(default)]
    done_reason: Option<String>,
    #[serde(default)]
    prompt_eval_count: u32,
    #[serde(default)]
    eval_count: u32,
}

#[async_trait]
impl LlmProvider for OllamaProvider {
    fn name(&self) -> &'static str {
        "ollama"
    }

    fn supported_models(&self) -> &[&'static str] {
        // Any locally-pulled model works; no static whitelist.
        &[]
    }

    async fn complete(&self, req: CompletionRequest) -> Result<CompletionResponse, LlmError> {
        let format = match &req.response_format {
            ResponseFormat::Free => None,
            ResponseFormat::Json { .. } => Some("json"),
        };
        let body = GenerateRequest {
            model: &req.model,
            prompt: req.user_prompt.clone(),
            system: &req.system_prompt,
            stream: false,
            format,
            options: GenerateOptions {
                temperature: req.temperature,
                num_predict: req.max_tokens,
                stop: req.stop_sequences.clone(),
            },
        };
        let url = format!("{}/api/generate", self.base_url);
        let resp = self.client.post(&url).json(&body).send().await?;
        let status = resp.status();
        if !status.is_success() {
            let text = resp.text().await.unwrap_or_default();
            return Err(LlmError::Http {
                status: status.as_u16(),
                body: text,
            });
        }
        let parsed: GenerateResponse = resp
            .json()
            .await
            .map_err(|e| LlmError::Parse(e.to_string()))?;
        Ok(CompletionResponse {
            model: parsed.model,
            text: parsed.response,
            input_tokens: parsed.prompt_eval_count,
            output_tokens: parsed.eval_count,
            stop_reason: parsed.done_reason.unwrap_or_else(|| "stop".into()),
        })
    }

    async fn stream<'a>(
        &'a self,
        _req: CompletionRequest,
    ) -> Result<BoxStream<'a, Result<TokenChunk, LlmError>>, LlmError> {
        Err(LlmError::Other(
            "stream not implemented for Ollama in Phase C".into(),
        ))
    }
}
