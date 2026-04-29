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
        req: CompletionRequest,
    ) -> Result<BoxStream<'a, Result<TokenChunk, LlmError>>, LlmError> {
        if !SUPPORTED.contains(&req.model.as_str()) {
            return Err(LlmError::UnsupportedModel(req.model));
        }
        // Anthropic Messages API SSE streaming. Set "stream": true and
        // parse the event stream: each `content_block_delta` event
        // carries one text delta; `message_stop` ends the stream.
        let body = serde_json::json!({
            "model": req.model,
            "max_tokens": req.max_tokens,
            "temperature": req.temperature,
            "system": req.system_prompt,
            "messages": [{"role": "user", "content": req.user_prompt}],
            "stream": true,
            "stop_sequences": req.stop_sequences,
        });
        let url = format!("{}/v1/messages", self.base_url);
        let resp = self
            .client
            .post(&url)
            .header("x-api-key", &self.api_key)
            .header("anthropic-version", "2023-06-01")
            .header("content-type", "application/json")
            .header("accept", "text/event-stream")
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

        // The Anthropic SSE wire format is `event: <name>\ndata: {…}\n\n`.
        // We only care about `content_block_delta` (carries `delta.text`)
        // and `message_stop` (terminates). All other events are control
        // metadata and dropped.
        use futures::StreamExt;
        let byte_stream = resp.bytes_stream();

        let chunked = async_stream::stream! {
            let mut buf: Vec<u8> = Vec::with_capacity(4096);
            let mut byte_stream = byte_stream;
            while let Some(item) = byte_stream.next().await {
                let bytes = match item {
                    Ok(b) => b,
                    Err(e) => {
                        yield Err(LlmError::Transport(e));
                        return;
                    }
                };
                buf.extend_from_slice(&bytes);

                // Drain complete SSE records (delimited by "\n\n").
                while let Some(idx) = find_double_newline(&buf) {
                    let record = buf[..idx].to_vec();
                    buf.drain(..idx + 2);
                    let Some((event, data)) = parse_sse_record(&record) else {
                        continue;
                    };
                    if event == "content_block_delta" {
                        // {"type":"content_block_delta","index":0,
                        //  "delta":{"type":"text_delta","text":"…"}}
                        if let Ok(v) = serde_json::from_str::<serde_json::Value>(&data) {
                            if let Some(text) =
                                v.get("delta").and_then(|d| d.get("text")).and_then(|t| t.as_str())
                            {
                                yield Ok(TokenChunk {
                                    text: text.to_string(),
                                    finish_reason: None,
                                });
                            }
                        }
                    } else if event == "message_stop" {
                        yield Ok(TokenChunk {
                            text: String::new(),
                            finish_reason: Some("end_turn".into()),
                        });
                        return;
                    } else if event == "error" {
                        yield Err(LlmError::Other(format!("anthropic stream error: {data}")));
                        return;
                    }
                }
            }
        };
        Ok(Box::pin(chunked))
    }
}

fn find_double_newline(buf: &[u8]) -> Option<usize> {
    buf.windows(2).position(|w| w == b"\n\n")
}

/// Parse one SSE record into (event, data). Returns None for malformed
/// or comment-only records.
fn parse_sse_record(rec: &[u8]) -> Option<(String, String)> {
    let s = std::str::from_utf8(rec).ok()?;
    let mut event: Option<String> = None;
    let mut data = String::new();
    for line in s.lines() {
        if let Some(rest) = line.strip_prefix("event: ") {
            event = Some(rest.to_string());
        } else if let Some(rest) = line.strip_prefix("data: ") {
            if !data.is_empty() {
                data.push('\n');
            }
            data.push_str(rest);
        }
    }
    Some((event?, data))
}
