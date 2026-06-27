//! String-keyed dispatch over the three first-class providers.
//!
//! Callers don't construct providers directly; they pass a
//! `(provider_name, plaintext_api_key)` pair and let `Registry`
//! pick the right impl. Reduces handler-side coupling to specific
//! provider types.

use crate::provider::{CompletionRequest, CompletionResponse, LlmError};
use crate::{AnthropicProvider, OllamaProvider, OpenAiProvider};

pub struct Registry;

impl Registry {
    /// All known provider names. Used by frontend dropdowns and the
    /// POST /api/me/llm-keys validation.
    pub fn known_providers() -> &'static [&'static str] {
        &["anthropic", "openai", "ollama"]
    }

    /// Dispatch a single-shot completion to the right provider impl.
    /// `api_key` is the plaintext key; `Registry` is the only place
    /// the plaintext lives (the handler decrypts, dispatches, then
    /// drops the plaintext when the future resolves).
    pub async fn complete(
        provider_name: &str,
        api_key: Option<String>,
        req: CompletionRequest,
    ) -> Result<CompletionResponse, LlmError> {
        use crate::provider::LlmProvider;
        match provider_name {
            "anthropic" => {
                let key = api_key.ok_or_else(|| {
                    LlmError::Unauthorized("anthropic requires an api key".into())
                })?;
                AnthropicProvider::new(key).complete(req).await
            }
            "openai" => {
                let key = api_key
                    .ok_or_else(|| LlmError::Unauthorized("openai requires an api key".into()))?;
                OpenAiProvider::new(key).complete(req).await
            }
            "ollama" => OllamaProvider::new().complete(req).await,
            other => Err(LlmError::Other(format!("unknown provider: {other}"))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_providers_lists_three() {
        let names = Registry::known_providers();
        assert!(names.contains(&"anthropic"));
        assert!(names.contains(&"openai"));
        assert!(names.contains(&"ollama"));
        assert_eq!(names.len(), 3);
    }

    #[tokio::test]
    async fn unknown_provider_returns_other() {
        let err = Registry::complete(
            "bogus",
            None,
            CompletionRequest {
                model: "x".into(),
                system_prompt: "".into(),
                user_prompt: "".into(),
                max_tokens: 1,
                temperature: 0.0,
                stop_sequences: vec![],
                response_format: crate::ResponseFormat::Free,
            },
        )
        .await
        .expect_err("unknown provider must error");
        assert!(matches!(err, LlmError::Other(_)));
    }

    #[tokio::test]
    async fn anthropic_without_key_returns_unauthorized() {
        let err = Registry::complete(
            "anthropic",
            None,
            CompletionRequest {
                model: "claude-sonnet-4-6".into(),
                system_prompt: "".into(),
                user_prompt: "".into(),
                max_tokens: 1,
                temperature: 0.0,
                stop_sequences: vec![],
                response_format: crate::ResponseFormat::Free,
            },
        )
        .await
        .expect_err("missing key must error");
        assert!(matches!(err, LlmError::Unauthorized(_)));
    }
}
