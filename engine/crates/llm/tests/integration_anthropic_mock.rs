//! End-to-end Anthropic provider against a mock server. No live
//! API calls.

use nasrudin_llm::{AnthropicProvider, CompletionRequest, LlmProvider, ResponseFormat};
use wiremock::matchers::{header, method, path};
use wiremock::{Mock, MockServer, ResponseTemplate};

#[tokio::test]
async fn complete_round_trips_against_mock() {
    let server = MockServer::start().await;
    Mock::given(method("POST"))
        .and(path("/v1/messages"))
        .and(header("x-api-key", "fake-key"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "model": "claude-sonnet-4-6",
            "content": [{"type": "text", "text": "Hello, researcher."}],
            "stop_reason": "end_turn",
            "usage": {"input_tokens": 12, "output_tokens": 8}
        })))
        .mount(&server)
        .await;

    let provider = AnthropicProvider::new("fake-key".into()).with_base_url(server.uri());
    let resp = provider
        .complete(CompletionRequest {
            model: "claude-sonnet-4-6".into(),
            system_prompt: "you are helpful".into(),
            user_prompt: "hello".into(),
            max_tokens: 256,
            temperature: 0.0,
            stop_sequences: vec![],
            response_format: ResponseFormat::Free,
        })
        .await
        .expect("complete returns Ok");
    assert_eq!(resp.text, "Hello, researcher.");
    assert_eq!(resp.input_tokens, 12);
    assert_eq!(resp.output_tokens, 8);
    assert_eq!(resp.stop_reason, "end_turn");
}

#[tokio::test]
async fn unsupported_model_short_circuits_before_http() {
    let provider = AnthropicProvider::new("fake-key".into());
    let err = provider
        .complete(CompletionRequest {
            model: "gpt-4o".into(),
            system_prompt: "".into(),
            user_prompt: "".into(),
            max_tokens: 1,
            temperature: 0.0,
            stop_sequences: vec![],
            response_format: ResponseFormat::Free,
        })
        .await
        .expect_err("unsupported model");
    assert!(matches!(err, nasrudin_llm::LlmError::UnsupportedModel(_)));
}

#[tokio::test]
async fn http_429_maps_to_rate_limited() {
    let server = MockServer::start().await;
    Mock::given(method("POST"))
        .and(path("/v1/messages"))
        .respond_with(ResponseTemplate::new(429).set_body_string("rate-limited"))
        .mount(&server)
        .await;
    let provider = AnthropicProvider::new("fake-key".into()).with_base_url(server.uri());
    let err = provider
        .complete(CompletionRequest {
            model: "claude-sonnet-4-6".into(),
            system_prompt: "".into(),
            user_prompt: "".into(),
            max_tokens: 1,
            temperature: 0.0,
            stop_sequences: vec![],
            response_format: ResponseFormat::Free,
        })
        .await
        .expect_err("expected error");
    assert!(matches!(err, nasrudin_llm::LlmError::RateLimited { .. }));
}
