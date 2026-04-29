//! End-to-end OpenAI provider against a mock server.

use nasrudin_llm::{CompletionRequest, LlmProvider, OpenAiProvider, ResponseFormat};
use wiremock::matchers::{header, method, path};
use wiremock::{Mock, MockServer, ResponseTemplate};

#[tokio::test]
async fn complete_round_trips_against_mock() {
    let server = MockServer::start().await;
    Mock::given(method("POST"))
        .and(path("/v1/chat/completions"))
        .and(header("authorization", "Bearer fake-key"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "model": "gpt-4o",
            "choices": [{
                "index": 0,
                "message": {"role": "assistant", "content": "Pong from OpenAI."},
                "finish_reason": "stop"
            }],
            "usage": {"prompt_tokens": 5, "completion_tokens": 4, "total_tokens": 9}
        })))
        .mount(&server)
        .await;

    let provider = OpenAiProvider::new("fake-key".into()).with_base_url(server.uri());
    let resp = provider
        .complete(CompletionRequest {
            model: "gpt-4o".into(),
            system_prompt: "you are helpful".into(),
            user_prompt: "ping".into(),
            max_tokens: 256,
            temperature: 0.0,
            stop_sequences: vec![],
            response_format: ResponseFormat::Free,
        })
        .await
        .expect("complete returns Ok");
    assert_eq!(resp.text, "Pong from OpenAI.");
    assert_eq!(resp.input_tokens, 5);
    assert_eq!(resp.output_tokens, 4);
}

#[tokio::test]
async fn http_401_maps_to_unauthorized() {
    let server = MockServer::start().await;
    Mock::given(method("POST"))
        .and(path("/v1/chat/completions"))
        .respond_with(ResponseTemplate::new(401).set_body_string("invalid_api_key"))
        .mount(&server)
        .await;
    let provider = OpenAiProvider::new("fake-key".into()).with_base_url(server.uri());
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
        .expect_err("expected error");
    assert!(matches!(err, nasrudin_llm::LlmError::Unauthorized(_)));
}
