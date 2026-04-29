//! End-to-end Ollama provider against a mock server.

use nasrudin_llm::{CompletionRequest, LlmProvider, OllamaProvider, ResponseFormat};
use wiremock::matchers::{method, path};
use wiremock::{Mock, MockServer, ResponseTemplate};

#[tokio::test]
async fn complete_round_trips_against_mock() {
    let server = MockServer::start().await;
    Mock::given(method("POST"))
        .and(path("/api/generate"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "model": "llama3.1",
            "response": "Local model says hi.",
            "done": true,
            "done_reason": "stop",
            "prompt_eval_count": 11,
            "eval_count": 7
        })))
        .mount(&server)
        .await;

    let provider = OllamaProvider::with_base_url(server.uri());
    let resp = provider
        .complete(CompletionRequest {
            model: "llama3.1".into(),
            system_prompt: "you are helpful".into(),
            user_prompt: "hi".into(),
            max_tokens: 256,
            temperature: 0.0,
            stop_sequences: vec![],
            response_format: ResponseFormat::Free,
        })
        .await
        .expect("complete returns Ok");
    assert_eq!(resp.text, "Local model says hi.");
    assert_eq!(resp.input_tokens, 11);
    assert_eq!(resp.output_tokens, 7);
}

#[tokio::test]
async fn http_500_maps_to_http_error() {
    let server = MockServer::start().await;
    Mock::given(method("POST"))
        .and(path("/api/generate"))
        .respond_with(ResponseTemplate::new(500).set_body_string("internal"))
        .mount(&server)
        .await;
    let provider = OllamaProvider::with_base_url(server.uri());
    let err = provider
        .complete(CompletionRequest {
            model: "llama3.1".into(),
            system_prompt: "".into(),
            user_prompt: "".into(),
            max_tokens: 1,
            temperature: 0.0,
            stop_sequences: vec![],
            response_format: ResponseFormat::Free,
        })
        .await
        .expect_err("expected error");
    assert!(matches!(err, nasrudin_llm::LlmError::Http { .. }));
}
