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
//!  2. **Default steerer model is resolved dynamically.** Operators can
//!     pin `STEERER_MODEL`; otherwise the API daemon queries Gradient's
//!     live model catalog and picks the newest GLM-family model it can
//!     identify. `supported_models()` is advisory only.
//!  3. **Lives in its own provider** so the BYO LLM Registry never
//!     accidentally dispatches a user request to the server's key.

use async_trait::async_trait;
use futures::stream::BoxStream;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

use crate::provider::{
    CompletionRequest, CompletionResponse, LlmError, LlmProvider, ResponseFormat, TokenChunk,
};

const DEFAULT_BASE_URL: &str = "https://inference.do-ai.run";
const DEFAULT_MAX_ATTEMPTS: u32 = 4;
const DEFAULT_MODEL_CACHE_TTL_SECONDS: u64 = 86_400;
// Names mirror DigitalOcean Gradient's serverless catalog. The list is
// advisory — `list_models()` queries the live catalog at boot and the
// daemon doesn't hard-reject anything not listed here, so adding a
// model here is purely about giving operators a sane default.
//
// Advisory fallback list. The steerer resolves the live GLM catalog at
// boot; this list is only for diagnostics and offline tests.
const SUPPORTED: &[&str] = &[
    "glm-5.2",
    "kimi-k2.6",
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
    max_attempts: u32,
}

#[derive(Debug, Clone)]
pub struct ResolvedGradientModel {
    pub model: String,
    pub source: GradientModelSource,
    pub catalog_models: Option<Vec<String>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GradientModelSource {
    ExplicitEnv,
    CachedCatalog,
    LiveCatalog,
    Fallback,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct CachedGradientModel {
    model: String,
    cached_at_unix_secs: u64,
}

impl GradientProvider {
    pub fn new(api_key: String) -> Self {
        Self {
            // Kimi K2.5 with reasoning_content + a steerer prompt that
            // includes the full physics atom registry can take 60-180 s
            // to come back. 60 s was tripping reqwest with
            // "transport: error sending request" every cycle on prod.
            // Also force HTTP/1.1: Cloudflare's HTTP/2 stream behind
            // inference.do-ai.run sometimes drops the connection between
            // the connect and the request body, surfacing as the same
            // generic transport error. HTTP/1.1 keep-alive is rock-solid.
            client: reqwest::Client::builder()
                .timeout(std::time::Duration::from_secs(300))
                .connect_timeout(std::time::Duration::from_secs(30))
                .http1_only()
                .pool_idle_timeout(std::time::Duration::from_secs(90))
                .build()
                .expect("reqwest client"),
            api_key,
            base_url: DEFAULT_BASE_URL.into(),
            max_attempts: DEFAULT_MAX_ATTEMPTS,
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

    /// Limit completion retry attempts. The cluster steerer uses this
    /// to make its per-refresh token ceiling meaningful; other callers
    /// can keep the default transient-failure retries.
    pub fn with_max_attempts(mut self, max_attempts: u32) -> Self {
        self.max_attempts = max_attempts.max(1);
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
        let r: R = resp
            .json()
            .await
            .map_err(|e| LlmError::Parse(e.to_string()))?;
        Ok(r.data.into_iter().map(|m| m.id).collect())
    }

    /// Resolve the model used by the high-level steerer.
    ///
    /// Priority:
    /// 1. `STEERER_MODEL`, when explicitly set.
    /// 2. Latest GLM-family model discovered in Gradient's live catalog.
    /// 3. `GRADIENT_GLM_MODEL_FALLBACK`, defaulting to `glm-5.2`.
    pub async fn resolve_steerer_model(&self) -> String {
        self.resolve_steerer_model_detailed().await.model
    }

    pub async fn resolve_steerer_model_detailed(&self) -> ResolvedGradientModel {
        if let Ok(model) = std::env::var("STEERER_MODEL") {
            let model = model.trim();
            if !model.is_empty() {
                return ResolvedGradientModel {
                    model: model.to_string(),
                    source: GradientModelSource::ExplicitEnv,
                    catalog_models: None,
                };
            }
        }
        let fallback =
            std::env::var("GRADIENT_GLM_MODEL_FALLBACK").unwrap_or_else(|_| "glm-5.2".into());
        let cache_path = steerer_model_cache_path();
        let ttl = steerer_model_cache_ttl_seconds();
        if let Some(model) = load_cached_steerer_model(&cache_path, ttl) {
            return ResolvedGradientModel {
                model,
                source: GradientModelSource::CachedCatalog,
                catalog_models: None,
            };
        }
        match self.list_models().await {
            Ok(models) => {
                let live_model = latest_glm_model(&models);
                let source = if live_model.is_some() {
                    GradientModelSource::LiveCatalog
                } else {
                    GradientModelSource::Fallback
                };
                let model = live_model.unwrap_or_else(|| fallback.clone());
                if source == GradientModelSource::LiveCatalog {
                    persist_cached_steerer_model(&cache_path, &model);
                }
                ResolvedGradientModel {
                    model,
                    source,
                    catalog_models: Some(models),
                }
            }
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    fallback = %fallback,
                    "Gradient model catalog probe failed; using GLM fallback model"
                );
                ResolvedGradientModel {
                    model: fallback,
                    source: GradientModelSource::Fallback,
                    catalog_models: None,
                }
            }
        }
    }
}

fn now_unix_secs() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

fn steerer_model_cache_ttl_seconds() -> u64 {
    std::env::var("GRADIENT_MODEL_CACHE_TTL_SECONDS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(DEFAULT_MODEL_CACHE_TTL_SECONDS)
}

fn steerer_model_cache_path() -> PathBuf {
    if let Ok(path) = std::env::var("GRADIENT_MODEL_CACHE_PATH") {
        return PathBuf::from(path);
    }
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
    PathBuf::from(home)
        .join(".local")
        .join("share")
        .join("nasrudin-worker")
        .join("gradient_steerer_model.json")
}

fn load_cached_steerer_model(path: &Path, ttl_seconds: u64) -> Option<String> {
    if ttl_seconds == 0 {
        return None;
    }
    let bytes = std::fs::read(path).ok()?;
    let cached: CachedGradientModel = serde_json::from_slice(&bytes).ok()?;
    if cached.model.trim().is_empty() {
        return None;
    }
    let age = now_unix_secs().saturating_sub(cached.cached_at_unix_secs);
    (age <= ttl_seconds).then_some(cached.model)
}

fn persist_cached_steerer_model(path: &Path, model: &str) {
    if model.trim().is_empty() {
        return;
    }
    if let Some(parent) = path.parent()
        && let Err(e) = std::fs::create_dir_all(parent)
    {
        tracing::warn!(error = %e, path = %parent.display(), "failed to create Gradient model cache dir");
        return;
    }
    let cached = CachedGradientModel {
        model: model.to_string(),
        cached_at_unix_secs: now_unix_secs(),
    };
    let Ok(bytes) = serde_json::to_vec_pretty(&cached) else {
        return;
    };
    if let Err(e) = std::fs::write(path, bytes) {
        tracing::warn!(error = %e, path = %path.display(), "failed to persist Gradient model cache");
    }
}

/// Pick the newest GLM-family model from a list of Gradient model IDs.
/// Accepts IDs such as `glm-5.2`, `zai-glm-5.2`, or `glm-5.2-air`.
pub fn latest_glm_model(models: &[String]) -> Option<String> {
    models
        .iter()
        .filter_map(|model| glm_version_key(model).map(|key| (key, model)))
        .max_by(|(a, am), (b, bm)| a.cmp(b).then_with(|| am.cmp(bm)))
        .map(|(_, model)| model.clone())
}

fn glm_version_key(model: &str) -> Option<Vec<u32>> {
    let lower = model.to_ascii_lowercase();
    let glm_idx = lower.find("glm")?;
    let after = &lower[glm_idx + 3..];
    let mut nums = Vec::new();
    let mut current = String::new();
    for ch in after.chars() {
        if ch.is_ascii_digit() {
            current.push(ch);
        } else if ch == '.' || ch == '-' || ch == '_' {
            if !current.is_empty() {
                nums.push(current.parse::<u32>().ok()?);
                current.clear();
            }
        } else if !current.is_empty() {
            nums.push(current.parse::<u32>().ok()?);
            break;
        }
    }
    if !current.is_empty() {
        nums.push(current.parse::<u32>().ok()?);
    }
    (!nums.is_empty()).then_some(nums)
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
    // Kimi K2.5/K2.6 emit `content: null` when the model spent its
    // budget on `reasoning_content` and never produced a final answer
    // (e.g. hit max_tokens mid-think). serde's `#[default]` only fires
    // for missing fields, not explicit null — without Option<String>
    // the response decode panics with "invalid type: null, expected
    // a string" and the steerer cycle aborts.
    #[serde(default)]
    content: Option<String>,
    #[serde(default)]
    reasoning_content: Option<String>,
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
                // OpenAI-compatible strict structured outputs. Kimi K2.6
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

        // inference.do-ai.run drops connections intermittently (transport
        // errors / 5xx). A single failed attempt used to silently leave
        // theorem display_names NULL ("gen N" in the UI) and abort steerer
        // cycles. Retry transient failures with exponential backoff; do NOT
        // retry deterministic failures (auth, 4xx) — those won't fix
        // themselves and would just waste the budget.
        let mut attempt = 0u32;
        loop {
            attempt += 1;
            let outcome: Result<CompletionResponse, LlmError> = async {
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
                    // Prefer `content` (final answer); fall back to
                    // `reasoning_content` so a truncated cycle still yields the
                    // best-available text instead of an empty string that
                    // breaks downstream JSON-schema parsing.
                    text: choice
                        .message
                        .content
                        .filter(|s| !s.is_empty())
                        .or(choice.message.reasoning_content)
                        .unwrap_or_default(),
                    input_tokens: usage.prompt_tokens,
                    output_tokens: usage.completion_tokens,
                    stop_reason: choice.finish_reason.unwrap_or_else(|| "stop".into()),
                })
            }
            .await;

            match outcome {
                Ok(r) => return Ok(r),
                Err(e) => {
                    let retryable = matches!(
                        &e,
                        LlmError::Transport(_) | LlmError::RateLimited { .. } | LlmError::Parse(_)
                    ) || matches!(&e, LlmError::Http { status, .. } if *status >= 500);
                    if retryable && attempt < self.max_attempts {
                        let backoff_ms = 300u64 * 2u64.pow(attempt - 1); // 300, 600, 1200
                        tracing::warn!(
                            attempt,
                            max_attempts = self.max_attempts,
                            backoff_ms,
                            error = %e,
                            "gradient call failed; retrying after backoff"
                        );
                        tokio::time::sleep(std::time::Duration::from_millis(backoff_ms)).await;
                        continue;
                    }
                    return Err(e);
                }
            }
        }
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
        assert!(p.supported_models().contains(&"glm-5.2"));
        assert!(p.supported_models().contains(&"kimi-k2.6"));
        // K2.5 stays during migration so deployments mid-upgrade
        // don't hard-fail.
        assert!(p.supported_models().contains(&"kimi-k2.5"));
    }

    #[test]
    fn latest_glm_model_picks_highest_version() {
        let models = vec![
            "kimi-k2.6".to_string(),
            "zai-glm-4.5".to_string(),
            "glm-5.1-air".to_string(),
            "glm-5.2".to_string(),
        ];

        assert_eq!(latest_glm_model(&models), Some("glm-5.2".to_string()));
    }

    #[test]
    fn latest_glm_model_returns_none_when_absent() {
        let models = vec!["kimi-k2.6".to_string(), "llama3.3-70b-instruct".to_string()];

        assert_eq!(latest_glm_model(&models), None);
    }

    #[test]
    fn cached_steerer_model_respects_ttl() {
        let path = std::env::temp_dir().join(format!(
            "nasrudin_gradient_model_cache_{}.json",
            std::process::id()
        ));
        let cached = CachedGradientModel {
            model: "glm-5.2".to_string(),
            cached_at_unix_secs: now_unix_secs(),
        };
        std::fs::write(&path, serde_json::to_vec(&cached).unwrap()).unwrap();

        assert_eq!(
            load_cached_steerer_model(&path, 60),
            Some("glm-5.2".to_string())
        );
        assert_eq!(load_cached_steerer_model(&path, 0), None);
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn persist_cached_steerer_model_round_trips() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("gradient_model.json");

        persist_cached_steerer_model(&path, "glm-5.2");

        assert_eq!(
            load_cached_steerer_model(&path, 60),
            Some("glm-5.2".to_string())
        );
    }

    #[test]
    fn max_attempts_can_be_limited_for_budgeted_callers() {
        let p = GradientProvider::new("test".into()).with_max_attempts(1);
        assert_eq!(p.max_attempts, 1);

        let p = GradientProvider::new("test".into()).with_max_attempts(0);
        assert_eq!(p.max_attempts, 1);
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
