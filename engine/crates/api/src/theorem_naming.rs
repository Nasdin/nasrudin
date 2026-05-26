//! LLM-driven naming for emergent theorems.
//!
//! Every theorem in the corpus deserves a human-readable name + a
//! one-sentence description. The 6 curated headlines short-circuit via
//! [`nasrudin_derive::headline_registry::match_canonical`]; for
//! everything else (the long tail of GA-discovered side lemmas), this
//! module asks Kimi K2.6 to read the canonical S-expr + Lean source +
//! axioms used and emit `{ name, description }` JSON.
//!
//! Wired in two places:
//!
//!   * [`reverify::flip_verified`](crate::reverify::ReverifyQueue::flip_verified)
//!     spawns a naming task right after a row flips to Verified.
//!   * `POST /api/admin/theorems/backfill_names` walks the long tail
//!     of pre-existing Verified rows whose `display_name` is still NULL.
//!
//! Both paths bound concurrency through `AppState.naming_semaphore` (3
//! in flight at a time — we don't want a backfill burst stealing all
//! the Gradient bandwidth from the steerer).

use async_trait::async_trait;
use serde::Deserialize;

use nasrudin_llm::{
    CompletionRequest, GradientProvider, LlmError, LlmProvider, ResponseFormat,
};

const SYSTEM_PROMPT: &str = include_str!("theorem_naming_system_prompt.txt");

const MAX_NAME_LEN: usize = 60;
const MAX_DESCRIPTION_LEN: usize = 200;
const MAX_LEAN_SOURCE_LEN: usize = 3000;

#[derive(Debug, Clone)]
pub struct NamedTheorem {
    pub display_name: String,
    pub description: String,
}

#[derive(Debug, thiserror::Error)]
pub enum NamingError {
    #[error("llm: {0}")]
    Llm(String),
    #[error("parse: {0}")]
    Parse(String),
    #[error("invalid response: {0}")]
    Invalid(String),
}

/// Internal LLM-call surface so tests can swap in a canned-reply fake.
/// Mirrors the [`crate::steerer::cycle::LlmCaller`] pattern.
#[async_trait]
pub trait NamingLlm: Send + Sync {
    async fn complete(&self, system: &str, user: &str) -> Result<String, NamingError>;
}

pub struct NamingClient {
    llm: Box<dyn NamingLlm>,
}

impl NamingClient {
    /// Build the production client. Uses `GRADIENT_API_KEY` +
    /// `STEERER_MODEL` (default `kimi-k2.6`, matching the steerer).
    pub fn from_env() -> Result<Self, LlmError> {
        let provider = GradientProvider::from_env()?;
        let model = std::env::var("STEERER_MODEL").unwrap_or_else(|_| "kimi-k2.6".into());
        Ok(Self {
            llm: Box::new(GradientNamingLlm {
                provider,
                model,
                strict_failed: std::sync::atomic::AtomicBool::new(false),
            }),
        })
    }

    /// Test/injection constructor.
    pub fn with_llm(llm: Box<dyn NamingLlm>) -> Self {
        Self { llm }
    }

    pub async fn name_theorem(
        &self,
        canonical: &str,
        lean_source: &str,
        axioms_used: &[String],
        domain: &str,
    ) -> Result<NamedTheorem, NamingError> {
        let user_prompt = build_user_prompt(canonical, lean_source, axioms_used, domain);
        let raw = self.llm.complete(SYSTEM_PROMPT, &user_prompt).await?;
        parse_and_validate(&raw)
    }
}

fn build_user_prompt(
    canonical: &str,
    lean_source: &str,
    axioms_used: &[String],
    domain: &str,
) -> String {
    let lean = truncate_chars(lean_source, MAX_LEAN_SOURCE_LEN);
    let axioms = if axioms_used.is_empty() {
        "(none)".to_string()
    } else {
        axioms_used.join(", ")
    };
    format!(
        "Domain: {domain}\n\nCanonical (prefix S-expression):\n{canonical}\n\n\
         Axioms used: {axioms}\n\nLean source:\n```lean\n{lean}\n```\n\n\
         Emit JSON: {{ \"name\": \"...\", \"description\": \"...\" }}"
    )
}

fn truncate_chars(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        s.to_string()
    } else {
        let mut out: String = s.chars().take(max).collect();
        out.push_str("…");
        out
    }
}

#[derive(Deserialize)]
struct RawNamed {
    name: String,
    description: String,
}

fn parse_and_validate(raw: &str) -> Result<NamedTheorem, NamingError> {
    let trimmed = strip_code_fence(raw.trim());
    let parsed: RawNamed = serde_json::from_str(trimmed)
        .map_err(|e| NamingError::Parse(e.to_string()))?;
    let name = sanitize_and_cap(&parsed.name, MAX_NAME_LEN);
    let description = sanitize_and_cap(&parsed.description, MAX_DESCRIPTION_LEN);
    if name.is_empty() {
        return Err(NamingError::Invalid("empty name".into()));
    }
    if description.is_empty() {
        return Err(NamingError::Invalid("empty description".into()));
    }
    Ok(NamedTheorem {
        display_name: name,
        description,
    })
}

fn strip_code_fence(s: &str) -> &str {
    let s = s.strip_prefix("```json").unwrap_or(s);
    let s = s.strip_prefix("```").unwrap_or(s);
    let s = s.strip_suffix("```").unwrap_or(s);
    s.trim()
}

fn sanitize_and_cap(s: &str, max: usize) -> String {
    let cleaned: String = s
        .chars()
        .filter(|c| !c.is_control() || *c == ' ')
        .collect::<String>()
        .trim()
        .to_string();
    if cleaned.chars().count() <= max {
        cleaned
    } else {
        cleaned.chars().take(max).collect()
    }
}

/// Production [`NamingLlm`] backed by Gradient + Kimi K2.6. Identical
/// strict→soft fallback policy to [`crate::steerer::cycle::GradientCaller`]:
/// start in `json_schema` mode, latch to `json_object` permanently if
/// the provider 400s once.
struct GradientNamingLlm {
    provider: GradientProvider,
    model: String,
    strict_failed: std::sync::atomic::AtomicBool,
}

impl GradientNamingLlm {
    fn schema() -> serde_json::Value {
        serde_json::json!({
            "type": "object",
            "additionalProperties": false,
            "required": ["name", "description"],
            "properties": {
                "name": { "type": "string", "minLength": 1, "maxLength": 120 },
                "description": { "type": "string", "minLength": 1, "maxLength": 400 }
            }
        })
    }
}

#[async_trait]
impl NamingLlm for GradientNamingLlm {
    async fn complete(&self, system: &str, user: &str) -> Result<String, NamingError> {
        let strict = !self
            .strict_failed
            .load(std::sync::atomic::Ordering::Relaxed);
        let response_format = if strict {
            ResponseFormat::JsonSchema {
                name: "NamedTheorem".into(),
                schema: Self::schema(),
            }
        } else {
            ResponseFormat::Json {
                schema: serde_json::json!({}),
            }
        };
        let req = CompletionRequest {
            model: self.model.clone(),
            system_prompt: system.to_owned(),
            user_prompt: user.to_owned(),
            max_tokens: 2048,
            temperature: 0.3,
            stop_sequences: vec![],
            response_format,
        };
        match self.provider.complete(req).await {
            Ok(r) => Ok(r.text),
            Err(LlmError::Http { status: 400, body }) if strict => {
                self.strict_failed
                    .store(true, std::sync::atomic::Ordering::Relaxed);
                tracing::warn!(
                    body = %body,
                    "Gradient rejected json_schema for naming; falling back to json_object"
                );
                let retry = CompletionRequest {
                    model: self.model.clone(),
                    system_prompt: system.to_owned(),
                    user_prompt: user.to_owned(),
                    max_tokens: 2048,
                    temperature: 0.3,
                    stop_sequences: vec![],
                    response_format: ResponseFormat::Json {
                        schema: serde_json::json!({}),
                    },
                };
                let r = self
                    .provider
                    .complete(retry)
                    .await
                    .map_err(|e| NamingError::Llm(e.to_string()))?;
                Ok(r.text)
            }
            Err(e) => Err(NamingError::Llm(e.to_string())),
        }
    }
}

impl From<LlmError> for NamingError {
    fn from(e: LlmError) -> Self {
        NamingError::Llm(e.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct CannedLlm {
        reply: String,
    }

    #[async_trait]
    impl NamingLlm for CannedLlm {
        async fn complete(&self, _system: &str, _user: &str) -> Result<String, NamingError> {
            Ok(self.reply.clone())
        }
    }

    struct FailingLlm;

    #[async_trait]
    impl NamingLlm for FailingLlm {
        async fn complete(&self, _system: &str, _user: &str) -> Result<String, NamingError> {
            Err(NamingError::Llm("boom".into()))
        }
    }

    fn client_with_reply(reply: &str) -> NamingClient {
        NamingClient::with_llm(Box::new(CannedLlm { reply: reply.into() }))
    }

    #[tokio::test]
    async fn parses_well_formed_reply() {
        let c = client_with_reply(
            r#"{"name":"Energy-momentum relation","description":"Relates total energy to momentum and rest mass."}"#,
        );
        let n = c
            .name_theorem("(= v:E v:E)", "theorem t : E = E := by rfl", &[], "sr")
            .await
            .unwrap();
        assert_eq!(n.display_name, "Energy-momentum relation");
        assert!(n.description.starts_with("Relates total energy"));
    }

    #[tokio::test]
    async fn strips_markdown_fence() {
        let c = client_with_reply(
            "```json\n{\"name\":\"X\",\"description\":\"Y.\"}\n```",
        );
        let n = c.name_theorem("c", "l", &[], "d").await.unwrap();
        assert_eq!(n.display_name, "X");
        assert_eq!(n.description, "Y.");
    }

    #[tokio::test]
    async fn rejects_empty_name() {
        let c = client_with_reply(r#"{"name":"","description":"d"}"#);
        assert!(matches!(
            c.name_theorem("c", "l", &[], "d").await,
            Err(NamingError::Invalid(_))
        ));
    }

    #[tokio::test]
    async fn rejects_empty_description() {
        let c = client_with_reply(r#"{"name":"n","description":"  "}"#);
        assert!(matches!(
            c.name_theorem("c", "l", &[], "d").await,
            Err(NamingError::Invalid(_))
        ));
    }

    #[tokio::test]
    async fn rejects_garbage_json() {
        let c = client_with_reply("{not json");
        assert!(matches!(
            c.name_theorem("c", "l", &[], "d").await,
            Err(NamingError::Parse(_))
        ));
    }

    #[tokio::test]
    async fn propagates_llm_error() {
        let c = NamingClient::with_llm(Box::new(FailingLlm));
        assert!(matches!(
            c.name_theorem("c", "l", &[], "d").await,
            Err(NamingError::Llm(_))
        ));
    }

    #[tokio::test]
    async fn caps_oversize_description() {
        let long = "a".repeat(500);
        let reply = format!(r#"{{"name":"n","description":"{}"}}"#, long);
        let c = client_with_reply(&reply);
        let n = c.name_theorem("c", "l", &[], "d").await.unwrap();
        assert_eq!(n.description.chars().count(), MAX_DESCRIPTION_LEN);
    }

    #[tokio::test]
    async fn caps_oversize_name() {
        let long = "a".repeat(120);
        let reply = format!(r#"{{"name":"{}","description":"ok."}}"#, long);
        let c = client_with_reply(&reply);
        let n = c.name_theorem("c", "l", &[], "d").await.unwrap();
        assert_eq!(n.display_name.chars().count(), MAX_NAME_LEN);
    }

    #[tokio::test]
    async fn strips_control_chars() {
        let reply = "{\"name\":\"foo\\u0007bar\",\"description\":\"a\\u0000b.\"}";
        let c = client_with_reply(reply);
        let n = c.name_theorem("c", "l", &[], "d").await.unwrap();
        assert!(!n.display_name.contains('\u{0007}'));
        assert!(!n.description.contains('\u{0000}'));
    }

    #[test]
    fn truncates_long_lean_source() {
        let big = "x".repeat(MAX_LEAN_SOURCE_LEN * 2);
        let prompt = build_user_prompt("c", &big, &[], "d");
        // The truncated lean source plus the fence/header overhead must
        // be far below the 2x raw input.
        assert!(prompt.len() < big.len());
        assert!(prompt.contains("…"));
    }

    #[test]
    fn axiom_list_serialises_into_prompt() {
        let p = build_user_prompt("c", "l", &["four_momentum".into(), "ms".into()], "sr");
        assert!(p.contains("four_momentum, ms"));
        assert!(p.contains("Domain: sr"));
    }
}
