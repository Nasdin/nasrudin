//! Synchronous server-side LLM call: hunch → corpus retrieval → prompt → LLM
//! → suggestions. Decryption happens here so plaintext never crosses module
//! boundaries; the `String` lives only on this stack frame.

use std::sync::Arc;

use thiserror::Error;
use uuid::Uuid;

use nasrudin_llm::{
    encryption::{decrypt, EncryptedKey},
    CompletionRequest, LlmError, Registry, ResponseFormat,
};

use crate::conjecture::prompt::{self, AxiomEntry, NeighbourTheorem};
use crate::conjecture::types::LlmSuggestion;
use crate::state::AppState;

#[derive(Debug, Error)]
pub enum OrchestrateError {
    #[error("provider not registered: {0}")]
    UnknownProvider(String),
    #[error("no api key for provider {0}")]
    NoProviderKey(String),
    #[error("encryption key not configured on server")]
    KeyEncryptUnset,
    #[error("decryption failed")]
    DecryptFailed,
    #[error("postgres unavailable")]
    PgUnavailable,
    #[error("llm call failed: {0}")]
    LlmCall(#[from] LlmError),
    #[error("llm response did not parse as JSON: {0}")]
    InvalidLlmJson(String),
    #[error("db error: {0}")]
    Db(#[from] sea_orm::DbErr),
}

pub async fn run_llm_phase(
    state: &Arc<AppState>,
    user_id: Uuid,
    hunch: &str,
    domain_hint: Option<&str>,
    provider: &str,
    model: &str,
) -> Result<Vec<LlmSuggestion>, OrchestrateError> {
    if !Registry::known_providers().contains(&provider) {
        return Err(OrchestrateError::UnknownProvider(provider.into()));
    }

    let encrypt_key = state
        .llm_encrypt_key
        .as_ref()
        .ok_or(OrchestrateError::KeyEncryptUnset)?;

    let pg = state.pg.as_ref().ok_or(OrchestrateError::PgUnavailable)?;

    let cipher = nasrudin_pg::query::user_llm_keys::get_ciphertext(pg, user_id, provider)
        .await?
        .ok_or_else(|| OrchestrateError::NoProviderKey(provider.into()))?;
    let api_key = decrypt(&EncryptedKey(cipher), encrypt_key)
        .map_err(|_| OrchestrateError::DecryptFailed)?;

    let neighbours = nearest_neighbours(state, hunch, 10);
    let axioms = axiom_catalog(state);
    let user_prompt = prompt::build_user_prompt(hunch, domain_hint, &neighbours, &axioms);

    let req = CompletionRequest {
        model: model.to_string(),
        system_prompt: prompt::SYSTEM_PROMPT.to_string(),
        user_prompt,
        max_tokens: 4096,
        temperature: 0.4,
        stop_sequences: vec![],
        response_format: ResponseFormat::Json {
            schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "suggestions": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "axiom_set": {"type": "array", "items": {"type": "string"}},
                                "initial_population": {"type": "array", "items": {"type": "string"}},
                                "mutation_priors": {"type": "object", "additionalProperties": {"type": "number"}},
                                "target_shape": {"type": "string"},
                                "rationale": {"type": "string"}
                            },
                            "required": ["axiom_set", "initial_population", "mutation_priors", "rationale"]
                        }
                    }
                },
                "required": ["suggestions"]
            }),
        },
    };

    let response = Registry::complete(provider, Some(api_key), req).await?;

    let parsed: ParsedResponse = serde_json::from_str(&response.text)
        .map_err(|e| OrchestrateError::InvalidLlmJson(format!("{e}: {}", response.text)))?;

    // Touch best-effort — UI hint only, not a correctness invariant.
    let _ = nasrudin_pg::query::user_llm_keys::touch_last_used(pg, user_id, provider).await;

    Ok(parsed.suggestions)
}

#[derive(serde::Deserialize)]
struct ParsedResponse {
    suggestions: Vec<LlmSuggestion>,
}

fn nearest_neighbours(state: &Arc<AppState>, _hunch: &str, _k: usize) -> Vec<NeighbourTheorem> {
    // Phase D launches without an Embedder threaded into AppState — adding
    // it requires a fastembed model load at boot which is a separate piece
    // of work. The LLM still produces useful seeds from the axiom catalog
    // alone; corpus retrieval is a quality boost, not a correctness one.
    if state.embed.is_none() {
        return Vec::new();
    }
    Vec::new()
}

fn axiom_catalog(state: &Arc<AppState>) -> Vec<AxiomEntry> {
    let store = state.axiom_store.load();
    store
        .iter()
        .map(|a| AxiomEntry {
            name: a.name.clone(),
            domain: format!("{:?}", a.domain),
            description: a.description.clone(),
        })
        .collect()
}
