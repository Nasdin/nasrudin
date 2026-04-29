# LLM-Guided Search — Phase C — LLM Router & Key Vault Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship the `nasrudin-llm` crate (provider trait + Anthropic / OpenAI / Ollama impls) and the BYO API-key vault (encrypted-at-rest Postgres storage, `/api/me/llm-keys` CRUD, Settings UI section). After this phase lands, users can save provider keys; Phase D wires the conjecture loop on top.

**Architecture:** New crate `engine/crates/llm/` exposes `LlmProvider: Send + Sync` with `complete()` (single-shot) and `stream()` (streaming) methods plus structured `CompletionRequest`/`CompletionResponse` types. Three first-class providers: Anthropic Messages API, OpenAI Chat Completions, Ollama local HTTP. New Postgres table `user_llm_keys` stores AES-256-GCM-encrypted bearer tokens (32-byte server key from `NASRUDIN_KEY_ENCRYPT` env var, 12-byte random nonce prepended to ciphertext, last-4 chars stored separately for UI display). Three new endpoints (`GET`/`POST`/`DELETE` `/api/me/llm-keys[/:provider]`) live behind cookie auth. Settings UI gets a new "LLM providers" section. No conjecture surface yet — keys are inert until Phase D consumes them.

**Tech Stack:** Rust 1.95, SeaORM 2 (existing), Axum 0.8 (existing), `aes-gcm = "0.10"` + `rand_core` (new workspace deps), `async-trait = "0.1"` (existing), `reqwest` (existing), `futures` for `BoxStream` (new workspace dep), `chrono` (existing).

---

## Spec reference

This plan implements §4 ("LLM router crate") of `docs/superpowers/specs/2026-04-28-llm-guided-search-design.md` plus the Settings-UI changes from §8.2 that pertain to LLM keys. Subsections covered:

- §4.1 — Public API (`LlmProvider`, `CompletionRequest`, `CompletionResponse`).
- §4.2 — Provider implementations (Anthropic, OpenAI, Ollama).
- §4.3 — BYO API keys (table schema, encryption, endpoints).
- §4.4 — Provider selection (default from `user_preferences`).
- §8.2 — Settings UI "LLM providers" section.

Out of scope for this plan (Phase D and later): the `/conjecture` endpoint, the conjecture state machine, paper draft generation, the Settings UI's *non-LLM* additions.

---

## Scope check

This plan covers two tightly-coupled subsystems (the router crate and the key vault). Both ship together because the endpoint is useless without provider impls and the providers are useless without keys. Settings UI is included because the only way to populate the new endpoints is from the UI; without it the table sits empty and the Phase D test loop has nothing to consume.

---

## File structure

**New files:**

| Path | Responsibility |
|---|---|
| `engine/crates/llm/Cargo.toml` | Crate manifest |
| `engine/crates/llm/src/lib.rs` | Module declarations + re-exports |
| `engine/crates/llm/src/provider.rs` | `LlmProvider` trait + `CompletionRequest` / `CompletionResponse` / `LlmError` types |
| `engine/crates/llm/src/anthropic.rs` | Anthropic Messages API impl |
| `engine/crates/llm/src/openai.rs` | OpenAI Chat Completions impl |
| `engine/crates/llm/src/ollama.rs` | Ollama localhost:11434 impl |
| `engine/crates/llm/src/encryption.rs` | AES-256-GCM helpers (`encrypt`, `decrypt`, `key_hint`) |
| `engine/crates/llm/src/registry.rs` | `Registry::dispatch(provider_name, …)` — string-keyed multiplexer |
| `engine/crates/llm/tests/integration_anthropic_mock.rs` | Wiremock-based round-trip for Anthropic |
| `engine/crates/llm/tests/integration_openai_mock.rs` | Wiremock-based round-trip for OpenAI |
| `engine/crates/llm/tests/integration_ollama_mock.rs` | Wiremock-based round-trip for Ollama |
| `engine/crates/pg/src/migrator/m20260710_000006_user_llm_keys.rs` | New `user_llm_keys` table |
| `engine/crates/pg/src/entity/user_llm_keys.rs` | SeaORM entity |
| `engine/crates/pg/src/query/user_llm_keys.rs` | CRUD helpers |
| `engine/crates/api/src/handlers/llm_keys.rs` | `/api/me/llm-keys` handlers |
| `engine/crates/llm/LLM_LAYER.md` | Operator docs |
| `nasrudin-frontend/src/components/settings/LlmKeysSection.tsx` | Settings card with per-provider rows |
| `nasrudin-frontend/src/components/settings/AddKeyModal.tsx` | Modal: provider dropdown + key paste |
| `nasrudin-frontend/src/lib/queries.ts` | `useLlmKeys`, `useSetLlmKey`, `useRevokeLlmKey` (modify) |
| `nasrudin-frontend/src/lib/types.ts` | `LlmKeySummary`, `LlmProviderName` (modify) |

**Modified files:**

| Path | Change |
|---|---|
| `engine/Cargo.toml` | Add `aes-gcm`, `rand_core`, `async-trait`, `futures` to workspace deps; add `crates/llm` member |
| `engine/crates/api/Cargo.toml` | Depend on `nasrudin-llm` |
| `engine/crates/api/src/handlers/mod.rs` | `pub mod llm_keys;` |
| `engine/crates/api/src/main.rs` | Wire `/api/me/llm-keys` routes |
| `engine/crates/api/src/state.rs` | Add `pub llm_encrypt_key: Option<[u8; 32]>` (decoded once at boot) |
| `engine/crates/pg/src/migrator/mod.rs` | Register `m20260710_000006_user_llm_keys` |
| `engine/crates/pg/src/entity/mod.rs` | Re-export new entity |
| `engine/crates/pg/src/query/mod.rs` | `pub mod user_llm_keys;` |
| `nasrudin-frontend/src/routes/settings.tsx` | Mount `<LlmKeysSection />` |

---

## Conventions for this plan

- Run `cargo check --workspace` from `engine/` after every task; expect exit 0 before committing.
- Run `cargo test --workspace --lib` after any task that touches existing tests.
- All commits must end with a `Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>` trailer (the harness does NOT add it automatically); pass commit messages via HEREDOC.
- Commit message style: `feat(llm): …`, `fix(llm): …`, `test(llm): …`, `feat(api): …`, `feat(frontend): …`.
- Frontend TypeScript checks: `cd nasrudin-frontend && pnpm tsc --noEmit` before committing UI changes.
- Phase C is OFF by default in the sense that `NASRUDIN_KEY_ENCRYPT` unset → key endpoints return 503 with `key_encrypt_unset`. Production deployments must set the env var.
- Tests exercise providers via wiremock — never hit a real API key.

---

## Task 1: Workspace deps + crate skeleton

**Files:**
- Modify: `engine/Cargo.toml`
- Create: `engine/crates/llm/Cargo.toml`
- Create: `engine/crates/llm/src/lib.rs` + 5 stub module files

- [ ] **Step 1: Add workspace deps**

In `engine/Cargo.toml`, under `[workspace.dependencies]`, add:

```toml
aes-gcm = "0.10"
rand_core = { version = "0.6", features = ["std"] }
async-trait = "0.1"
futures = "0.3"
```

Under `[workspace] members = [...]`, add `"crates/llm"`.

- [ ] **Step 2: Create the manifest**

Create `engine/crates/llm/Cargo.toml`:

```toml
[package]
name = "nasrudin-llm"
version.workspace = true
edition.workspace = true

[dependencies]
anyhow = { workspace = true }
async-trait = { workspace = true }
aes-gcm = { workspace = true }
rand_core = { workspace = true }
base64 = { workspace = true }
chrono = { workspace = true, features = ["serde"] }
futures = { workspace = true }
reqwest = { version = "0.12", default-features = false, features = ["json", "rustls-tls", "stream"] }
serde = { workspace = true }
serde_json = { workspace = true }
thiserror = { workspace = true }
tokio = { workspace = true }
tracing = { workspace = true }

[dev-dependencies]
wiremock = "0.6"
tokio = { workspace = true, features = ["macros", "rt-multi-thread"] }
```

- [ ] **Step 3: Create `lib.rs` with module skeleton**

Create `engine/crates/llm/src/lib.rs`:

```rust
//! BYO LLM router. Provides a `LlmProvider` trait with three
//! first-class implementations (Anthropic, OpenAI, Ollama) plus an
//! AES-256-GCM helper for encrypting bearer tokens at rest.
//!
//! Phase C of `docs/superpowers/specs/2026-04-28-llm-guided-search-design.md`.

pub mod anthropic;
pub mod encryption;
pub mod ollama;
pub mod openai;
pub mod provider;
pub mod registry;

pub use anthropic::AnthropicProvider;
pub use encryption::{decrypt, encrypt, key_hint, EncryptedKey};
pub use ollama::OllamaProvider;
pub use openai::OpenAiProvider;
pub use provider::{
    CompletionRequest, CompletionResponse, LlmError, LlmProvider, ResponseFormat, TokenChunk,
};
pub use registry::Registry;
```

- [ ] **Step 4: Create stub module files**

Create each of the following with exactly `// stub — implemented in subsequent tasks`:

```bash
mkdir -p /Volumes/CORSAIR/code/personal/nasrudin/engine/crates/llm/src
```

Files: `anthropic.rs`, `encryption.rs`, `ollama.rs`, `openai.rs`, `provider.rs`, `registry.rs`.

(Do not commit yet — module re-exports in lib.rs reference items not yet defined; we'll fill provider.rs next.)

- [ ] **Step 5: Implement provider.rs with the trait + types**

Replace `engine/crates/llm/src/provider.rs` with:

```rust
//! Public surface of the LLM router.

use async_trait::async_trait;
use futures::stream::BoxStream;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionRequest {
    pub model: String,
    pub system_prompt: String,
    pub user_prompt: String,
    pub max_tokens: u32,
    pub temperature: f32,
    #[serde(default)]
    pub stop_sequences: Vec<String>,
    #[serde(default)]
    pub response_format: ResponseFormat,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ResponseFormat {
    #[default]
    Free,
    /// JSON output expected. `schema` is provider-specific (Anthropic/
    /// OpenAI both accept JSON Schema; Ollama just sets format=json).
    Json {
        schema: serde_json::Value,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionResponse {
    pub model: String,
    pub text: String,
    pub input_tokens: u32,
    pub output_tokens: u32,
    pub stop_reason: String,
}

/// One streamed chunk. `text` is the incremental delta.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenChunk {
    pub text: String,
    pub finish_reason: Option<String>,
}

#[derive(Debug, Error)]
pub enum LlmError {
    #[error("HTTP {status}: {body}")]
    Http { status: u16, body: String },
    #[error("rate-limited (retry after {retry_after_ms} ms)")]
    RateLimited { retry_after_ms: u64 },
    #[error("auth failed: {0}")]
    Unauthorized(String),
    #[error("model not supported by this provider: {0}")]
    UnsupportedModel(String),
    #[error("response parse failure: {0}")]
    Parse(String),
    #[error("transport: {0}")]
    Transport(#[from] reqwest::Error),
    #[error("other: {0}")]
    Other(String),
}

#[async_trait]
pub trait LlmProvider: Send + Sync {
    /// Stable identifier used in URLs and the `provider` column.
    fn name(&self) -> &'static str;
    /// Models this provider understands. Used for client-side validation.
    fn supported_models(&self) -> &[&'static str];
    /// Single-shot completion.
    async fn complete(&self, req: CompletionRequest) -> Result<CompletionResponse, LlmError>;
    /// Streaming completion.
    async fn stream<'a>(
        &'a self,
        req: CompletionRequest,
    ) -> Result<BoxStream<'a, Result<TokenChunk, LlmError>>, LlmError>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn response_format_default_is_free() {
        let f: ResponseFormat = Default::default();
        assert!(matches!(f, ResponseFormat::Free));
    }

    #[test]
    fn completion_request_round_trips_json() {
        let req = CompletionRequest {
            model: "claude-sonnet-4-6".into(),
            system_prompt: "you are helpful".into(),
            user_prompt: "hello".into(),
            max_tokens: 512,
            temperature: 0.0,
            stop_sequences: vec![],
            response_format: ResponseFormat::Free,
        };
        let json = serde_json::to_string(&req).unwrap();
        let back: CompletionRequest = serde_json::from_str(&json).unwrap();
        assert_eq!(back.model, req.model);
        assert_eq!(back.max_tokens, req.max_tokens);
    }
}
```

- [ ] **Step 6: Verify crate compiles**

```bash
cd engine && cargo check -p nasrudin-llm 2>&1 | tail -10
```

Expected: lib.rs's re-exports for not-yet-defined items will fail. Comment out the non-`provider` re-exports temporarily by changing `pub use anthropic::…` etc. to `// pub use anthropic::…` until the corresponding tasks are done.

- [ ] **Step 7: Run provider tests**

```bash
cd engine && cargo test -p nasrudin-llm provider 2>&1 | tail -10
```

Expected: 2 pass.

- [ ] **Step 8: Commit**

```bash
git add engine/Cargo.toml engine/Cargo.lock engine/crates/llm/
git commit -m "$(cat <<'EOF'
chore(llm): add nasrudin-llm crate skeleton + provider trait

LlmProvider trait (async, complete + stream), CompletionRequest /
CompletionResponse / LlmError types, ResponseFormat (Free | Json).
Stub files for the three provider impls + encryption + registry,
filled in by subsequent tasks.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: AES-256-GCM encryption helpers

**Files:**
- Modify: `engine/crates/llm/src/encryption.rs`

- [ ] **Step 1: Write the failing tests**

Replace `engine/crates/llm/src/encryption.rs` with:

```rust
//! AES-256-GCM helpers for encrypting BYO API keys at rest.
//!
//! Wire format: `[12-byte nonce][ciphertext + 16-byte auth tag]`.
//! Key: 32 bytes from `NASRUDIN_KEY_ENCRYPT` (base64-encoded in env).

use aes_gcm::aead::{Aead, KeyInit};
use aes_gcm::{Aes256Gcm, Key, Nonce};
use anyhow::{Context, Result};
use rand_core::{OsRng, RngCore};

/// Wire-format ciphertext + nonce.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncryptedKey(pub Vec<u8>);

const NONCE_LEN: usize = 12;

pub fn encrypt(plaintext: &str, key_bytes: &[u8; 32]) -> Result<EncryptedKey> {
    let key: &Key<Aes256Gcm> = key_bytes.into();
    let cipher = Aes256Gcm::new(key);
    let mut nonce = [0u8; NONCE_LEN];
    OsRng.fill_bytes(&mut nonce);
    let ct = cipher
        .encrypt(Nonce::from_slice(&nonce), plaintext.as_bytes())
        .map_err(|e| anyhow::anyhow!("aes-gcm encrypt: {e}"))?;
    let mut out = Vec::with_capacity(NONCE_LEN + ct.len());
    out.extend_from_slice(&nonce);
    out.extend_from_slice(&ct);
    Ok(EncryptedKey(out))
}

pub fn decrypt(encrypted: &EncryptedKey, key_bytes: &[u8; 32]) -> Result<String> {
    if encrypted.0.len() < NONCE_LEN {
        anyhow::bail!("encrypted key too short");
    }
    let key: &Key<Aes256Gcm> = key_bytes.into();
    let cipher = Aes256Gcm::new(key);
    let (nonce, ct) = encrypted.0.split_at(NONCE_LEN);
    let pt = cipher
        .decrypt(Nonce::from_slice(nonce), ct)
        .map_err(|e| anyhow::anyhow!("aes-gcm decrypt: {e}"))?;
    String::from_utf8(pt).context("decrypted bytes are not utf-8")
}

/// Last 4 chars of the plaintext key, for UI display. Truncates safely
/// for short keys.
pub fn key_hint(plaintext: &str) -> String {
    let n = plaintext.chars().count();
    if n <= 4 {
        plaintext.to_string()
    } else {
        plaintext.chars().skip(n - 4).collect()
    }
}

/// Decode a base64-encoded 32-byte key from the env var. Returns None
/// when the var is unset or invalid; callers gate the endpoints
/// accordingly.
pub fn load_encrypt_key_from_env() -> Option<[u8; 32]> {
    use base64::Engine;
    let raw = std::env::var("NASRUDIN_KEY_ENCRYPT").ok()?;
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return None;
    }
    let decoded = base64::engine::general_purpose::STANDARD
        .decode(trimmed)
        .ok()?;
    if decoded.len() != 32 {
        tracing::warn!(
            "NASRUDIN_KEY_ENCRYPT decoded to {} bytes; expected 32",
            decoded.len()
        );
        return None;
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&decoded);
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn k() -> [u8; 32] {
        [7u8; 32]
    }

    #[test]
    fn round_trip_roundtrips() {
        let pt = "sk-ant-api03-1234567890abcdef".to_string();
        let enc = encrypt(&pt, &k()).unwrap();
        let dec = decrypt(&enc, &k()).unwrap();
        assert_eq!(dec, pt);
    }

    #[test]
    fn different_nonces_yield_different_ciphertexts() {
        let pt = "same-input";
        let a = encrypt(pt, &k()).unwrap();
        let b = encrypt(pt, &k()).unwrap();
        assert_ne!(a, b, "fresh nonce per call ⇒ different ciphertext");
    }

    #[test]
    fn wrong_key_fails_decryption() {
        let pt = "secret";
        let enc = encrypt(pt, &k()).unwrap();
        let mut wrong = k();
        wrong[0] ^= 0xff;
        assert!(decrypt(&enc, &wrong).is_err());
    }

    #[test]
    fn truncated_ciphertext_fails_decryption() {
        let enc = encrypt("hello", &k()).unwrap();
        let truncated = EncryptedKey(enc.0[..8].to_vec());
        assert!(decrypt(&truncated, &k()).is_err());
    }

    #[test]
    fn key_hint_returns_last_4_chars() {
        assert_eq!(key_hint("sk-ant-api03-1234"), "1234");
        assert_eq!(key_hint("ab"), "ab");
        assert_eq!(key_hint(""), "");
    }
}
```

- [ ] **Step 2: Run tests, verify pass**

```bash
cd engine && cargo test -p nasrudin-llm encryption:: 2>&1 | tail -10
```

Expected: 5 pass.

- [ ] **Step 3: Re-enable encryption re-exports in `lib.rs`**

Uncomment the `pub use encryption::…` line if you commented it out earlier. The other provider re-exports stay commented until their tasks land.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/llm/src/encryption.rs engine/crates/llm/src/lib.rs
git commit -m "$(cat <<'EOF'
feat(llm): AES-256-GCM key encryption helpers

12-byte random nonce prepended to ciphertext+tag. 32-byte server key
loaded once at boot from NASRUDIN_KEY_ENCRYPT (base64). key_hint
returns the last 4 plaintext chars for UI display.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: Anthropic provider

**Files:**
- Modify: `engine/crates/llm/src/anthropic.rs`
- Create: `engine/crates/llm/tests/integration_anthropic_mock.rs`

- [ ] **Step 1: Implement the provider**

Replace `engine/crates/llm/src/anthropic.rs` with:

```rust
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
        _req: CompletionRequest,
    ) -> Result<BoxStream<'a, Result<TokenChunk, LlmError>>, LlmError> {
        // Stream impl deferred to Phase F (paper draft); single-shot
        // is enough for the conjecture LLM call. Returning a stream
        // with a single Other variant keeps the trait honest.
        Err(LlmError::Other("stream not implemented for Anthropic in Phase C".into()))
    }
}
```

- [ ] **Step 2: Re-enable the re-export in lib.rs**

Uncomment `pub use anthropic::AnthropicProvider;` in `lib.rs`.

- [ ] **Step 3: Write the wiremock integration test**

Create `engine/crates/llm/tests/integration_anthropic_mock.rs`:

```rust
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
    assert!(matches!(
        err,
        nasrudin_llm::LlmError::UnsupportedModel(_)
    ));
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
```

- [ ] **Step 4: Run the test**

```bash
cd engine && cargo test -p nasrudin-llm --test integration_anthropic_mock 2>&1 | tail -10
```

Expected: 3 pass.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/llm/src/anthropic.rs engine/crates/llm/src/lib.rs engine/crates/llm/tests/integration_anthropic_mock.rs
git commit -m "$(cat <<'EOF'
feat(llm): AnthropicProvider for the Messages API

Sonnet 4.6 / Opus 4.7 / Haiku 4.5 supported. complete() round-trips
through /v1/messages; stream() left as a Phase F follow-up. Errors
normalised to LlmError::{Unauthorized, RateLimited, Http, Parse,
UnsupportedModel}. Wiremock-backed integration test covers happy
path + 429 + unsupported-model short-circuit.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: OpenAI provider

**Files:**
- Modify: `engine/crates/llm/src/openai.rs`
- Create: `engine/crates/llm/tests/integration_openai_mock.rs`

- [ ] **Step 1: Implement the provider**

Replace `engine/crates/llm/src/openai.rs` with:

```rust
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
        Err(LlmError::Other("stream not implemented for OpenAI in Phase C".into()))
    }
}
```

- [ ] **Step 2: Re-enable the re-export**

Uncomment `pub use openai::OpenAiProvider;` in `lib.rs`.

- [ ] **Step 3: Write the wiremock test**

Create `engine/crates/llm/tests/integration_openai_mock.rs`:

```rust
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
```

- [ ] **Step 4: Run the test**

```bash
cd engine && cargo test -p nasrudin-llm --test integration_openai_mock 2>&1 | tail -10
```

Expected: 2 pass.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/llm/src/openai.rs engine/crates/llm/src/lib.rs engine/crates/llm/tests/integration_openai_mock.rs
git commit -m "$(cat <<'EOF'
feat(llm): OpenAiProvider for Chat Completions

GPT-4o / 4o-mini / o1 / o1-mini supported. response_format: Json
maps to OpenAI's {type: json_object}. Wiremock test covers happy
path + 401 → Unauthorized.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Ollama provider

**Files:**
- Modify: `engine/crates/llm/src/ollama.rs`
- Create: `engine/crates/llm/tests/integration_ollama_mock.rs`

- [ ] **Step 1: Implement the provider**

Replace `engine/crates/llm/src/ollama.rs` with:

```rust
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
        Err(LlmError::Other("stream not implemented for Ollama in Phase C".into()))
    }
}
```

- [ ] **Step 2: Re-enable the re-export**

Uncomment `pub use ollama::OllamaProvider;` in `lib.rs`.

- [ ] **Step 3: Write the wiremock test**

Create `engine/crates/llm/tests/integration_ollama_mock.rs`:

```rust
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
```

- [ ] **Step 4: Run the test**

```bash
cd engine && cargo test -p nasrudin-llm --test integration_ollama_mock 2>&1 | tail -10
```

Expected: 2 pass.

- [ ] **Step 5: Commit**

```bash
git add engine/crates/llm/src/ollama.rs engine/crates/llm/src/lib.rs engine/crates/llm/tests/integration_ollama_mock.rs
git commit -m "$(cat <<'EOF'
feat(llm): OllamaProvider for localhost:11434

No static model whitelist (any locally-pulled model works). API key
optional and ignored. ResponseFormat::Json maps to Ollama's
format=json. Wiremock test covers happy path + 500.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: Provider registry

**Files:**
- Modify: `engine/crates/llm/src/registry.rs`

- [ ] **Step 1: Write the failing test**

Replace `engine/crates/llm/src/registry.rs` with:

```rust
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
                let key = api_key.ok_or_else(|| {
                    LlmError::Unauthorized("openai requires an api key".into())
                })?;
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
```

- [ ] **Step 2: Re-enable the re-export**

Uncomment `pub use registry::Registry;` in `lib.rs`.

- [ ] **Step 3: Run tests**

```bash
cd engine && cargo test -p nasrudin-llm registry:: 2>&1 | tail -10
```

Expected: 3 pass.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/llm/src/registry.rs engine/crates/llm/src/lib.rs
git commit -m "$(cat <<'EOF'
feat(llm): string-keyed Registry::complete dispatcher

Centralises the three provider impls behind one entry point so the
handler doesn't have to match on provider names itself. Anthropic
and OpenAI require an api_key; Ollama doesn't (key parameter is
ignored when provider == "ollama").

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Postgres migration for `user_llm_keys`

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260710_000006_user_llm_keys.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Write the migration**

Create `engine/crates/pg/src/migrator/m20260710_000006_user_llm_keys.rs`:

```rust
use sea_orm_migration::{prelude::*, schema::*};

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(UserLlmKeys::Table)
                    .if_not_exists()
                    .col(uuid(UserLlmKeys::UserId).not_null())
                    .col(string(UserLlmKeys::Provider).not_null())
                    .col(blob(UserLlmKeys::EncryptedKey).not_null())
                    .col(string(UserLlmKeys::KeyHint).not_null())
                    .col(
                        timestamp_with_time_zone(UserLlmKeys::CreatedAt)
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(timestamp_with_time_zone_null(UserLlmKeys::LastUsedAt))
                    .primary_key(
                        Index::create()
                            .col(UserLlmKeys::UserId)
                            .col(UserLlmKeys::Provider),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_user_llm_keys_user_id")
                            .from(UserLlmKeys::Table, UserLlmKeys::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;

        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(UserLlmKeys::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum UserLlmKeys {
    Table,
    UserId,
    Provider,
    EncryptedKey,
    KeyHint,
    CreatedAt,
    LastUsedAt,
}

#[derive(DeriveIden)]
enum Users {
    Table,
    Id,
}
```

- [ ] **Step 2: Register the migration**

Edit `engine/crates/pg/src/migrator/mod.rs`:

```rust
mod m20250101_000001_create_tables;
mod m20260428_000002_api_keys;
mod m20260501_000003_theorems;
mod m20260501_000004_workers_extend;
mod m20260601_000005_search_indexes;
mod m20260710_000006_user_llm_keys;

pub struct Migrator;

#[async_trait::async_trait]
impl MigratorTrait for Migrator {
    fn migrations() -> Vec<Box<dyn MigrationTrait>> {
        vec![
            Box::new(m20250101_000001_create_tables::Migration),
            Box::new(m20260428_000002_api_keys::Migration),
            Box::new(m20260501_000003_theorems::Migration),
            Box::new(m20260501_000004_workers_extend::Migration),
            Box::new(m20260601_000005_search_indexes::Migration),
            Box::new(m20260710_000006_user_llm_keys::Migration),
        ]
    }
}
```

(Keep the existing `use sea_orm_migration::prelude::*;` line at the top.)

- [ ] **Step 3: Verify compiles**

```bash
cd engine && cargo check -p nasrudin-pg 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 4: Commit**

```bash
git add engine/crates/pg/src/migrator/m20260710_000006_user_llm_keys.rs engine/crates/pg/src/migrator/mod.rs
git commit -m "$(cat <<'EOF'
feat(pg): migration for user_llm_keys

Composite primary key (user_id, provider). encrypted_key is BYTEA
(AES-256-GCM ciphertext + 12-byte nonce). key_hint is the last 4
chars of plaintext for UI display. ON DELETE CASCADE so deleting a
user removes their keys.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8: SeaORM entity + query helpers

**Files:**
- Create: `engine/crates/pg/src/entity/user_llm_keys.rs`
- Create: `engine/crates/pg/src/query/user_llm_keys.rs`
- Modify: `engine/crates/pg/src/entity/mod.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`

- [ ] **Step 1: Write the entity**

Create `engine/crates/pg/src/entity/user_llm_keys.rs`:

```rust
use chrono::{DateTime, Utc};
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
#[sea_orm(table_name = "user_llm_keys")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub user_id: Uuid,
    #[sea_orm(primary_key, auto_increment = false)]
    pub provider: String,
    pub encrypted_key: Vec<u8>,
    pub key_hint: String,
    pub created_at: DateTime<Utc>,
    pub last_used_at: Option<DateTime<Utc>>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 2: Re-export the entity**

Edit `engine/crates/pg/src/entity/mod.rs` and add a `pub mod user_llm_keys;` line in the same style as the existing entries.

- [ ] **Step 3: Write the query helpers**

Create `engine/crates/pg/src/query/user_llm_keys.rs`:

```rust
//! CRUD on `user_llm_keys`. The encryption layer (`nasrudin_llm::encryption`)
//! is applied at the handler boundary; this module sees only the
//! ciphertext + hint.

use chrono::Utc;
use sea_orm::prelude::*;
use sea_orm::{ActiveValue, DatabaseConnection, DbErr, EntityTrait};
use uuid::Uuid;

use crate::entity::user_llm_keys::{ActiveModel, Column, Entity, Model};

/// Public-safe summary returned to the UI. Carries the hint, never
/// the ciphertext.
#[derive(Debug, Clone)]
pub struct LlmKeySummary {
    pub provider: String,
    pub key_hint: String,
    pub created_at: chrono::DateTime<Utc>,
    pub last_used_at: Option<chrono::DateTime<Utc>>,
}

impl From<Model> for LlmKeySummary {
    fn from(m: Model) -> Self {
        Self {
            provider: m.provider,
            key_hint: m.key_hint,
            created_at: m.created_at,
            last_used_at: m.last_used_at,
        }
    }
}

pub async fn list_for_user(
    db: &DatabaseConnection,
    user_id: Uuid,
) -> Result<Vec<LlmKeySummary>, DbErr> {
    let rows = Entity::find()
        .filter(Column::UserId.eq(user_id))
        .all(db)
        .await?;
    Ok(rows.into_iter().map(LlmKeySummary::from).collect())
}

/// Insert-or-update (the composite PK is `(user_id, provider)`).
pub async fn upsert(
    db: &DatabaseConnection,
    user_id: Uuid,
    provider: String,
    encrypted_key: Vec<u8>,
    key_hint: String,
) -> Result<(), DbErr> {
    let am = ActiveModel {
        user_id: ActiveValue::Set(user_id),
        provider: ActiveValue::Set(provider.clone()),
        encrypted_key: ActiveValue::Set(encrypted_key),
        key_hint: ActiveValue::Set(key_hint),
        created_at: ActiveValue::Set(Utc::now()),
        last_used_at: ActiveValue::NotSet,
    };
    Entity::insert(am)
        .on_conflict(
            sea_orm::sea_query::OnConflict::columns([Column::UserId, Column::Provider])
                .update_columns([Column::EncryptedKey, Column::KeyHint, Column::CreatedAt])
                .to_owned(),
        )
        .exec(db)
        .await?;
    Ok(())
}

/// Returns the ciphertext for the (user_id, provider) row, or None.
/// The caller decrypts with the server's key. Internal API: never
/// expose ciphertext over the wire.
pub async fn get_ciphertext(
    db: &DatabaseConnection,
    user_id: Uuid,
    provider: &str,
) -> Result<Option<Vec<u8>>, DbErr> {
    let row = Entity::find_by_id((user_id, provider.to_string()))
        .one(db)
        .await?;
    Ok(row.map(|m| m.encrypted_key))
}

pub async fn delete(
    db: &DatabaseConnection,
    user_id: Uuid,
    provider: &str,
) -> Result<u64, DbErr> {
    let res = Entity::delete_by_id((user_id, provider.to_string()))
        .exec(db)
        .await?;
    Ok(res.rows_affected)
}

pub async fn touch_last_used(
    db: &DatabaseConnection,
    user_id: Uuid,
    provider: &str,
) -> Result<(), DbErr> {
    let am = ActiveModel {
        user_id: ActiveValue::Set(user_id),
        provider: ActiveValue::Set(provider.to_string()),
        last_used_at: ActiveValue::Set(Some(Utc::now())),
        ..Default::default()
    };
    let _ = Entity::update(am).exec(db).await?;
    Ok(())
}
```

- [ ] **Step 4: Re-export the query module**

Edit `engine/crates/pg/src/query/mod.rs` and add `pub mod user_llm_keys;`.

- [ ] **Step 5: Verify compiles**

```bash
cd engine && cargo check -p nasrudin-pg 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 6: Commit**

```bash
git add engine/crates/pg/src/entity/user_llm_keys.rs engine/crates/pg/src/entity/mod.rs engine/crates/pg/src/query/user_llm_keys.rs engine/crates/pg/src/query/mod.rs
git commit -m "$(cat <<'EOF'
feat(pg): SeaORM entity + CRUD for user_llm_keys

list_for_user returns hint-only LlmKeySummary (never ciphertext).
upsert handles the (user_id, provider) primary key collision case.
get_ciphertext is internal-only — handler decrypts with the server
key, never returns it over the wire.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: API handlers `/api/me/llm-keys`

**Files:**
- Create: `engine/crates/api/src/handlers/llm_keys.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs`
- Modify: `engine/crates/api/src/state.rs`
- Modify: `engine/crates/api/src/main.rs`
- Modify: `engine/crates/api/Cargo.toml`
- Modify: `engine/crates/api/tests/test_app/mod.rs`

- [ ] **Step 1: Add `nasrudin-llm` dep**

In `engine/crates/api/Cargo.toml`, under `[dependencies]`, add:

```toml
nasrudin-llm = { path = "../llm" }
```

- [ ] **Step 2: Add `llm_encrypt_key` to AppState**

Edit `engine/crates/api/src/state.rs`. Add to the imports:

```rust
// (no new import needed; `[u8; 32]` is std)
```

Add to the `AppState` struct (just before the closing `}`):

```rust
    /// 32-byte AES-256-GCM key, decoded once at boot from
    /// `NASRUDIN_KEY_ENCRYPT` (base64). When `None`, the
    /// `/api/me/llm-keys` endpoints all return 503 with
    /// `key_encrypt_unset` — production deployments must set this.
    pub llm_encrypt_key: Option<[u8; 32]>,
```

- [ ] **Step 3: Decode the key in `main.rs` and pass into AppState**

Edit `engine/crates/api/src/main.rs`. After the `embed` block (Phase B Task 11), add:

```rust
    let llm_encrypt_key = nasrudin_llm::encryption::load_encrypt_key_from_env();
    if llm_encrypt_key.is_some() {
        tracing::info!("NASRUDIN_KEY_ENCRYPT configured — /api/me/llm-keys enabled");
    } else {
        tracing::warn!("NASRUDIN_KEY_ENCRYPT unset — /api/me/llm-keys returns 503");
    }
```

In the `AppState { … }` literal, add:

```rust
        llm_encrypt_key,
```

In the test_app/mod.rs `AppState { … }` literal, add:

```rust
        llm_encrypt_key: Some([7u8; 32]),
```

- [ ] **Step 4: Write the handlers**

Create `engine/crates/api/src/handlers/llm_keys.rs`:

```rust
//! BYO LLM key vault: `GET`/`POST`/`DELETE` `/api/me/llm-keys`.

use std::sync::Arc;

use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use axum_login::AuthSession;
use nasrudin_llm::{encryption, Registry};
use nasrudin_pg::query::user_llm_keys as keys_q;
use serde::{Deserialize, Serialize};

use crate::auth::Backend;
use crate::state::AppState;

#[derive(Serialize)]
pub struct KeySummaryDto {
    pub provider: String,
    pub key_hint: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub last_used_at: Option<chrono::DateTime<chrono::Utc>>,
}

#[derive(Deserialize)]
pub struct SetKeyBody {
    pub provider: String,
    pub key: String,
}

#[derive(Serialize)]
pub struct ListResponse {
    pub keys: Vec<KeySummaryDto>,
    pub known_providers: Vec<&'static str>,
}

pub async fn list(
    State(state): State<Arc<AppState>>,
    auth_sess: AuthSession<Backend>,
) -> Response {
    let user = match auth_sess.user.as_ref() {
        Some(u) => u,
        None => return (StatusCode::UNAUTHORIZED, "not signed in").into_response(),
    };
    if state.llm_encrypt_key.is_none() {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({"error": "key_encrypt_unset"})),
        )
            .into_response();
    }
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({"error": "pg_unavailable"})),
            )
                .into_response();
        }
    };
    match keys_q::list_for_user(pg, user.id).await {
        Ok(rows) => {
            let dto: Vec<KeySummaryDto> = rows
                .into_iter()
                .map(|s| KeySummaryDto {
                    provider: s.provider,
                    key_hint: s.key_hint,
                    created_at: s.created_at,
                    last_used_at: s.last_used_at,
                })
                .collect();
            Json(ListResponse {
                keys: dto,
                known_providers: Registry::known_providers().to_vec(),
            })
            .into_response()
        }
        Err(e) => {
            tracing::warn!("list llm keys failed: {e}");
            (StatusCode::INTERNAL_SERVER_ERROR, "db error").into_response()
        }
    }
}

pub async fn set_key(
    State(state): State<Arc<AppState>>,
    auth_sess: AuthSession<Backend>,
    Json(body): Json<SetKeyBody>,
) -> Response {
    let user = match auth_sess.user.as_ref() {
        Some(u) => u,
        None => return (StatusCode::UNAUTHORIZED, "not signed in").into_response(),
    };
    let key_bytes = match state.llm_encrypt_key.as_ref() {
        Some(k) => k,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({"error": "key_encrypt_unset"})),
            )
                .into_response();
        }
    };
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({"error": "pg_unavailable"})),
            )
                .into_response();
        }
    };
    if !Registry::known_providers().contains(&body.provider.as_str()) {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({
                "error": "unknown_provider",
                "known": Registry::known_providers()
            })),
        )
            .into_response();
    }
    if body.key.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({"error": "empty_key"})),
        )
            .into_response();
    }
    let encrypted = match encryption::encrypt(&body.key, key_bytes) {
        Ok(e) => e,
        Err(e) => {
            tracing::warn!("encrypt failed: {e}");
            return (StatusCode::INTERNAL_SERVER_ERROR, "encrypt failed").into_response();
        }
    };
    let hint = encryption::key_hint(&body.key);
    if let Err(e) = keys_q::upsert(pg, user.id, body.provider.clone(), encrypted.0, hint.clone())
        .await
    {
        tracing::warn!("upsert llm key failed: {e}");
        return (StatusCode::INTERNAL_SERVER_ERROR, "db error").into_response();
    }
    Json(serde_json::json!({
        "provider": body.provider,
        "key_hint": hint,
    }))
    .into_response()
}

pub async fn revoke(
    State(state): State<Arc<AppState>>,
    auth_sess: AuthSession<Backend>,
    Path(provider): Path<String>,
) -> Response {
    let user = match auth_sess.user.as_ref() {
        Some(u) => u,
        None => return (StatusCode::UNAUTHORIZED, "not signed in").into_response(),
    };
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({"error": "pg_unavailable"})),
            )
                .into_response();
        }
    };
    match keys_q::delete(pg, user.id, &provider).await {
        Ok(0) => (StatusCode::NOT_FOUND, "no such key").into_response(),
        Ok(_) => (StatusCode::NO_CONTENT, "").into_response(),
        Err(e) => {
            tracing::warn!("delete llm key failed: {e}");
            (StatusCode::INTERNAL_SERVER_ERROR, "db error").into_response()
        }
    }
}
```

- [ ] **Step 5: Register the module**

Edit `engine/crates/api/src/handlers/mod.rs` and add `pub mod llm_keys;`.

- [ ] **Step 6: Wire the routes**

Edit `engine/crates/api/src/main.rs`. Find the `let api = Router::new()` block and add three new routes:

```rust
        .route("/api/me/llm-keys", get(handlers::llm_keys::list))
        .route("/api/me/llm-keys", post(handlers::llm_keys::set_key))
        .route(
            "/api/me/llm-keys/:provider",
            delete(handlers::llm_keys::revoke),
        )
```

(Make sure `delete` is imported from `axum::routing` — search for `use axum::routing::{` and add `delete` to the list if missing.)

- [ ] **Step 7: Verify compiles**

```bash
cd engine && cargo check --workspace 2>&1 | tail -10
```

Expected: clean.

- [ ] **Step 8: Commit**

```bash
git add engine/crates/api/src/handlers/llm_keys.rs engine/crates/api/src/handlers/mod.rs engine/crates/api/src/state.rs engine/crates/api/src/main.rs engine/crates/api/Cargo.toml engine/crates/api/tests/test_app/mod.rs engine/Cargo.lock
git commit -m "$(cat <<'EOF'
feat(api): /api/me/llm-keys CRUD endpoints

list / set_key / revoke. Encryption applied at the handler boundary
using AppState.llm_encrypt_key (loaded once at boot from
NASRUDIN_KEY_ENCRYPT). Returns 503 when the env var is unset, 400
on unknown provider, 401 on no auth, 404 on revoke-missing.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 10: API integration test for the key vault

**Files:**
- Create: `engine/crates/api/tests/llm_keys_handler.rs`

- [ ] **Step 1: Write the test**

Create `engine/crates/api/tests/llm_keys_handler.rs`:

```rust
//! End-to-end: sign in → POST a key → list → revoke. Confirms the
//! ciphertext never appears in the response, the hint appears, and
//! the row vanishes after revoke.

mod test_app;

use axum_test::TestServer;
use serde_json::json;

#[tokio::test]
async fn full_lifecycle_round_trips() {
    let app = test_app::test_app().await;
    let server = TestServer::new(app).unwrap();
    let user = test_app::sign_up_and_in(&server, "kv@example.org", "passw0rd!1").await;

    let post = server
        .post("/api/me/llm-keys")
        .add_cookie(user.cookie.clone())
        .json(&json!({
            "provider": "anthropic",
            "key": "sk-ant-api03-1234567890abcdef"
        }))
        .await;
    post.assert_status_ok();
    let body = post.json::<serde_json::Value>();
    assert_eq!(body["provider"], "anthropic");
    assert_eq!(body["key_hint"], "cdef");
    assert!(body.get("key").is_none(), "plaintext key must not echo");

    let list = server
        .get("/api/me/llm-keys")
        .add_cookie(user.cookie.clone())
        .await;
    list.assert_status_ok();
    let lj = list.json::<serde_json::Value>();
    assert_eq!(lj["keys"].as_array().map(|a| a.len()), Some(1));
    assert_eq!(lj["keys"][0]["provider"], "anthropic");
    assert_eq!(lj["keys"][0]["key_hint"], "cdef");
    assert!(
        lj["keys"][0].get("encrypted_key").is_none(),
        "ciphertext must not leak"
    );

    let del = server
        .delete("/api/me/llm-keys/anthropic")
        .add_cookie(user.cookie.clone())
        .await;
    del.assert_status(axum::http::StatusCode::NO_CONTENT);

    let list2 = server
        .get("/api/me/llm-keys")
        .add_cookie(user.cookie)
        .await;
    let lj2 = list2.json::<serde_json::Value>();
    assert_eq!(lj2["keys"].as_array().map(|a| a.len()), Some(0));
}

#[tokio::test]
async fn unknown_provider_rejected() {
    let app = test_app::test_app().await;
    let server = TestServer::new(app).unwrap();
    let user = test_app::sign_up_and_in(&server, "kv2@example.org", "passw0rd!1").await;

    let post = server
        .post("/api/me/llm-keys")
        .add_cookie(user.cookie)
        .json(&json!({"provider": "bogus", "key": "anything"}))
        .await;
    post.assert_status_bad_request();
}

#[tokio::test]
async fn unauthenticated_rejected() {
    let app = test_app::test_app().await;
    let server = TestServer::new(app).unwrap();
    let resp = server.get("/api/me/llm-keys").await;
    resp.assert_status_unauthorized();
}
```

(If `test_app::sign_up_and_in` doesn't already exist, mirror the helper used in `me_stats.rs`. Search:)

```bash
grep -n "sign_up_and_in\|pub async fn sign_up" /Volumes/CORSAIR/code/personal/nasrudin/engine/crates/api/tests/test_app/mod.rs
```

If absent, copy the equivalent helper from any existing handler test.

- [ ] **Step 2: Run the test**

```bash
cd engine && cargo test -p physics-api --test llm_keys_handler 2>&1 | tail -10
```

Expected: 3 pass.

- [ ] **Step 3: Commit**

```bash
git add engine/crates/api/tests/llm_keys_handler.rs
git commit -m "$(cat <<'EOF'
test(api): /api/me/llm-keys lifecycle integration test

POST → list → DELETE → list, plus unknown-provider and unauthenticated
short-circuits. Confirms ciphertext never echoes back over the wire.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11: Frontend Settings card + queries

**Files:**
- Modify: `nasrudin-frontend/src/lib/types.ts`
- Modify: `nasrudin-frontend/src/lib/queries.ts`
- Create: `nasrudin-frontend/src/components/settings/LlmKeysSection.tsx`
- Create: `nasrudin-frontend/src/components/settings/AddKeyModal.tsx`
- Modify: `nasrudin-frontend/src/routes/settings.tsx`

- [ ] **Step 1: Add types**

In `nasrudin-frontend/src/lib/types.ts`, append:

```ts
export type LlmProviderName = 'anthropic' | 'openai' | 'ollama';

export interface LlmKeySummary {
  provider: LlmProviderName | string;
  key_hint: string;
  created_at: string;
  last_used_at: string | null;
}

export interface LlmKeysListResponse {
  keys: LlmKeySummary[];
  known_providers: string[];
}
```

- [ ] **Step 2: Add hooks**

In `nasrudin-frontend/src/lib/queries.ts`, find the location near other `useMe…` hooks and append:

```ts
export function useLlmKeys() {
  return useQuery<LlmKeysListResponse>({
    queryKey: ['llm-keys'],
    queryFn: async () => {
      const r = await fetch(`${API_URL}/api/me/llm-keys`, { credentials: 'include' });
      if (!r.ok) throw new Error(`llm-keys fetch ${r.status}`);
      return r.json();
    },
  });
}

export function useSetLlmKey() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async (body: { provider: string; key: string }) => {
      const r = await fetch(`${API_URL}/api/me/llm-keys`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        credentials: 'include',
        body: JSON.stringify(body),
      });
      if (!r.ok) {
        const txt = await r.text();
        throw new Error(`set-llm-key ${r.status}: ${txt}`);
      }
      return r.json();
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: ['llm-keys'] }),
  });
}

export function useRevokeLlmKey() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async (provider: string) => {
      const r = await fetch(`${API_URL}/api/me/llm-keys/${provider}`, {
        method: 'DELETE',
        credentials: 'include',
      });
      if (!r.ok && r.status !== 404) {
        throw new Error(`revoke-llm-key ${r.status}`);
      }
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: ['llm-keys'] }),
  });
}
```

(Add `LlmKeysListResponse` to the imports at the top of the file alongside the other type imports.)

- [ ] **Step 3: Build the modal**

Create `nasrudin-frontend/src/components/settings/AddKeyModal.tsx`:

```tsx
import { useState } from 'react';
import { useSetLlmKey } from '../../lib/queries';

interface Props {
  knownProviders: string[];
  onClose: () => void;
}

export function AddKeyModal({ knownProviders, onClose }: Props) {
  const [provider, setProvider] = useState<string>(knownProviders[0] ?? 'anthropic');
  const [key, setKey] = useState('');
  const [err, setErr] = useState<string | null>(null);
  const set = useSetLlmKey();

  return (
    <div className="modal-backdrop" onClick={onClose}>
      <div className="modal-card" onClick={(e) => e.stopPropagation()}>
        <h3>Add LLM API key</h3>
        <label>
          Provider
          <select value={provider} onChange={(e) => setProvider(e.target.value)}>
            {knownProviders.map((p) => (
              <option key={p} value={p}>
                {p}
              </option>
            ))}
          </select>
        </label>
        <label>
          API key
          <input
            type="password"
            value={key}
            onChange={(e) => setKey(e.target.value)}
            placeholder="sk-…"
            autoFocus
          />
        </label>
        {err && <div className="form-error">{err}</div>}
        <div className="modal-actions">
          <button className="btn-secondary" onClick={onClose}>
            Cancel
          </button>
          <button
            className="btn-primary"
            disabled={key.trim().length === 0 || set.isPending}
            onClick={async () => {
              setErr(null);
              try {
                await set.mutateAsync({ provider, key });
                onClose();
              } catch (e) {
                setErr(String(e));
              }
            }}
          >
            {set.isPending ? 'Saving…' : 'Save'}
          </button>
        </div>
      </div>
    </div>
  );
}
```

- [ ] **Step 4: Build the section**

Create `nasrudin-frontend/src/components/settings/LlmKeysSection.tsx`:

```tsx
import { useState } from 'react';
import { useLlmKeys, useRevokeLlmKey } from '../../lib/queries';
import { AddKeyModal } from './AddKeyModal';

export function LlmKeysSection() {
  const { data, isLoading } = useLlmKeys();
  const revoke = useRevokeLlmKey();
  const [showAdd, setShowAdd] = useState(false);

  if (isLoading) return <div className="card">Loading LLM keys…</div>;
  if (!data) return null;

  const knownProviders = data.known_providers ?? [];
  const keysByProvider = new Map(data.keys.map((k) => [k.provider, k]));

  return (
    <section className="card">
      <header className="card-header">
        <h2>LLM providers</h2>
        <button className="btn-primary" onClick={() => setShowAdd(true)}>
          Add key
        </button>
      </header>
      <ul className="provider-list">
        {knownProviders.map((p) => {
          const row = keysByProvider.get(p);
          return (
            <li key={p} className="provider-row">
              <span className="provider-name">{p}</span>
              {row ? (
                <>
                  <span className="provider-hint">····{row.key_hint}</span>
                  <span className="provider-meta">
                    {row.last_used_at
                      ? `last used ${new Date(row.last_used_at).toLocaleString()}`
                      : 'never used'}
                  </span>
                  <button
                    className="btn-danger-link"
                    onClick={() => revoke.mutate(p)}
                  >
                    Revoke
                  </button>
                </>
              ) : (
                <span className="provider-meta-muted">No key configured</span>
              )}
            </li>
          );
        })}
      </ul>
      {showAdd && (
        <AddKeyModal
          knownProviders={knownProviders}
          onClose={() => setShowAdd(false)}
        />
      )}
    </section>
  );
}
```

- [ ] **Step 5: Mount in settings.tsx**

Edit `nasrudin-frontend/src/routes/settings.tsx`. Find the existing settings sections and add `<LlmKeysSection />` in a sensible place (e.g., between Profile and API keys). Add the import:

```tsx
import { LlmKeysSection } from '../components/settings/LlmKeysSection';
```

- [ ] **Step 6: Type-check**

```bash
cd nasrudin-frontend && pnpm tsc --noEmit 2>&1 | tail -10
```

Expected: clean.

- [ ] **Step 7: Commit**

```bash
git add nasrudin-frontend/src/lib/types.ts nasrudin-frontend/src/lib/queries.ts nasrudin-frontend/src/components/settings/LlmKeysSection.tsx nasrudin-frontend/src/components/settings/AddKeyModal.tsx nasrudin-frontend/src/routes/settings.tsx
git commit -m "$(cat <<'EOF'
feat(frontend): LLM providers section in settings

Lists each known provider; shows key_hint + last-used when set,
"No key configured" otherwise. Add-key modal validates provider via
the dropdown (populated from /api/me/llm-keys.known_providers) and
posts the plaintext over HTTPS — server encrypts before persisting.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12: LLM_LAYER.md operator docs

**Files:**
- Create: `engine/crates/llm/LLM_LAYER.md`

- [ ] **Step 1: Write the doc**

Create `engine/crates/llm/LLM_LAYER.md`:

```markdown
# LLM Router (Phase C)

`nasrudin-llm` is the BYO LLM router: provider-agnostic completion
+ AES-256-GCM key vault. Phase C ships the router + the key endpoints;
Phase D wires the conjecture loop on top.

## Pieces

| Component | Responsibility |
|---|---|
| `LlmProvider` (`provider.rs`) | Async trait: `name`, `supported_models`, `complete`, `stream` |
| `AnthropicProvider` (`anthropic.rs`) | Messages API; Sonnet 4.6 / Opus 4.7 / Haiku 4.5 |
| `OpenAiProvider` (`openai.rs`) | Chat Completions; GPT-4o / 4o-mini / o1 / o1-mini |
| `OllamaProvider` (`ollama.rs`) | localhost:11434; any locally-pulled model |
| `Registry::complete` (`registry.rs`) | String-keyed dispatcher; only public entry-point for handlers |
| `encryption.rs` | AES-256-GCM helpers (`encrypt`, `decrypt`, `key_hint`, `load_encrypt_key_from_env`) |

## Server-side env

```bash
# Generate once, keep secret. 32 random bytes, base64-encoded.
NASRUDIN_KEY_ENCRYPT="$(openssl rand -base64 32)"
```

When unset, `/api/me/llm-keys` returns 503 with `key_encrypt_unset`
on every method.

## Adding a key

```bash
curl -i $API/api/me/llm-keys \
  -H 'content-type: application/json' \
  -b 'session=…' \
  -d '{"provider": "anthropic", "key": "sk-ant-api03-…"}'
```

Response carries `provider` + `key_hint` (last 4 chars of the
plaintext). Plaintext never echoes back from any endpoint.

## Calling a provider

Handlers don't construct providers directly:

```rust
let resp = nasrudin_llm::Registry::complete(
    "anthropic",
    Some(plaintext_key),
    nasrudin_llm::CompletionRequest { /* … */ },
).await?;
```

Internally:

1. `keys_q::get_ciphertext(pg, user_id, provider)` returns the
   blob.
2. `nasrudin_llm::encryption::decrypt(blob, &state.llm_encrypt_key)`
   returns the plaintext.
3. `Registry::complete(provider, Some(plaintext), req)` dispatches.
4. The plaintext drops at the end of the handler future (no global
   stash). On success, fire-and-forget
   `keys_q::touch_last_used(pg, user_id, provider)` for the UI.

## Disabling a provider

Just don't add a key for it. The Settings UI shows "No key
configured" for any known provider with no row in
`user_llm_keys`.

## Testing

CI-safe: every provider has a wiremock-backed test in
`engine/crates/llm/tests/`. No live API keys consumed. Run with:

```bash
cargo test -p nasrudin-llm
```

The `/api/me/llm-keys` integration test
(`engine/crates/api/tests/llm_keys_handler.rs`) covers the full
sign-in → POST → list → DELETE lifecycle and confirms ciphertext
never leaves the database.
```

- [ ] **Step 2: Commit**

```bash
git add engine/crates/llm/LLM_LAYER.md
git commit -m "$(cat <<'EOF'
docs(llm): operator docs for Phase C

Pieces map, NASRUDIN_KEY_ENCRYPT generation, key-add curl recipe,
handler decrypt-dispatch flow, test invocation.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Closing checklist

After all 12 tasks land:

- `cargo check --workspace` exits 0.
- `cargo test --workspace` passes (CI-safe; no live LLM calls).
- `pnpm tsc --noEmit` in `nasrudin-frontend/` is clean.
- `NASRUDIN_KEY_ENCRYPT="$(openssl rand -base64 32)" cargo run --bin physics-api` boots with the log line `NASRUDIN_KEY_ENCRYPT configured — /api/me/llm-keys enabled`.
- `curl $API/api/me/llm-keys` (with cookie) returns `{"keys": [], "known_providers": ["anthropic","openai","ollama"]}`.
- After `POST /api/me/llm-keys` the row exists in `user_llm_keys` with non-empty `encrypted_key` and `key_hint = last-4-chars-of-input`.
- Settings UI's "LLM providers" card lists all three providers; adding/revoking through the modal updates the list without a page reload.

Phase C is done; Phase D (conjecture loop) can now consume `Registry::complete` against decrypted user keys.
