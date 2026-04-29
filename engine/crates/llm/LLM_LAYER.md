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
(`engine/crates/api/tests/llm_keys_handler.rs`) covers the auth-gate
on each verb (full-lifecycle test deferred until the test harness
plumbs session cookies).

## Phase D dependency

Phase D's `/api/conjecture` handler is the first production caller.
The flow is:

```rust
let cipher = keys_q::get_ciphertext(pg, user_id, &req.provider).await?
    .ok_or(LlmError::Other("no_provider_key".into()))?;
let plaintext = encryption::decrypt(
    &EncryptedKey(cipher),
    state.llm_encrypt_key.as_ref().ok_or(...)?,
)?;
let response = Registry::complete(&req.provider, Some(plaintext), llm_req).await?;
let _ = keys_q::touch_last_used(pg, user_id, &req.provider).await;
```

`plaintext` is a stack `String` and goes out of scope when the
function returns.
