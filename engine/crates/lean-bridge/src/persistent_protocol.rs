//! JSON-RPC protocol used to talk to a long-lived `lean --server` subprocess.
//!
//! ## Wire format
//!
//! One JSON object per line on stdin/stdout. The Rust client (Task 10)
//! writes [`Request`] values and reads [`Response`] values; the Lean-side
//! script (`prover/scripts/nasrudin_server.lean`) does the inverse.
//!
//! ## Boot sequence
//!
//! On startup the Lean script imports Mathlib once (~3-8 s) and emits a
//! single `{"kind":"ok","id":0}` line so the Rust client knows the
//! elaborator is warm. After that, requests/responses are correlated by
//! the `id` field — the client picks monotonic ids.
//!
//! ## Lifecycle
//!
//! The client pushes a `Shutdown` request (no id, no response) when
//! dropping the elaborator. On any decode error the Lean side may emit
//! `Fatal { message }` — the client logs and tears down the subprocess.

use serde::{Deserialize, Serialize};

/// A request from the Rust client to the Lean server.
#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Request {
    /// Type-check the given Lean source. Reports any elaboration errors.
    Elaborate { id: u64, source: String },
    /// Verify that `tactic` proves the goal in `source`. Returns success
    /// or first-tactic-error.
    VerifyTactic {
        id: u64,
        source: String,
        tactic: String,
    },
    /// Health check. Server replies with `Pong { id }`.
    Ping { id: u64 },
    /// Tell the server to shut down cleanly. No response.
    Shutdown,
}

/// A response from the Lean server to the Rust client.
#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Response {
    /// Initial boot acknowledgement (`id == 0` by convention) and any
    /// generic `Ok` reply that doesn't carry payload.
    Ok { id: u64 },
    ElaborateOk {
        id: u64,
        elapsed_ms: u32,
    },
    ElaborateError {
        id: u64,
        message: String,
        elapsed_ms: u32,
    },
    VerifyOk {
        id: u64,
        elapsed_ms: u32,
    },
    VerifyError {
        id: u64,
        message: String,
        elapsed_ms: u32,
    },
    Pong {
        id: u64,
    },
    /// Unrecoverable server-side error. Client should kill the subprocess
    /// and either retry on a fresh one or surface the failure.
    Fatal {
        message: String,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn request_elaborate_roundtrip() {
        let r = Request::Elaborate {
            id: 7,
            source: "theorem foo : True := trivial".into(),
        };
        let s = serde_json::to_string(&r).unwrap();
        let back: Request = serde_json::from_str(&s).unwrap();
        assert_eq!(r, back);
    }

    #[test]
    fn request_verify_tactic_roundtrip() {
        let r = Request::VerifyTactic {
            id: 11,
            source: "theorem bar : 1 + 1 = 2 := by".into(),
            tactic: "ring".into(),
        };
        let s = serde_json::to_string(&r).unwrap();
        let back: Request = serde_json::from_str(&s).unwrap();
        assert_eq!(r, back);
    }

    #[test]
    fn request_ping_roundtrip() {
        let r = Request::Ping { id: 1 };
        let s = serde_json::to_string(&r).unwrap();
        let back: Request = serde_json::from_str(&s).unwrap();
        assert_eq!(r, back);
    }

    #[test]
    fn request_shutdown_has_no_id() {
        let r = Request::Shutdown;
        let s = serde_json::to_string(&r).unwrap();
        assert!(!s.contains("id"));
        let back: Request = serde_json::from_str(&s).unwrap();
        assert_eq!(r, back);
    }

    #[test]
    fn response_verify_error_roundtrip() {
        let r = Response::VerifyError {
            id: 3,
            message: "linarith failed".into(),
            elapsed_ms: 250,
        };
        let s = serde_json::to_string(&r).unwrap();
        let back: Response = serde_json::from_str(&s).unwrap();
        assert_eq!(r, back);
    }

    #[test]
    fn response_fatal_has_no_id() {
        let r = Response::Fatal {
            message: "oom".into(),
        };
        let s = serde_json::to_string(&r).unwrap();
        assert!(!s.contains("\"id\""));
        let back: Response = serde_json::from_str(&s).unwrap();
        assert_eq!(r, back);
    }

    #[test]
    fn snake_case_tag_for_verify_tactic() {
        let r = Request::VerifyTactic {
            id: 0,
            source: "".into(),
            tactic: "".into(),
        };
        let s = serde_json::to_string(&r).unwrap();
        assert!(s.contains("\"kind\":\"verify_tactic\""));
    }
}
