//! C FFI declarations for the Lean4 proof verification kernel.
//!
//! These functions are exported by the Lean4 `PhysicsGenerator` library
//! with `@[export]` annotations. The Rust side links against the compiled
//! Lean4 static library + `leanshared` runtime.
//!
//! This module is gated behind the `lean-ffi` feature flag because the
//! Lean4 library must be compiled first via `lake build`.
//!
//! See LEAN4-BRIDGE.md §1 for the full FFI specification.

/// FFI result codes from Lean4.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum FfiResultCode {
    Verified = 0,
    Rejected = 1,
    Timeout = 2,
    ParseError = 3,
}

impl FfiResultCode {
    pub fn from_u32(code: u32) -> Option<Self> {
        match code {
            0 => Some(Self::Verified),
            1 => Some(Self::Rejected),
            2 => Some(Self::Timeout),
            3 => Some(Self::ParseError),
            _ => None,
        }
    }
}

// The actual FFI extern block is only compiled when linking against the
// Lean4 static library.
#[cfg(feature = "lean-ffi")]
mod linked {
    #[link(name = "PhysicsGenerator")]
    #[link(name = "leanshared")]
    extern "C" {
        /// Initialize the Lean4 runtime and load Mathlib + PhysicsGenerator.
        /// Must be called exactly once before any other function.
        /// Returns 0 on success, nonzero on failure.
        pub fn pg_init() -> u32;

        /// Verify a candidate theorem statement.
        ///
        /// * `input` — UTF-8 canonical prefix notation string
        /// * `input_len` — byte length of input
        /// * `output` — buffer for proof bytes (if verified)
        /// * `output_cap` — capacity of output buffer
        /// * `output_len` — out: actual bytes written to output
        ///
        /// Returns: 0=verified, 1=rejected, 2=timeout, 3=parse error
        pub fn pg_verify(
            input: *const u8,
            input_len: usize,
            output: *mut u8,
            output_cap: usize,
            output_len: *mut usize,
        ) -> u32;

        /// Simplify an expression using Lean4 `simp`.
        ///
        /// Input/output buffers follow the same convention as `pg_verify`.
        /// Output contains the simplified canonical form (UTF-8).
        pub fn pg_simplify(
            input: *const u8,
            input_len: usize,
            output: *mut u8,
            output_cap: usize,
            output_len: *mut usize,
        ) -> u32;

        /// Run the `grind` tactic on a goal expression.
        ///
        /// More powerful than `simp` but slower (up to 10s timeout).
        pub fn pg_grind(
            input: *const u8,
            input_len: usize,
            output: *mut u8,
            output_cap: usize,
            output_len: *mut usize,
        ) -> u32;

        /// Shutdown the Lean4 runtime and free resources.
        pub fn pg_shutdown() -> u32;
    }

    /// Lean4 runtime initialization (from lean.h).
    extern "C" {
        pub fn lean_initialize_runtime_module();
    }
}

/// Safe wrapper for FFI calls when the `lean-ffi` feature is enabled.
#[cfg(feature = "lean-ffi")]
pub mod safe {
    use super::{FfiResultCode, linked};
    use crate::VerifyResult;

    /// Output buffer size for proof terms (256 KB).
    const VERIFY_BUFFER_SIZE: usize = 256 * 1024;
    /// Output buffer size for simplified expressions (64 KB).
    const SIMPLIFY_BUFFER_SIZE: usize = 64 * 1024;

    /// Initialize the Lean4 runtime. Call once at startup.
    pub fn init() -> Result<(), String> {
        unsafe {
            linked::lean_initialize_runtime_module();
        }
        let result = unsafe { linked::pg_init() };
        match result {
            0 => Ok(()),
            code => Err(format!("Lean4 pg_init failed with code {code}")),
        }
    }

    /// Verify a canonical expression string via FFI.
    pub fn verify(canonical: &str) -> VerifyResult {
        let input = canonical.as_bytes();
        let mut output = vec![0u8; VERIFY_BUFFER_SIZE];
        let mut output_len: usize = 0;

        let result = unsafe {
            linked::pg_verify(
                input.as_ptr(),
                input.len(),
                output.as_mut_ptr(),
                output.len(),
                &mut output_len,
            )
        };

        match FfiResultCode::from_u32(result) {
            Some(FfiResultCode::Verified) => {
                output.truncate(output_len);
                VerifyResult::Verified {
                    proof_term: output,
                }
            }
            Some(FfiResultCode::Rejected) => VerifyResult::Rejected {
                reason: "All tactics failed".to_string(),
            },
            Some(FfiResultCode::Timeout) => VerifyResult::Timeout,
            Some(FfiResultCode::ParseError) => VerifyResult::ParseError {
                message: "Failed to parse canonical expression in Lean4".to_string(),
            },
            None => VerifyResult::FfiError {
                message: format!("Unknown FFI result code: {result}"),
            },
        }
    }

    /// Simplify an expression via FFI.
    pub fn simplify(canonical: &str) -> Result<String, String> {
        let input = canonical.as_bytes();
        let mut output = vec![0u8; SIMPLIFY_BUFFER_SIZE];
        let mut output_len: usize = 0;

        let result = unsafe {
            linked::pg_simplify(
                input.as_ptr(),
                input.len(),
                output.as_mut_ptr(),
                output.len(),
                &mut output_len,
            )
        };

        match result {
            0 => {
                output.truncate(output_len);
                String::from_utf8(output).map_err(|e| e.to_string())
            }
            code => Err(format!("pg_simplify failed with code {code}")),
        }
    }

    /// Shutdown the Lean4 runtime.
    pub fn shutdown() {
        unsafe {
            linked::pg_shutdown();
        }
    }
}
