# Lean4-Rust Bridge: Technical Specification

## Overview

Lean4 serves as the verification oracle. Rust generates candidates; Lean4 proves
or rejects them. Communication uses two channels:

1. **C FFI** — synchronous, single-theorem verification
2. **Shared Memory Ring Buffer** — high-throughput batch verification

---

## 1. C FFI Bridge

### Lean4 Exports

Lean4 functions are exported with C-linkage using `@[export]`:

```lean
-- PhysicsGenerator/Bridge/FFI.lean

/-- Initialize the Lean4 runtime + load Mathlib environment.
    Must be called exactly once before any other function. -/
@[export pg_init]
def pgInit : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    -- Import Mathlib + PhysLean environments
    let env ← importModules #[
      { module := `Mathlib },
      { module := `PhysicsGenerator.Axioms }
    ] {}
    -- Store in global IORef for subsequent calls
    pgEnvRef.set env
    return 0
  catch e =>
    IO.eprintln s!"Init failed: {e}"
    return 1

/-- Verify a candidate theorem statement.
    Input:  UTF-8 encoded canonical expression string
    Output: 0 = verified, 1 = rejected, 2 = timeout, 3 = parse error
    If verified, proof bytes written to output buffer. -/
@[export pg_verify]
def pgVerify (inputPtr : @& ByteArray) (inputLen : USize)
             (outputPtr : @& ByteArray) (outputCap : USize)
             (outputLen : @& USize) : IO UInt32 := do
  let input := String.fromUTF8! (inputPtr.extract 0 inputLen.toNat)
  -- Parse canonical prefix notation to Lean4 Expr
  let expr ← match ← parseCanonical input with
    | some e => pure e
    | none   => return 3
  -- Try tactics in order of speed
  let tactics := #[
    (`omega,     500),    -- 500ms timeout
    (`norm_num,  500),
    (`ring,      1000),
    (`simp,      2000),
    (`linarith,  2000),
    (`field_simp, 2000),
    (`polyrith,  5000),
    (`grind,     10000),  -- grind is slowest, most powerful
  ]
  for (tac, timeout) in tactics do
    match ← runTacticWithTimeout tac expr timeout with
    | .success proof =>
      let bytes := serializeProof proof
      -- Write to output buffer
      copyToBuffer outputPtr bytes outputLen
      return 0
    | .failure => continue
    | .timeout => continue
  return 1  -- All tactics failed

/-- Simplify an expression using simp with Mathlib lemmas.
    Returns simplified canonical form. -/
@[export pg_simplify]
def pgSimplify (inputPtr : @& ByteArray) (inputLen : USize)
               (outputPtr : @& ByteArray) (outputCap : USize)
               (outputLen : @& USize) : IO UInt32 := do
  let input := String.fromUTF8! (inputPtr.extract 0 inputLen.toNat)
  let expr ← match ← parseCanonical input with
    | some e => pure e
    | none   => return 3
  let simplified ← runSimp expr
  let output := toCanonical simplified
  copyToBuffer outputPtr output.toUTF8 outputLen
  return 0

/-- Run grind tactic on a goal expression.
    More powerful than simp but slower. -/
@[export pg_grind]
def pgGrind (inputPtr : @& ByteArray) (inputLen : USize)
            (outputPtr : @& ByteArray) (outputCap : USize)
            (outputLen : @& USize) : IO UInt32 := do
  let input := String.fromUTF8! (inputPtr.extract 0 inputLen.toNat)
  let expr ← match ← parseCanonical input with
    | some e => pure e
    | none   => return 3
  match ← runGrindWithTimeout expr 10000 with
  | .success proof =>
    copyToBuffer outputPtr (serializeProof proof) outputLen
    return 0
  | .timeout => return 2
  | .failure => return 1

/-- Shutdown and cleanup -/
@[export pg_shutdown]
def pgShutdown : IO UInt32 := do
  pgEnvRef.set default
  return 0
```

### Rust Declarations

```rust
// engine/crates/lean-bridge/src/ffi.rs

use std::ffi::c_void;

#[link(name = "PhysicsGenerator")]  // Links to Lean4 static library
#[link(name = "leanshared")]        // Lean4 runtime
extern "C" {
    fn pg_init() -> u32;
    fn pg_verify(
        input: *const u8, input_len: usize,
        output: *mut u8, output_cap: usize,
        output_len: *mut usize,
    ) -> u32;
    fn pg_simplify(
        input: *const u8, input_len: usize,
        output: *mut u8, output_cap: usize,
        output_len: *mut usize,
    ) -> u32;
    fn pg_grind(
        input: *const u8, input_len: usize,
        output: *mut u8, output_cap: usize,
        output_len: *mut usize,
    ) -> u32;
    fn pg_shutdown() -> u32;
}

/// Safe wrapper around Lean4 FFI
pub struct LeanBridge {
    _initialized: bool,
}

#[derive(Debug)]
pub enum VerifyResult {
    Verified(Vec<u8>),  // proof bytes
    Rejected,
    Timeout,
    ParseError,
    FfiError(String),
}

impl LeanBridge {
    /// Initialize Lean4 runtime. Call once at startup.
    pub fn new() -> Result<Self, String> {
        // Must initialize Lean runtime first
        unsafe { lean_initialize_runtime_module(); }
        let result = unsafe { pg_init() };
        match result {
            0 => Ok(Self { _initialized: true }),
            _ => Err(format!("Lean4 init failed with code {}", result)),
        }
    }

    /// Verify a candidate theorem.
    pub fn verify(&self, canonical: &str) -> VerifyResult {
        let input = canonical.as_bytes();
        let mut output = vec![0u8; 256 * 1024]; // 256KB buffer
        let mut output_len: usize = 0;

        let result = unsafe {
            pg_verify(
                input.as_ptr(), input.len(),
                output.as_mut_ptr(), output.len(),
                &mut output_len,
            )
        };

        match result {
            0 => {
                output.truncate(output_len);
                VerifyResult::Verified(output)
            }
            1 => VerifyResult::Rejected,
            2 => VerifyResult::Timeout,
            3 => VerifyResult::ParseError,
            code => VerifyResult::FfiError(format!("Unknown code: {}", code)),
        }
    }

    /// Simplify an expression using Lean4's simp tactic.
    pub fn simplify(&self, canonical: &str) -> Result<String, String> {
        let input = canonical.as_bytes();
        let mut output = vec![0u8; 64 * 1024];
        let mut output_len: usize = 0;

        let result = unsafe {
            pg_simplify(
                input.as_ptr(), input.len(),
                output.as_mut_ptr(), output.len(),
                &mut output_len,
            )
        };

        match result {
            0 => {
                output.truncate(output_len);
                String::from_utf8(output).map_err(|e| e.to_string())
            }
            _ => Err(format!("Simplify failed with code {}", result)),
        }
    }
}

impl Drop for LeanBridge {
    fn drop(&mut self) {
        unsafe { pg_shutdown(); }
    }
}

// Lean4 runtime initialization (from lean.h)
extern "C" {
    fn lean_initialize_runtime_module();
}
```

### Build Integration

```toml
# engine/crates/lean-bridge/build.rs context:

# 1. Lake builds Lean4 project into a static library
# 2. build.rs tells Cargo where to find it
# 3. Cargo links against the static lib + leanshared
```

```rust
// engine/crates/lean-bridge/build.rs
fn main() {
    // Path to Lean4 static library (built by Lake)
    let lean_lib_dir = std::env::var("LEAN_LIB_DIR")
        .unwrap_or_else(|_| "../../../prover/build/lib".to_string());

    // Path to Lean4 runtime
    let lean_sysroot = std::env::var("LEAN_SYSROOT")
        .unwrap_or_else(|_| {
            let output = std::process::Command::new("lean")
                .arg("--print-prefix")
                .output()
                .expect("lean not found");
            String::from_utf8(output.stdout).unwrap().trim().to_string()
        });

    println!("cargo:rustc-link-search=native={}", lean_lib_dir);
    println!("cargo:rustc-link-search=native={}/lib/lean/library", lean_sysroot);
    println!("cargo:rustc-link-lib=static=PhysicsGenerator");
    println!("cargo:rustc-link-lib=dylib=leanshared");
}
```

---

## 2. Shared Memory Ring Buffer

For high-throughput verification (1000+ candidates/second):

### Memory Layout

```
Offset    Size        Description
───────────────────────────────────────────────────
0x0000    8 bytes     write_head (AtomicU64) — Rust increments
0x0008    8 bytes     read_head (AtomicU64) — Lean4 increments
0x0010    8 bytes     result_write_head (AtomicU64) — Lean4 increments
0x0018    8 bytes     result_read_head (AtomicU64) — Rust increments
0x0020    8 bytes     slot_count (u64) — number of slots
0x0028    8 bytes     candidate_slot_size (u64) — bytes per candidate slot
0x0030    8 bytes     result_slot_size (u64) — bytes per result slot
0x0038    8 bytes     reserved

0x0040    N * 4096    Candidate ring buffer
                      Each slot:
                        [0..4]   payload_len: u32
                        [4..8]   sequence_num: u32
                        [8..]    payload: UTF-8 canonical expression

0x0040 + N*4096       Result ring buffer
                      Each slot:
                        [0]      status: u8 (0=verified, 1=rejected, 2=timeout)
                        [1..5]   sequence_num: u32 (matches candidate)
                        [5..9]   payload_len: u32
                        [9..]    payload: proof bytes (if verified)
```

### Rust Producer

```rust
// engine/crates/lean-bridge/src/shared_mem.rs

use memmap2::MmapMut;
use std::sync::atomic::{AtomicU64, Ordering};

pub struct SharedMemProducer {
    mmap: MmapMut,
    slot_count: u64,
    candidate_slot_size: u64,
    candidates_offset: usize,
    results_offset: usize,
}

impl SharedMemProducer {
    /// Push a candidate into the ring buffer.
    /// Returns sequence number for matching with result.
    pub fn push_candidate(&self, canonical: &[u8]) -> Option<u32> {
        let write_head = self.write_head();
        let read_head = self.read_head();

        // Check if ring is full
        if write_head - read_head >= self.slot_count {
            return None; // Buffer full, Lean4 can't keep up
        }

        let slot_idx = (write_head % self.slot_count) as usize;
        let offset = self.candidates_offset + slot_idx * self.candidate_slot_size as usize;
        let seq = write_head as u32;

        // Write payload length + sequence + data
        let slot = &mut self.mmap[offset..offset + self.candidate_slot_size as usize];
        slot[0..4].copy_from_slice(&(canonical.len() as u32).to_le_bytes());
        slot[4..8].copy_from_slice(&seq.to_le_bytes());
        slot[8..8 + canonical.len()].copy_from_slice(canonical);

        // Advance write head (release ordering for Lean4 to see data)
        self.set_write_head(write_head + 1);
        Some(seq)
    }

    /// Poll for a result matching a sequence number.
    pub fn poll_result(&self, seq: u32) -> Option<VerifyResult> {
        // ... read from result ring buffer
        todo!()
    }
}
```

### Lean4 Consumer

```lean
-- PhysicsGenerator/Bridge/SharedMem.lean

/-- Worker loop: read candidates from shared memory, verify, write results -/
@[export pg_worker_loop]
def workerLoop (shmPath : @& String) : IO Unit := do
  let shm ← openSharedMemory shmPath
  loop do
    -- Spin-wait for new candidate
    let candidate ← shm.readNextCandidate
    -- Verify using tactic cascade
    let result ← verifyCandidateFromBytes candidate.payload
    -- Write result back to result ring
    shm.writeResult candidate.sequenceNum result
```

### Process Architecture

```
┌─────────────────┐
│  Rust Engine     │
│  (main process)  │ ── mmap file ──┐
│                  │                 │
│  Push candidates │                 │
│  Poll results    │                 │
└─────────────────┘                 │
                                     │
┌─────────────────┐                 │
│  Lean4 Worker 1  │ ── reads/writes ┤
│  (child process) │                 │
└─────────────────┘                 │
                                     │
┌─────────────────┐                 │
│  Lean4 Worker 2  │ ── reads/writes ┤
│  (child process) │                 │
└─────────────────┘                 │
                                     │
┌─────────────────┐                 │
│  Lean4 Worker N  │ ── reads/writes ┘
│  (child process) │
└─────────────────┘
```

Rust spawns N Lean4 worker processes. Each loads the Mathlib environment once
and enters the verification loop. Workers coordinate via atomic pointers in
shared memory — no locks needed.

---

## 3. Canonical Expression Format

Lean4 and Rust must agree on a canonical representation for expressions.

### Prefix Notation Grammar

```
expr      := var | const | lit | app | binop | unop | quant | special
var       := "v:" IDENT
const     := "c:" CONST_NAME
lit       := "n:" RATIONAL
app       := "(@ " expr " " expr ")"
binop     := "(+ " expr " " expr ")"
           | "(* " expr " " expr ")"
           | "(/ " expr " " expr ")"
           | "(^ " expr " " expr ")"
           | "(= " expr " " expr ")"
           | "(-> " expr " " expr ")"
unop      := "(neg " expr ")"
           | "(sqrt " expr ")"
           | "(sin " expr ")"
           | "(cos " expr ")"
           | "(exp " expr ")"
           | "(log " expr ")"
           | "(deriv " IDENT " " expr ")"
           | "(partial " IDENT " " expr ")"
           | "(grad " expr ")"
           | "(div " expr ")"
           | "(curl " expr ")"
quant     := "(forall " IDENT " " TYPE " " expr ")"
           | "(exists " IDENT " " TYPE " " expr ")"
           | "(lambda " IDENT " " TYPE " " expr ")"
special   := "(integral " IDENT " " expr " " expr " " expr ")"
           | "(sum " IDENT " " expr " " expr " " expr ")"
           | "(limit " IDENT " " expr " " expr ")"
```

### Example

E = mc^2 in canonical prefix notation:
```
(= v:E (* v:m (^ c:speed_of_light n:2)))
```

Newton's second law F = ma:
```
(= v:F (* v:m v:a))
```

Schrodinger equation:
```
(= (* (c:i) (* c:hbar (partial t (v:psi))))
   (@ v:H (v:psi)))
```

---

## 4. Tactic Strategy

The verification pipeline tries tactics in order of speed and power:

| Priority | Tactic | Timeout | Best For |
|----------|--------|---------|----------|
| 1 | `omega` | 500ms | Integer/natural number goals |
| 2 | `norm_num` | 500ms | Numeric computations |
| 3 | `ring` | 1s | Polynomial ring equalities |
| 4 | `simp` | 2s | Rewriting with Mathlib lemma DB |
| 5 | `linarith` | 2s | Linear arithmetic inequalities |
| 6 | `field_simp` | 2s | Field fraction simplification |
| 7 | `polyrith` | 5s | Polynomial arithmetic (calls external oracle) |
| 8 | `grind` | 10s | SMT-style reasoning (most powerful) |

If all tactics fail, the candidate is rejected. The GA can try again with
modified versions in future generations.

---

## 5. Proof Export (Academic Validation)

When a theorem is verified, the proof term and tactic are stored in RocksDB.
To allow independent verification by academics, the system can export any
theorem as a standalone `.lean` file.

### Export Pipeline

```
GET /api/theorems/:id/proof.lean
    │
    ▼
┌─────────────────────────────────────────────────────────────┐
│  engine/crates/lean-bridge/src/export.rs                     │
│                                                               │
│  1. Load TheoremRecord from RocksDB (theorems CF)            │
│  2. Load ProofRecord from RocksDB (proofs CF)                │
│  3. Load LineageRecord from RocksDB (lineage CF)             │
│  4. Resolve axiom ancestors → determine required imports     │
│  5. Convert Expr AST → Lean4 type signature                  │
│  6. Convert ProofTree → Lean4 proof body                     │
│  7. Emit .lean file with header, imports, statement, proof   │
└─────────────────────────────────────────────────────────────┘
```

### Lean4 Export Format

```lean
/-
  Auto-generated by Nasrudin (https://nasrudin.example.com)
  Theorem ID: a1b2c3d4e5f6g7h8
  Domain:     SpecialRelativity
  Depth:      8
  Verified:   2025-03-15T14:32:01Z
  Tactic:     grind (10.2s)
  Lean4:      v4.27.0

  Verify independently:
    lake build PhysicsGenerator.Exported.energy_momentum_relation
-/

import PhysicsGenerator.Axioms.SpecialRelativity
import PhysicsGenerator.Axioms.Mechanics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- Energy-momentum relation: E² = (pc)² + (mc²)² -/
theorem energy_momentum_relation
  (E p m : ℝ) (c : ℝ) (hc : c = speed_of_light)
  (h_rest_energy : rest_energy m c = m * c ^ 2)
  (h_momentum_energy : momentum_energy p c = p * c) :
  E ^ 2 = (p * c) ^ 2 + (m * c ^ 2) ^ 2 := by
  grind [sr_postulate_1, sr_postulate_2,
         energy_conservation, momentum_conservation]
```

### Export Strategies by ProofTree Type

| ProofTree variant | Export strategy |
|-------------------|----------------|
| `TacticProof { tactic, proof_term }` | Emit `by <tactic> [lemmas]`. Preferred — most readable. |
| `ModusPonens { premise, implication }` | Emit `have` chain: `have h1 := ...; exact h1 ...` |
| `EqChain(steps)` | Emit `calc` block with chained equalities |
| `Rewrite { equation, target, position }` | Emit `rw [equation] at target` |
| `Substitute { source, var, replacement }` | Emit `specialize source (replacement)` |
| `Algebraic { source, operations }` | Emit `ring_nf` or step-by-step `linarith`/`field_simp` |
| Raw proof term (opaque `Vec<u8>`) | Deserialize via Lean4 FFI, emit term-mode proof as fallback |

### Import Resolution

The export generator traces the theorem's axiom ancestors (from the `lineage`
CF) and maps each axiom ID to its Lean4 module:

```rust
fn resolve_imports(axiom_ids: &[TheoremId]) -> Vec<String> {
    axiom_ids.iter().map(|id| {
        match classify_axiom(id) {
            Domain::ClassicalMechanics => "PhysicsGenerator.Axioms.Mechanics",
            Domain::SpecialRelativity  => "PhysicsGenerator.Axioms.SpecialRelativity",
            Domain::Electromagnetism   => "PhysicsGenerator.Axioms.Electromagnetism",
            Domain::QuantumMechanics   => "PhysicsGenerator.Axioms.QuantumMechanics",
            Domain::Thermodynamics     => "PhysicsGenerator.Axioms.Thermodynamics",
            Domain::GeneralRelativity  => "PhysicsGenerator.Axioms.GeneralRelativity",
            _ => "PhysicsGenerator.Axioms.Dimensions",
        }
    }).collect::<BTreeSet<_>>() // dedup + sort
      .into_iter().collect()
}
```

Only the modules actually needed are imported, keeping the exported file minimal.

### Verification by Academics

An academic validates a Nasrudin theorem by:

1. **Download** the `.lean` file from the UI ("Download .lean" button in the
   proof tab) or via `GET /api/theorems/:id/proof.lean`.
2. **Clone** the Nasrudin prover project, which provides the axiom definitions
   and Mathlib dependency:
   ```bash
   git clone https://github.com/nasrudin/prover
   cd prover
   ```
3. **Place** the downloaded file in `PhysicsGenerator/Exported/`.
4. **Build** with Lake:
   ```bash
   lake build PhysicsGenerator.Exported.<theorem_name>
   ```
5. **Exit code 0** means Lean4 independently type-checked the proof from
   scratch — the theorem is valid given the stated axioms.

This provides a complete chain of trust: the proof is not "trust the server
said so" — the academic re-runs Lean4's kernel checker on their own hardware.
