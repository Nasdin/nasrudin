/-!
# Bridge Types

Types for communication between Lean4 and Rust via C FFI.
-/

namespace PhysicsGenerator.Bridge

/-- Result of attempting to verify a candidate theorem -/
inductive VerifyResult
  | verified (proofBytes : ByteArray)
  | rejected (reason : String)
  | timeout
  | parseError (message : String)

/-- A candidate theorem submitted by the Rust engine -/
structure Candidate where
  /-- Canonical prefix notation of the proposition -/
  canonical : String
  /-- Unique sequence number for matching results -/
  sequenceNum : UInt32
  deriving Repr

end PhysicsGenerator.Bridge
