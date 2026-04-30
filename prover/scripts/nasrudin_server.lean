/-
  Long-lived Nasrudin elaborator server.

  Reads JSON requests from stdin (one per line), writes JSON responses to
  stdout (one per line). Pre-loads Mathlib + LeafImports + Basic at startup.

  Wire format matches `engine/crates/lean-bridge/src/persistent_protocol.rs`.

  Boot sequence:
    1. `lake env lean --run scripts/nasrudin_server.lean` is spawned with
       the lakefile's search path set up so `import Mathlib` resolves.
    2. We immediately emit `{"kind":"ok","id":0}` so the Rust client knows
       the elaborator is warm.
    3. Per request: parse JSON, dispatch to handler, emit response JSON.

  Each `Elaborate`/`VerifyTactic` request runs `Lean.Elab.process` against
  the *startup* environment (no accumulation across requests), so a bad
  candidate cannot leak declarations into subsequent requests.

  Throughput: cold-boot is ~5–10s (Mathlib load); per-request elaboration
  is typically ~100–500ms vs. ~30–120s for `lake build`.
-/
import Mathlib
import PhysicsGenerator.LeafImports
import PhysicsGenerator.Basic

open Lean Elab

namespace Nasrudin.Server

/-! ## Wire types matching persistent_protocol.rs -/

structure ElaborateReq where
  id : Nat
  source : String
deriving FromJson

structure VerifyTacticReq where
  id : Nat
  source : String
  tactic : String
deriving FromJson

structure PingReq where
  id : Nat
deriving FromJson

/-- Build a response line as JSON, matching the Rust enum tags. -/
def respOk (id : Nat) : String :=
  Json.mkObj [("kind", Json.str "ok"), ("id", toJson id)] |>.compress

def respPong (id : Nat) : String :=
  Json.mkObj [("kind", Json.str "pong"), ("id", toJson id)] |>.compress

def respElabOk (id : Nat) (elapsedMs : Nat) : String :=
  Json.mkObj
    [ ("kind", Json.str "elaborate_ok")
    , ("id", toJson id)
    , ("elapsed_ms", toJson elapsedMs)
    ]
  |>.compress

def respElabError (id : Nat) (message : String) (elapsedMs : Nat) : String :=
  Json.mkObj
    [ ("kind", Json.str "elaborate_error")
    , ("id", toJson id)
    , ("message", Json.str message)
    , ("elapsed_ms", toJson elapsedMs)
    ]
  |>.compress

def respVerifyOk (id : Nat) (elapsedMs : Nat) : String :=
  Json.mkObj
    [ ("kind", Json.str "verify_ok")
    , ("id", toJson id)
    , ("elapsed_ms", toJson elapsedMs)
    ]
  |>.compress

def respVerifyError (id : Nat) (message : String) (elapsedMs : Nat) : String :=
  Json.mkObj
    [ ("kind", Json.str "verify_error")
    , ("id", toJson id)
    , ("message", Json.str message)
    , ("elapsed_ms", toJson elapsedMs)
    ]
  |>.compress

def respFatal (message : String) : String :=
  Json.mkObj
    [ ("kind", Json.str "fatal")
    , ("message", Json.str message)
    ]
  |>.compress

/-- Write a response line and flush. -/
def emit (line : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn line
  stdout.flush

/-- Strip leading `import …` lines from candidate source: every module the
    GA emits already has its imports satisfied by our boot-time imports. -/
def stripImports (s : String) : String :=
  let lines := s.splitOn "\n"
  let kept := lines.filter fun l =>
    -- trimLeft is deprecated to trimAsciiStart in 4.27; both return Slice.
    -- Coerce the literal to Slice via the auto-coercion to compare.
    let t := l.trimAsciiStart
    ¬ t.startsWith "import "
  String.intercalate "\n" kept

/-- Format the error subset of a MessageLog into a single string. -/
def formatErrors (msgs : MessageLog) : IO String := do
  let mut out := ""
  for msg in msgs.toList do
    if msg.severity == MessageSeverity.error then
      let s ← msg.toString
      out := out ++ s ++ "\n"
  return out

/-- Run elaboration of `source` against `env`. Returns `Except err ()`. -/
def elaborateSource (env : Environment) (source : String) : IO (Except String Unit) := do
  let stripped := stripImports source
  try
    let (_envOut, msgs) ← Lean.Elab.process stripped env {}
    if msgs.hasErrors then
      let err ← formatErrors msgs
      return .error err
    else
      return .ok ()
  catch e =>
    return .error s!"elaborator exception: {e}"

end Nasrudin.Server

open Nasrudin.Server

/-! ## Request dispatch.

  Each branch is `try`-wrapped at the IO level: a thrown exception during
  one request emits a `fatal` line but does NOT crash the loop, so the
  Rust supervisor only restarts the subprocess on truly unrecoverable
  conditions (e.g. stdin EOF). -/

def handleElaborate (env : Environment) (line : String) : IO Unit := do
  let startMs ← IO.monoMsNow
  match Json.parse line >>= fromJson? (α := ElaborateReq) with
  | .error e => emit (respFatal s!"elaborate parse: {e}")
  | .ok req =>
    match ← elaborateSource env req.source with
    | .ok () =>
      let elapsed := (← IO.monoMsNow) - startMs
      emit (respElabOk req.id elapsed)
    | .error msg =>
      let elapsed := (← IO.monoMsNow) - startMs
      emit (respElabError req.id msg elapsed)

def handleVerifyTactic (env : Environment) (line : String) : IO Unit := do
  let startMs ← IO.monoMsNow
  match Json.parse line >>= fromJson? (α := VerifyTacticReq) with
  | .error e => emit (respFatal s!"verify_tactic parse: {e}")
  | .ok req =>
    -- Splice tactic into the source: the GA's emitter ends each
    -- theorem statement with `:= by\n` and a newline, so appending
    -- `tactic\n` produces a complete theorem block.
    let combined := req.source ++ "  " ++ req.tactic ++ "\n"
    match ← elaborateSource env combined with
    | .ok () =>
      let elapsed := (← IO.monoMsNow) - startMs
      emit (respVerifyOk req.id elapsed)
    | .error msg =>
      let elapsed := (← IO.monoMsNow) - startMs
      emit (respVerifyError req.id msg elapsed)

def handlePing (line : String) : IO Unit := do
  match Json.parse line >>= fromJson? (α := PingReq) with
  | .error e => emit (respFatal s!"ping parse: {e}")
  | .ok req => emit (respPong req.id)

/-- Returns `false` on Shutdown, otherwise `true` (continue loop). -/
def dispatch (env : Environment) (line : String) : IO Bool := do
  match Json.parse line with
  | .error e =>
    emit (respFatal s!"json parse error: {e}")
    return true
  | .ok j =>
    match j.getObjValAs? String "kind" with
    | .error _ =>
      emit (respFatal "missing or non-string \"kind\" field")
      return true
    | .ok kind =>
      match kind with
      | "elaborate"      => handleElaborate env line; return true
      | "verify_tactic"  => handleVerifyTactic env line; return true
      | "ping"           => handlePing line; return true
      | "shutdown"       => return false
      | other =>
        emit (respFatal s!"unknown request kind: {other}")
        return true

/-! ## Entry point.

  In `lean --run`, by the time `main` executes, all `import` directives at
  the top of this file have been processed. We capture the resulting
  environment via `getEnv` (inside an `IO` action that has elaborator
  access) and reuse it for every subsequent request. -/

def main : IO Unit := do
  -- The startup environment with Mathlib + LeafImports + Basic loaded is
  -- already in scope; pull it out via importModules so we have a
  -- top-level `Environment` value to pass to `Lean.Elab.process`.
  let imports : Array Import := #[
    { module := `Mathlib },
    { module := `PhysicsGenerator.LeafImports },
    { module := `PhysicsGenerator.Basic }
  ]
  -- trustLevel 1024 = trust the .olean files we just imported (they're
  -- our own + Mathlib, kernel-checked at lake build time).
  let env ← Lean.importModules imports (opts := {}) (trustLevel := 1024)

  -- Boot ack — Rust client waits for this before sending requests.
  emit (respOk 0)

  let stdin ← IO.getStdin
  let mut keepGoing := true
  while keepGoing do
    -- `getLine` returns "" at EOF (no trailing newline). On well-formed
    -- input each line is at least "\n", so empty string ⇒ stdin closed.
    let line ← stdin.getLine
    if line.isEmpty then break
    let trimmed := line.trim
    if trimmed.isEmpty then continue
    keepGoing ← dispatch env trimmed
