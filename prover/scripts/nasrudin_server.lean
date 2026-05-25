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

  Each `Elaborate`/`VerifyTactic` request runs `Lean.Language.Lean.process`
  against the persistent module cache (imports are deserialised once at
  daemon boot and reused thereafter), so a bad candidate cannot leak
  declarations into subsequent requests.

  Throughput: cold-boot is ~5–10s (Mathlib load); per-request elaboration
  is typically ~100–500ms vs. ~30–120s for `lake build`.

  Why `Language.Lean.process` and not `Lean.Elab.process`:
  `Lean.Elab.process` builds a `Command.State` with an EMPTY
  `Parser.ModuleParserState`, so parser extensions registered by
  `import Mathlib` (e.g. `≤`, `ℝ`, the `(x : ℝ)` binder syntax) never
  activate. Every elaboration then errors at the first unicode char.
  `Language.Lean.process` is what `Lean.Elab.runFrontend` uses; it
  invokes `processHeader`, which loads the imports AND wires up their
  parser extensions before parsing the body.
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

/-- True iff the source contains at least one `import …` line at the start
    of a line (after optional leading whitespace). -/
def hasImport (s : String) : Bool :=
  s.splitOn "\n" |>.any fun l => l.trimAsciiStart.startsWith "import "

/-- Default header used when a candidate omits its own imports. The GA's
    seed emitter currently includes them, but legacy callers (and the
    quick-probe scripts) sometimes don't. We always want Mathlib +
    LeafImports + Basic in scope so notation like `≤`, `ℝ`, and the
    PhysicsGenerator atoms resolve. -/
def defaultHeader : String :=
  "import Mathlib\nimport PhysicsGenerator.LeafImports\nimport PhysicsGenerator.Basic\n"

/-- Format the error subset of a MessageLog into a single string. -/
def formatErrors (msgs : MessageLog) : IO String := do
  let mut out := ""
  for msg in msgs.toList do
    if msg.severity == MessageSeverity.error then
      let s ← msg.toString
      out := out ++ s ++ "\n"
  return out

/-- Run elaboration of `source`. Returns `Except err ()`.

    Uses `Lean.Language.Lean.process`, the same pipeline as
    `Lean.Elab.runFrontend`. This runs `processHeader` on the source's
    own `import` lines, which loads the cached `.olean` files (instant
    after the first call) AND activates their registered parser
    extensions. Without that step `≤`, `ℝ`, etc. all fail to parse. -/
def elaborateSource (source : String) : IO (Except String Unit) := do
  let prepared :=
    if hasImport source then source else defaultHeader ++ source
  try
    let mainModuleName : Lean.Name := `NasrudinCandidate
    let inputCtx := Lean.Parser.mkInputContext prepared "<input>"
    let ctx : Lean.Language.ProcessingContext := { inputCtx with }
    let setup (stx : Lean.Elab.HeaderSyntax) :
        Lean.Language.ProcessingT IO
          (Except Lean.Language.Lean.HeaderProcessedSnapshot
            Lean.Language.Lean.SetupImportsResult) := do
      return .ok {
        mainModuleName
        isModule    := stx.isModule
        imports     := stx.imports
        opts        := {}
        trustLevel  := 1024
      }
    let snap ← Lean.Language.Lean.process setup none ctx
    match Lean.Language.Lean.waitForFinalCmdState? snap with
    | none =>
      -- Header processing or the very first command snapshot failed. The
      -- diagnostics live on the snapshot tree; pull them out so the
      -- caller sees an informative error instead of "no cmd state".
      let snaps := Lean.Language.toSnapshotTree snap
      let mut buf : MessageLog := {}
      for child in snaps.getAll do
        buf := buf ++ child.diagnostics.msgLog
      if buf.hasErrors then
        let err ← formatErrors buf
        return .error err
      else
        return .error "elaborator produced no final command state"
    | some cmdState =>
      if cmdState.messages.hasErrors then
        let err ← formatErrors cmdState.messages
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

def handleElaborate (line : String) : IO Unit := do
  let startMs ← IO.monoMsNow
  match Json.parse line >>= fromJson? (α := ElaborateReq) with
  | .error e => emit (respFatal s!"elaborate parse: {e}")
  | .ok req =>
    match ← elaborateSource req.source with
    | .ok () =>
      let elapsed := (← IO.monoMsNow) - startMs
      emit (respElabOk req.id elapsed)
    | .error msg =>
      let elapsed := (← IO.monoMsNow) - startMs
      emit (respElabError req.id msg elapsed)

def handleVerifyTactic (line : String) : IO Unit := do
  let startMs ← IO.monoMsNow
  match Json.parse line >>= fromJson? (α := VerifyTacticReq) with
  | .error e => emit (respFatal s!"verify_tactic parse: {e}")
  | .ok req =>
    -- Splice tactic into the source: the GA's emitter ends each
    -- theorem statement with `:= by\n` and a newline, so appending
    -- `tactic\n` produces a complete theorem block.
    let combined := req.source ++ "  " ++ req.tactic ++ "\n"
    match ← elaborateSource combined with
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
def dispatch (line : String) : IO Bool := do
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
      | "elaborate"      => handleElaborate line; return true
      | "verify_tactic"  => handleVerifyTactic line; return true
      | "ping"           => handlePing line; return true
      | "shutdown"       => return false
      | other =>
        emit (respFatal s!"unknown request kind: {other}")
        return true

/-! ## Entry point.

  In `lean --run`, by the time `main` executes, the `import Mathlib`,
  `import PhysicsGenerator.LeafImports`, and `import PhysicsGenerator.Basic`
  directives at the top of this file have been processed and the relevant
  `.olean` files are paged in. Each subsequent
  `Lean.Language.Lean.process` call re-runs `processHeader` for the
  candidate source, but the import resolution hits the already-warm
  module cache, so per-request cost is in the ~ms range (vs. the ~5-10s
  cold-boot deserialisation we pay once here). -/

def main : IO Unit := do
  -- We do NOT pre-build an `Environment` value with `Lean.importModules`
  -- and feed it to `Lean.Elab.process` — that pipeline (intentionally)
  -- does not activate parser extensions registered by the imports, so
  -- candidate sources fail at the first unicode token (`≤`, `ℝ`, …).
  -- Instead each request goes through `Lean.Language.Lean.process`,
  -- which does the full `processHeader`-then-elaborate-body dance.

  -- Boot ack — Rust client waits for this before sending requests.
  emit (respOk 0)

  let stdin ← IO.getStdin
  let mut keepGoing := true
  while keepGoing do
    -- `getLine` returns "" at EOF (no trailing newline). On well-formed
    -- input each line is at least "\n", so empty string ⇒ stdin closed.
    let line ← stdin.getLine
    if line.isEmpty then break
    -- `trimAscii` returns `String.Slice` in Lean 4.27+. Slice has an
    -- `isEmpty` and is auto-coerced to String at the dispatch boundary.
    let trimmed := line.trimAscii
    if trimmed.isEmpty then continue
    keepGoing ← dispatch trimmed.toString
