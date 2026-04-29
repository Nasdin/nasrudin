/-
  Long-lived Nasrudin elaborator-server stub.

  Reads JSON requests from stdin (one per line), writes JSON responses to
  stdout (one per line). Pre-loads Mathlib at startup.

  Wire format matches `engine/crates/lean-bridge/src/persistent_protocol.rs`.

  TODO(prover): flesh out the elaboration loop using Lean.Elab APIs. For
  now this stub exists so the Rust side has something to spawn; it
  immediately replies Fatal to any non-Ping request, and the Rust side
  falls back to subprocess-per-call.
-/
import Mathlib

def main : IO Unit := do
  -- Boot acknowledgement so the Rust client knows Mathlib is loaded.
  let stdout ← IO.getStdout
  stdout.putStrLn "{\"kind\":\"ok\",\"id\":0}"
  stdout.flush
  -- Read-eval loop.
  let stdin ← IO.getStdin
  while ¬ (← stdin.isEof) do
    let line ← stdin.getLine
    let trimmed := line.trim
    if trimmed.isEmpty then continue
    -- Crude parse: only Ping is recognised in the stub.
    if trimmed.startsWith "{\"kind\":\"ping\"" then
      -- Echo the id from the request.
      let idPart :=
        match trimmed.splitOn "\"id\":" |>.tail? with
        | some (rest :: _) => rest.takeWhile (fun c => c.isDigit)
        | _ => "0"
      stdout.putStrLn s!"\{\"kind\":\"pong\",\"id\":{idPart}\}"
      stdout.flush
    else
      stdout.putStrLn "{\"kind\":\"fatal\",\"message\":\"stub server: only Ping is implemented\"}"
      stdout.flush
