/-
Transport + user-facing entry points: run a Mathematica command on Lean term(s).
Port of `execute` / `execute_and_eval` / `run_command_on*` / `load_file` from the
Lean 3 `mathematica.lean`, plus `escape_term` / `escape_quotes` / `escape_slash` /
`strip_newline` from `mathematica_parser.lean`.

The kernel connection is abstracted behind `Transport`, so the Lean 3 mechanism
(shell out to `python3 client2.py`, which relays over a socket to a running
`server2.m`) — kept as the day-one default — can later be swapped for a native
socket without touching the reflection/translation pipeline.  `mockTransport`
returns a canned response, letting us test the whole Lean-side round-trip
(reflect → send → parse → translate) with no live Mathematica kernel.

This ties the pipeline together:
  Expr --formatExpr--> string --(Transport)--> wire --Wire.parse--> MMExpr --exprOfMMExpr--> Expr
-/
import Mathematica.Reflect
import Mathematica.Translate
import Mathematica.Wire

open Lean Lean.Meta

namespace Mathematica

/-! ### String escaping (protocol plumbing) -/

/-- `&` → `&&`.  A command is `&!`-terminated on the wire, so literal `&` must be
    doubled (the server undoes it).  Port of `escape_term`. -/
def escapeTerm (s : String) : String :=
  s.foldl (fun acc c => if c == '&' then acc ++ "&&" else acc.push c) ""

/-- `"` → `\"`, for embedding in a Mathematica string (port of `escape_quotes`). -/
def escapeQuotes (s : String) : String :=
  s.foldl (fun acc c => if c == '"' then acc ++ "\\\"" else acc.push c) ""

/-- `\` → `\\` (port of `escape_slash`). -/
def escapeSlash (s : String) : String :=
  s.foldl (fun acc c => if c == '\\' then acc ++ "\\\\" else acc.push c) ""

/-- Drop a single trailing newline (port of `strip_newline`). -/
def stripNewline (s : String) : String :=
  if s.endsWith "\n" then String.ofList s.toList.dropLast else s

/-! ### Transport -/

/-- How to talk to a Mathematica kernel: given a prepared, `&!`-terminated payload
    and whether to evaluate in the global (persistent) context, return the raw
    wire response. -/
structure Transport where
  send : (payload : String) → (global : Bool) → IO String

/-- The Lean 3 mechanism: shell out to the Python client, which relays the payload
    to a running server over a socket and prints the response.  Long payloads
    (≥ 2040 chars) go via a temp file (`-f`), matching Lean 3. -/
def Transport.pythonClient (clientPath : String) (python : String := "python3") : Transport :=
  { send := fun payload global => do
      let gArgs := if global then #["-g"] else #[]
      let out ←
        if payload.length < 2040 then
          IO.Process.output { cmd := python, args := #[clientPath] ++ gArgs ++ #[payload] }
        else do
          let tmpDir := (← IO.getEnv "TMPDIR").getD "/tmp"
          let tmp := System.FilePath.mk (tmpDir ++ "/mathematica_bridge_exch.txt")
          IO.FS.writeFile tmp payload
          IO.Process.output { cmd := python, args := #[clientPath] ++ gArgs ++ #["-f", tmp.toString] }
      if out.exitCode != 0 then
        throw (IO.userError s!"mathematica client exited with code {out.exitCode}: {out.stderr}")
      return out.stdout }

/-- Read the client path from `MATHEMATICA_BRIDGE_CLIENT`, else a repo-relative
    default. -/
def Transport.fromEnv : IO Transport := do
  let path := (← IO.getEnv "MATHEMATICA_BRIDGE_CLIENT").getD "wolfram/client.py"
  return Transport.pythonClient path

/-- A test transport that returns a fixed response, ignoring the payload — lets us
    exercise the full reflect → send → parse → translate path with no kernel. -/
def mockTransport (response : String) : Transport :=
  { send := fun _ _ => pure response }

/-! ### Execute -/

/-- Send `cmd` to Mathematica, return the raw wire response (port of `execute`). -/
def executeRaw (t : Transport) (cmd : String) (global : Bool := false) : IO String :=
  t.send (escapeTerm cmd ++ "&!") global

/-- Send `cmd`, parse the response into an `MMExpr` (port of `execute_and_eval`). -/
def executeAndEval (t : Transport) (cmd : String) (global : Bool := false) : IO MMExpr := do
  let resp ← executeRaw t cmd global
  match Wire.parse resp with
  | .ok m    => return m
  | .error e => throw (IO.userError s!"could not parse Mathematica response: {e}\n  raw: {resp}")

/-! ### User-facing: run a Mathematica command on Lean term(s) -/

/-- Reflect `e` into Mathematica syntax, wrap it with `cmd`, evaluate, and translate
    the result back to an `Expr` (port of `run_command_on`). -/
def runCommandOn (t : Transport) (cmd : String → String) (e : Expr) : MetaM Expr := do
  let m ← executeAndEval t (cmd (← formatExpr e))
  exprOfMMExpr [] m

/-- Two-argument version (port of `run_command_on_2`). -/
def runCommandOn2 (t : Transport) (cmd : String → String → String) (e₁ e₂ : Expr) : MetaM Expr := do
  let m ← executeAndEval t (cmd (← formatExpr e₁) (← formatExpr e₂))
  exprOfMMExpr [] m

/-- Reflect each element into a Mathematica list `{…}` and run `cmd` on it
    (port of `run_command_on_list`). -/
def runCommandOnList (t : Transport) (cmd : String → String) (es : List Expr) : MetaM Expr := do
  let parts ← es.mapM formatExpr
  let m ← executeAndEval t (cmd ("{" ++ String.intercalate ", " parts ++ "}"))
  exprOfMMExpr [] m

/-- Build a `Get[...]` command loading a Mathematica file on a search path
    (port of `mk_get_cmd`). -/
def mkGetCmd (searchDir path : String) : String :=
  "Get[\"" ++ path ++ "\",Path->{DirectoryFormat[\"" ++ searchDir ++ "\"]}];"

/-- Reflect `e`, but first import the file at `path` (port of `run_command_on_using`). -/
def runCommandOnUsing (t : Transport) (cmd : String → String) (e : Expr) (searchDir path : String) :
    MetaM Expr :=
  let getCmd := escapeSlash (mkGetCmd searchDir path)
  runCommandOn t (fun s => getCmd ++ cmd s) e

/-- Load a Mathematica file into the global context (port of `load_file`). -/
def loadFile (t : Transport) (searchDir path : String) : IO Unit := do
  let _ ← executeRaw t (mkGetCmd searchDir path) (global := true)
  pure ()

/-! ## Tests -/

#eval show MetaM Unit from do
  let assert (lbl : String) (b : Bool) : MetaM Unit := unless b do throwError m!"{lbl}: failed"
  -- pure protocol helpers
  assert "escapeTerm"   (escapeTerm "a&b&c" == "a&&b&&c")
  assert "escapeQuotes" (escapeQuotes "say \"hi\"" == "say \\\"hi\\\"")
  assert "escapeSlash"  (escapeSlash "a\\b" == "a\\\\b")
  assert "stripNewline" (stripNewline "line\n" == "line" && stripNewline "x" == "x")
  assert "mkGetCmd"     (mkGetCmd "/dir" "foo.wl" == "Get[\"foo.wl\",Path->{DirectoryFormat[\"/dir\"]}];")
  -- full round-trip against a mock kernel (no Mathematica needed): the mock
  -- pretends the kernel returned Plus[1,2] regardless of input.
  let t := mockTransport "AY[Plus][I[1],I[2]]"
  let e ← runCommandOn t (fun s => s) (mkConst ``Nat)
  assert "mock: runCommandOn" (← isDefEq e (← mkAppM ``HAdd.hAdd #[mkNatLit 1, mkNatLit 2]))
  let e2 ← runCommandOnList t (fun s => s) [mkNatLit 1, mkNatLit 2]
  assert "mock: runCommandOnList" (← isDefEq e2 (← mkAppM ``HAdd.hAdd #[mkNatLit 1, mkNatLit 2]))
  -- a malformed kernel response surfaces as a structured error, not a crash
  let bad := mockTransport "not-a-wire-response"
  let threw ← (do let _ ← runCommandOn bad (fun s => s) (mkConst ``Nat); pure false) <|> pure true
  assert "mock: malformed response throws" threw

end Mathematica
