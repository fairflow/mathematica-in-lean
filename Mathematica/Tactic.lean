/-
Transport + user-facing entry points: run a Mathematica command on Lean term(s).
Port of `execute` / `execute_and_eval` / `run_command_on*` / `load_file` from the
Lean 3 `mathematica.lean`.

Lean reaches a Mathematica kernel through a `Transport`.  The default,
`Transport.persistentKernel`, spawns one long-lived `WolframKernel` and drives it
over stdin/stdout — **no Python and no socket server**.  (The Lean 3 design shelled
out to a Python client relaying over a socket to a `server2.m`; that whole layer is
gone — `IO.Process` gives Lean a persistent kernel directly, and a mutex makes it
safe under Lean's parallel elaboration.)  `mockTransport` returns a canned response
for kernel-free testing.

Pipeline:
  Expr --formatExpr--> string --(Transport)--> wire --Wire.parse--> MMExpr --exprOfMMExpr--> Expr
-/
import Mathematica.Reflect
import Mathematica.Translate
import Mathematica.Wire
import Std.Sync.Mutex

open Lean Lean.Meta

namespace Mathematica

/-! ### String escaping -/

/-- `\` → `\\` (port of `escape_slash`); used when embedding a path in a command. -/
def escapeSlash (s : String) : String :=
  s.foldl (fun acc c => if c == '\\' then acc ++ "\\\\" else acc.push c) ""

/-! ### Transport -/

/-- How Lean reaches a Mathematica kernel: given a Mathematica command, return the
    raw `OutputFormat`-serialised wire response.  `global` requests the persistent
    context (only `persistentKernel` distinguishes it). -/
structure Transport where
  send : (cmd : String) → (global : Bool) → IO String

/-- A test transport returning a fixed response, ignoring the command — exercises
    the full reflect → send → parse → translate path with no kernel. -/
def mockTransport (response : String) : Transport :=
  { send := fun _ _ => pure response }

/-- Stateless transport: a fresh `wolframscript -code` per call, loading
    `lean_form.wl` and printing `OutputFormat[cmd]`.  Simple, but spawns a kernel
    per call (slower; parallel calls can exceed a concurrent-kernel license limit).
    `global` is ignored. -/
def Transport.wolframScript (wolframscript leanFormPath : String) : Transport :=
  { send := fun cmd _global => do
      let code := "Get[\"" ++ leanFormPath ++ "\"]; OutputFormat[" ++ cmd ++ "]"
      let out ← IO.Process.output { cmd := wolframscript, args := #["-code", code] }
      if out.exitCode != 0 then
        throw (IO.userError s!"wolframscript exited with code {out.exitCode}: {out.stderr}")
      return out.stdout }   -- trailing newline is tolerated by Wire.parse

/-- Read a persistent kernel's stdout until the `<MME>` end-marker, returning the
    payload between `<MMS>` and `<MME>` (any pre-marker echo is discarded). -/
private partial def readUntilMarker (h : IO.FS.Handle) (acc : String) : IO String := do
  let line ← h.getLine
  if line.isEmpty then throw (IO.userError "WolframKernel closed its output unexpectedly")
  let acc := acc ++ line
  if (acc.splitOn "<MME>").length > 1 then
    return (((acc.splitOn "<MMS>").getLast!).splitOn "<MME>").head!
  else readUntilMarker h acc

/-- Persistent transport (the default; the reason no Python is needed): spawn one
    long-lived `WolframKernel -noprompt`, load `lean_form.wl` once, and drive it over
    stdin/stdout.  Each command asks the kernel to print `<MMS>…wire…<MME>`; a mutex
    serialises access so Lean's parallel elaboration is safe.  One kernel ⇒ one
    license checkout and no per-call startup. -/
def Transport.persistentKernel (kernelPath leanFormPath : String) : IO Transport := do
  let child ← IO.Process.spawn
    { cmd := kernelPath, args := #["-noprompt"],
      stdin := .piped, stdout := .piped, stderr := .null }
  let hin := child.stdin
  let hout := child.stdout
  hin.putStr ("Get[\"" ++ leanFormPath ++ "\"];\n")
  hin.flush
  let lock ← Std.Mutex.new ()
  return { send := fun cmd _global => lock.atomically do
    hin.putStr ("WriteString[\"stdout\",\"<MMS>\"<>OutputFormat[" ++ cmd ++ "]<>\"<MME>\\n\"]\n")
    hin.flush
    readUntilMarker hout "" }

/-! ### Execute -/

/-- Send `cmd` to Mathematica, return the raw wire response (port of `execute`). -/
def executeRaw (t : Transport) (cmd : String) (global : Bool := false) : IO String :=
  t.send cmd global

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

/-- `runCommandOn2` but importing `path` first (port of `run_command_on_2_using`). -/
def runCommandOn2Using (t : Transport) (cmd : String → String → String) (e₁ e₂ : Expr)
    (searchDir path : String) : MetaM Expr :=
  let getCmd := escapeSlash (mkGetCmd searchDir path)
  runCommandOn2 t (fun s₁ s₂ => getCmd ++ cmd s₁ s₂) e₁ e₂

/-- `runCommandOnList` but importing `path` first (port of `run_command_on_list_using`). -/
def runCommandOnListUsing (t : Transport) (cmd : String → String) (es : List Expr)
    (searchDir path : String) : MetaM Expr :=
  let getCmd := escapeSlash (mkGetCmd searchDir path)
  runCommandOnList t (fun s => getCmd ++ cmd s) es

/-- Load a Mathematica file into the global context (port of `load_file`). -/
def loadFile (t : Transport) (searchDir path : String) : IO Unit := do
  let _ ← executeRaw t (mkGetCmd searchDir path) (global := true)
  pure ()

/-- Evaluate a *raw* Mathematica command and translate the result to an `Expr` —
    no Lean input is reflected.  E.g. `evalMathematica t "Prime[100]"` gives the
    100th prime as a Lean numeral. -/
def evalMathematica (t : Transport) (cmd : String) : MetaM Expr := do
  exprOfMMExpr [] (← executeAndEval t cmd)

/-! ### The `mathematica_simp` tactic -/

/-- Oracle: trust Mathematica.  From a proof of `P'` (the kernel's simplification
    of the goal `P`) conclude `P`.  This is logically **unsound** in general — it
    trusts an external kernel — and appears in `#print axioms`.  For exploration,
    not for trusted proofs. -/
axiom trust {P : Prop} (P' : Prop) (h : P') : P

/-- The single persistent kernel, spawned lazily on first use and reused. -/
initialize kernelRef : IO.Ref (Option Transport) ← IO.mkRef none
/-- Serialises the lazy spawn of `kernelRef`. -/
initialize kernelLock : Std.Mutex Unit ← Std.Mutex.new ()

/-- The default transport: one persistent `WolframKernel`, spawned on first use and
    reused thereafter.  Configure via `MATHEMATICA_BRIDGE_KERNEL` (path to
    `WolframKernel`; defaults to the standard macOS location) and
    `MATHEMATICA_BRIDGE_LEANFORM` (absolute path to `wolfram/lean_form.wl`). -/
def defaultTransport : IO Transport := kernelLock.atomically do
  match ← kernelRef.get with
  | some t => return t
  | none =>
    let kernel := (← IO.getEnv "MATHEMATICA_BRIDGE_KERNEL").getD
      "/Applications/Wolfram.app/Contents/MacOS/WolframKernel"
    let some lf ← IO.getEnv "MATHEMATICA_BRIDGE_LEANFORM"
      | throw (IO.userError
          "set MATHEMATICA_BRIDGE_LEANFORM to the absolute path of wolfram/lean_form.wl")
    let t ← Transport.persistentKernel kernel lf
    kernelRef.set (some t)
    return t

open Lean.Elab.Tactic in
/-- `mathematica_simp` reflects the goal, asks Mathematica to `FullSimplify` it,
    and replaces the goal with the resulting proposition — closing it outright if
    Mathematica returns `True`.  Trusts the kernel via the `Mathematica.trust`
    oracle axiom (see `#print axioms`).  Configure the kernel via the
    `MATHEMATICA_BRIDGE_*` environment variables (see `defaultTransport`). -/
elab "mathematica_simp" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  unless ← isProp goalType do
    throwError "mathematica_simp: the goal is not a proposition"
  let t ← defaultTransport
  let simplified ← runCommandOn t (fun s => "Activate[LeanForm[" ++ s ++ "]] // FullSimplify") goalType
  unless ← isProp simplified do
    throwError m!"mathematica_simp: Mathematica's result is not a proposition:{indentExpr simplified}"
  if ← isDefEq simplified (mkConst ``True) then
    goal.assign (mkApp3 (mkConst ``trust) goalType (mkConst ``True) (mkConst ``True.intro))
    replaceMainGoal []
  else
    let newGoal ← mkFreshExprMVar simplified
    goal.assign (mkApp3 (mkConst ``trust) goalType simplified newGoal)
    replaceMainGoal [newGoal.mvarId!]

/-! ## Tests -/

#eval show MetaM Unit from do
  let assert (lbl : String) (b : Bool) : MetaM Unit := unless b do throwError m!"{lbl}: failed"
  -- pure protocol helpers
  assert "escapeSlash"  (escapeSlash "a\\b" == "a\\\\b")
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
