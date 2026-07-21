/-
P0 spike — `lean-verify`, the reverse bridge's Lean-side verification service.

See `docs/REVERSE_BRIDGE_DESIGN.md`. This is the smallest thing that proves the
path end to end: mathlib is imported **once** at startup, then the process reads
one wire-form claim per line on stdin, turns it into a Lean `Prop` through the
*existing* `Wire.parse` → `exprOfMMExpr` translation, tries a small proving
pipeline, **adds the proof to the kernel** (so the verdict is genuinely
kernel-checked), and prints a verdict with the axiom set — which for a real proof
is `[propext, Classical.choice, Quot.sound]`, with no `Mathematica.trust`.

Line-framed rather than `<MMS>…<MME>`-framed so it can be driven straight from a
shell pipe (`echo … | lean_verify`). Pipeline: `intros` then `decide` / `omega` /
`rfl` — core/builtin tactics only, since imported mathlib `elab` tactics don't
dispatch in a standalone `importModules` process (see `proveTactics` and the P0
notes in `docs/REVERSE_BRIDGE_DESIGN.md`). A claim whose negation is provable comes
back `REFUTED`; one nothing proves comes back `UNKNOWN` (never a false `REFUTED`).
That is the whole spike; the richer (frontend-hosted) pipeline, `<MMS>` framing, and
the Mathematica-side paclet are later phases.
-/
import Mathematica.Wire
import Mathematica.Translate
import Mathlib.Data.Real.Basic

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic Mathematica

namespace Reverse

/-- A verdict for one claim. `status ∈ {VERIFIED, REFUTED, UNKNOWN, ERROR}`. -/
structure Verdict where
  status : String
  detail : String := ""

def Verdict.line (v : Verdict) : String :=
  if v.detail.isEmpty then v.status else s!"{v.status} {v.detail}"

/-- The proving pipeline: a display name and a tactic *source string*, tried in
    order.  `intros` first so a universally-quantified goal (`∀ n : ℕ, …`) becomes
    a bare goal.

    **Only core/builtin tactics** (`decide`, `omega`, `rfl`, …): these are compiled
    into the binary and dispatch reliably.  Imported mathlib `elab` tactics
    (`ring1`, `norm_num`, `nlinarith`) do NOT work in this standalone
    `importModules` process — the elaborator is found but its generated
    quotation-matcher throws `unsupportedSyntax` under the interpreter.  Hosting
    those is the job of the P1 service (see `docs/REVERSE_BRIDGE_DESIGN.md`). -/
def proveTactics : Array (String × String) :=
  #[ ("decide", "intros; decide"),
     ("omega",  "intros; omega"),
     ("rfl",    "intros; rfl") ]

/-- Try to close goal `P` with tactic source `tacSrc`; return the proof on success.
    The tactic is parsed with the *runtime* parser tables (populated by `loadExts`)
    so its syntax kind matches the runtime elaborator lookup — a compile-time
    quotation would bake in a kind the standalone process can't dispatch. -/
def proveWith (P : Expr) (tacSrc : String) : TermElabM (Option Expr) := do
  let stx ← match Lean.Parser.runParserCategory (← getEnv) `tactic s!"({tacSrc})" with
    | .ok stx => pure stx
    | .error _ => return none
  let mvar ← mkFreshExprMVar P
  try
    let remaining ← Lean.Elab.Tactic.run mvar.mvarId! (evalTactic stx)
    unless remaining.isEmpty do return none
    let e ← instantiateMVars mvar
    if e.hasExprMVar then return none
    return some e
  catch _ => return none

private def fmtAxioms (axs : Array Name) : String :=
  "[" ++ String.intercalate "," (axs.toList.map toString) ++ "]"

/-- Add the proof to the kernel (which re-checks it) and collect its axioms. -/
def certify (idx : Nat) (P proof : Expr) : TermElabM (Except String (Array Name)) := do
  let name := Name.mkSimple s!"_leanVerify_{idx}"
  try
    addDecl (.thmDecl { name, levelParams := [], type := P, value := proof })
    return .ok (← collectAxioms name)
  catch e => return .error (← (e.toMessageData).toString)

/-- Elaborate + verify one wire-form claim. -/
def verifyClaim (idx : Nat) (wire : String) : TermElabM Verdict := do
  match Wire.parse wire with
  | .error e => return { status := "ERROR", detail := s!"parse: {e}" }
  | .ok m =>
    let P ← try exprOfMMExpr [] m
      catch e => return { status := "ERROR", detail := s!"translate: {← e.toMessageData.toString}" }
    unless ← isProp P do
      return { status := "ERROR", detail := "translated claim is not a Prop" }
    for (nm, tac) in proveTactics do
      if let some proof ← proveWith P tac then
        match ← certify idx P proof with
        | .ok axs   => return { status := "VERIFIED", detail := s!"by={nm} axioms={fmtAxioms axs}" }
        | .error e  => return { status := "ERROR", detail := s!"kernel rejected proof: {e}" }
    -- nothing proved P; is P refutable (¬P provable)?
    let notP ← mkAppM ``Not #[P]
    for (nm, tac) in proveTactics do
      if let some _ ← proveWith notP tac then
        return { status := "REFUTED", detail := s!"by=¬·{nm}" }
    return { status := "UNKNOWN" }

/-- Run a `TermElabM` action against `env`/`state`, returning the value and the
    updated core state (so kernel-added theorems persist across claims). -/
def runOnce {α : Type} (ctx : Core.Context) (st : Core.State) (x : TermElabM α) :
    IO (α × Core.State) :=
  (MetaM.run' (TermElabM.run' x)).toIO ctx st

end Reverse

open Reverse in
/-- Entry point: mathlib imported once, then a read → verify → print loop. -/
unsafe def main (_args : List String) : IO Unit := do
  -- `loadExts := true` populates the env extensions (instance discrimination tree,
  -- simp sets, tactic elaborators, …); without it TC synthesis finds no instances.
  -- It runs interpreter code, so `enableInitializersExecution` must precede it.
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let imports : Array Import := #[
    { module := `Mathematica.Wire }, { module := `Mathematica.Translate },
    { module := `Mathlib.Data.Real.Basic } ]
  let env ← importModules imports {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<lean-verify>", fileMap := default }
  let mut st : Core.State := { env }
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut idx := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break            -- EOF (getLine returns "" only at EOF)
    -- skip blank lines; otherwise pass the line through verbatim — `Wire.parse`
    -- normalises the trailing newline itself, so no (deprecated) trim is needed.
    if line.all (fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t') then continue
    let (v, st') ← runOnce ctx st (verifyClaim idx line)
    stdout.putStrLn v.line
    stdout.flush
    st := st'
    idx := idx + 1
