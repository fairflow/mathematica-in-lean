/-
`mathematica_rw` — a **sound** Mathematica-assisted rewriting tactic.

Mathematica proposes, Lean disposes.  For an equality goal `a = b`, it asks
Mathematica to simplify each side, then *validates* each proposed simplification
with a Lean certificate tactic (`rfl` / `ring1` / `field_simp; ring1` / `norm_num` /
`simp`).  Only validated rewrites are used, so the proof is kernel-checked — **no
`Mathematica.trust` axiom** (contrast `mathematica_simp`).

Key detail: Mathematica's *result* is rendered to **term syntax** (numerals stay
polymorphic) and elaborated **at the goal side's type**, so `x^2 + 2*x + 1` comes
back as a real (not a `HAdd ℝ ℕ` type error) — the fix for the numeral-typing edge.

This is the general form of `mathematica_ring`: the CAS finds the normal form, Lean
proves the step; strictly more than `ring`, since it uses whichever validation tactic
fits each side and Mathematica can reach normal forms one Lean tactic would not.

Usage: `mathematica_rw` (uses `Simplify`) or `mathematica_rw "FullSimplify"` (any
Mathematica command: `Factor`, `Together`, …).  Closes the goal, or leaves the
simpler goal `a' = b'` if the two sides don't validate as equal.
-/
import Mathematica.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic

namespace Mathematica

private def fromExcept'' {α} : Except String α → MetaM α
  | .ok a => pure a | .error e => throwError e

/-- Render a Mathematica result `MMExpr` as a Lean **term** (numerals kept
    polymorphic; a reflected `LeanLocal[…]` becomes the fvar's identifier).  Returns
    `none` for anything outside the handled arithmetic/rational fragment, so an
    unrecognised result just makes the rewrite fail (soundly) rather than misfire. -/
private partial def mmToSyntax (m : MMExpr) : MetaM (Option (TSyntax `term)) := do
  match m with
  | .int i =>
      let lit := Syntax.mkNumLit (toString i.natAbs)
      let r ← if i < 0 then `(-$lit) else `($lit)
      return some r
  | .app (.sym "Rational") [p, q]  => bin p q (fun a b => `($a / $b))
  | .app (.sym "Divide")   [p, q]  => bin p q (fun a b => `($a / $b))
  | .app (.sym "Subtract") [p, q]  => bin p q (fun a b => `($a - $b))
  | .app (.sym "Power")    [p, .int e] =>
      if e ≥ 0 then
        match ← mmToSyntax p with
        | some a =>
            let lit := Syntax.mkNumLit (toString e.toNat)
            let r ← `($a ^ $lit)
            return some r
        | none => return none
      else return none
  | .app (.sym "Plus")  (x :: xs) => foldOp x xs (fun a b => `($a + $b))
  | .app (.sym "Times") (x :: xs) => foldOp x xs (fun a b => `($a * $b))
  | .app (.sym "LeanLocal") (nm :: _) =>
      let fid : FVarId := ⟨← fromExcept'' (nameOfMMExpr nm)⟩
      let un ← fid.getUserName
      return some (mkIdent un)
  | _ => return none
where
  bin (p q : MMExpr) (f : TSyntax `term → TSyntax `term → MetaM (TSyntax `term)) :
      MetaM (Option (TSyntax `term)) := do
    match ← mmToSyntax p, ← mmToSyntax q with
    | some a, some b => let r ← f a b; return some r
    | _, _ => return none
  foldOp (x : MMExpr) (xs : List MMExpr) (f : TSyntax `term → TSyntax `term → MetaM (TSyntax `term)) :
      MetaM (Option (TSyntax `term)) := do
    match ← mmToSyntax x with
    | none => return none
    | some a0 =>
        let mut acc := a0
        for y in xs do
          match ← mmToSyntax y with
          | none => return none
          | some b => acc ← f acc b
        return some acc

/-- Simplify `e` in Mathematica with `cmd`, then elaborate the result **at type
    `ty`** (so numerals get the right type).  `none` if it can't be rendered/typed. -/
def mmSimplifyAt (t : Transport) (cmd : String) (e ty : Expr) : TermElabM (Option Expr) := do
  let m ← executeAndEval t (cmd ++ "[Activate[LeanForm[" ++ (← formatExpr e) ++ "]]]")
  match ← mmToSyntax m with
  | none => return none
  | some stx =>
    try
      let e' ← elabTermEnsuringType stx (some ty)
      synthesizeSyntheticMVarsNoPostponing
      let e' ← instantiateMVars e'
      return if e'.hasExprMVar then none else some e'
    catch _ => return none

/-- Validation ladder: prove `lhs = rhs` with a certificate tactic, or `none`. -/
def validateEq (lhs rhs : Expr) : TermElabM (Option Expr) := do
  let eqType ← mkEq lhs rhs
  let tacs : List (TSyntax `tactic) :=
    [← `(tactic| rfl), ← `(tactic| ring1), ← `(tactic| (field_simp; ring1)),
     ← `(tactic| norm_num), ← `(tactic| simp)]
  for tac in tacs do
    let mvar ← mkFreshExprMVar eqType
    let ok ← (do
      let rem ← Lean.Elab.Tactic.run mvar.mvarId! (evalTactic tac)
      pure (rem.isEmpty && !(← instantiateMVars mvar).hasExprMVar)) <|> pure false
    if ok then return some (← instantiateMVars mvar)
  return none

syntax (name := mmRw) "mathematica_rw" (ppSpace str)? : tactic

/-! ### The fixed-point subterm loop

Pick a subterm, simplify it in Mathematica, validate the step, rewrite it in place,
and repeat until nothing changes.  "Guiding into a subterm" is `MVarId.rewrite`: given
a proof `sub = sub'` it `kabstract`s the occurrences of `sub` into the congruence
motive and rewrites — we only choose *which* subterm to try; the kernel does the rest. -/

/-- Data types Mathematica can meaningfully simplify (and the bridge can round-trip).
    Matched by name against the runtime env, so this module needn't import them. -/
private def isNumericType (τ : Expr) : MetaM Bool := do
  let env ← getEnv
  (([`Nat, `Int, `Rat, `Real] : List Name).filter env.contains).anyM
    fun n => isDefEq τ (mkConst n)

/-- All application-subterms of `e` (numeric-valued ones are the candidates). -/
private partial def collectApps : Expr → Array Expr → Array Expr := fun e acc =>
  let acc := if e.isApp then acc.push e else acc
  match e with
  | .app f a         => collectApps a (collectApps f acc)
  | .lam _ d b _     => collectApps b (collectApps d acc)
  | .forallE _ d b _ => collectApps b (collectApps d acc)
  | .letE _ d v b _  => collectApps b (collectApps v (collectApps d acc))
  | .mdata _ b       => collectApps b acc
  | .proj _ _ b      => collectApps b acc
  | _                => acc

/-- Candidate subterms, deduplicated and **largest first** (simplify big chunks before
    their parts — not aggressively optimal, just a sensible order). -/
private def candidates (e : Expr) : Array Expr :=
  ((collectApps e #[]).toList.eraseDups.toArray).qsort
    (fun a b => a.approxDepth > b.approxDepth)

/-- Try to simplify `sub` in Mathematica, validate the step, and rewrite it into the
    goal.  Returns whether it made progress.  Sound: only a validated equality is used. -/
private def tryRewriteSubterm (t : Transport) (cmd : String) (sub : Expr) : TacticM Bool := do
  let subTy ← inferType sub
  unless ← isNumericType subTy do return false
  let some sub' ← mmSimplifyAt t cmd sub subTy | return false
  if ← isDefEq sub sub' then return false
  let some pf ← validateEq sub sub' | return false
  let goal ← getMainGoal
  try
    let r ← goal.rewrite (← goal.getType) pf
    replaceMainGoal ((← goal.replaceTargetEq r.eNew r.eqProof) :: r.mvarIds)
    return true
  catch _ => return false

/-- One pass: rewrite the first subterm that makes progress. -/
private def rwOnePass (t : Transport) (cmd : String) : TacticM Bool := do
  for sub in candidates (← (← getMainGoal).getType) do
    if ← tryRewriteSubterm t cmd sub then return true
  return false

@[tactic mmRw]
def elabMmRw : Tactic := fun stx => do
  let cmd : String := match stx with
    | `(tactic| mathematica_rw $s:str) => s.getString
    | _ => "Simplify"
  let t ← defaultTransport
  -- fixed-point loop (step-capped for termination)
  let mut n := 0
  let mut changed := true
  while changed && n < 25 do
    changed ← (← getMainGoal).withContext (rwOnePass t cmd)
    n := n + 1
  -- best-effort close of whatever remains
  try evalTactic (← `(tactic|
        first | rfl | ring1 | (field_simp; ring1) | norm_num | simp | decide | omega))
  catch _ => pure ()

end Mathematica
