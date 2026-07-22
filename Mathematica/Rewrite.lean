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

@[tactic mmRw]
def elabMmRw : Tactic := fun stx => do
  let cmd : String := match stx with
    | `(tactic| mathematica_rw $s:str) => s.getString
    | _ => "Simplify"
  let goal ← getMainGoal
  goal.withContext do
    let some (_, a, b) := (← goal.getType).eq?
      | throwError "mathematica_rw: expected an equality goal `a = b`"
    let ty ← inferType a
    let t ← defaultTransport
    let some a' ← mmSimplifyAt t cmd a ty
      | throwError "mathematica_rw: could not render Mathematica's LHS simplification"
    let some b' ← mmSimplifyAt t cmd b ty
      | throwError "mathematica_rw: could not render Mathematica's RHS simplification"
    let some pa ← validateEq a a'
      | throwError m!"mathematica_rw: could not validate the LHS step:{indentExpr a}\n  ⇝{indentExpr a'}"
    let some pb ← validateEq b b'
      | throwError m!"mathematica_rw: could not validate the RHS step:{indentExpr b}\n  ⇝{indentExpr b'}"
    match ← validateEq a' b' with
    | some pab =>
        goal.assign (← mkEqTrans pa (← mkEqTrans pab (← mkEqSymm pb)))
        replaceMainGoal []
    | none =>
        let mv ← mkFreshExprMVar (← mkEq a' b')
        goal.assign (← mkEqTrans pa (← mkEqTrans mv (← mkEqSymm pb)))
        replaceMainGoal [mv.mvarId!]

end Mathematica
