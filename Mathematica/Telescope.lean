/-
`mathematica_telescope` — automating the creative-telescoping case study.

For a binomial sum identity `∑_{k=0}^{n} C(n,k)^p = …`, this **fetches the WZ
certificate through the bridge** (`WZCert`, defined in `wolfram/lean_form.wl`) — the
recurrence coefficients and the rational certificate `R(n,k)` — reports it, and closes
the goal.

Honest scope (v1): generating a boundary-correct telescoping *proof term* from an
arbitrary fetched `R` is a research-grade build (the boundary handling in
`examples/CreativeTelescoping.lean` L1b was binomial-specific).  So this v1 wires up
the **discovery** (certificate fetched live via the bridge, at tactic time) and closes
the supported family (`p = 1, 2`) via the corresponding library lemma.  The sound
certificate *verification* is `wz_cert` in the case-study file; turning a fetched `R`
into an auto-generated closed-form proof is the remaining step (see the design notes).
-/
import Mathematica.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace Mathematica

/-- Recognise a summand `fun k => n.choose k` (`p = 1`) or `fun k => (n.choose k)^2`
    (`p = 2`); returns the power. -/
private def choosePow (f : Expr) : Option Nat :=
  match f with
  | .lam _ _ body _ =>
      if body.isAppOf ``Nat.choose then some 1
      else if body.isAppOf ``HPow.hPow then
        let a := body.getAppArgs
        if a.size ≥ 6 && a[4]!.isAppOf ``Nat.choose then
          match a[5]!.nat? with | some 2 => some 2 | _ => none
        else none
      else none
  | _ => none

elab "mathematica_telescope" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let some (_, lhs, _) := (← goal.getType).eq?
      | throwError "mathematica_telescope: expected a sum identity `∑ … = …`"
    let (fn, args) := lhs.getAppFnArgs
    unless fn == ``Finset.sum && args.size == 5 do
      throwError "mathematica_telescope: LHS is not a `Finset.sum`"
    let some p := choosePow args[4]!
      | throwError "mathematica_telescope: unsupported summand (expected `C(n,k)` or `C(n,k)^2`)"
    -- fetch the certificate through the bridge
    let t ← defaultTransport
    let cmd := "ToString[InputForm[WZCert[Function[{a, b}, Binomial[a, b]^"
      ++ toString p ++ "], n, k]]]"
    let cert ← executeAndEval t cmd
    let certStr := match cert with | .str s => s | other => toString other
    logInfo m!"mathematica_telescope: WZCert[C(n,k)^{p}] ⇒ {certStr}\n\
      (recurrence coefficients a0(n), a1(n) and certificate R(n,k), found live via the bridge)"
    -- close via the family lemma
    match p with
    | 1 => evalTactic (← `(tactic| exact Nat.sum_range_choose _))
    | 2 => evalTactic (← `(tactic| exact Nat.sum_range_choose_sq _))
    | _ => throwError "mathematica_telescope: unsupported power {p}"

end Mathematica
