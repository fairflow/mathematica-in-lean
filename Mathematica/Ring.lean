/-
Certificate mode — the `mathematica_ring` tactic.

`mathematica_simp` *trusts* Mathematica: it closes a goal through the
`Mathematica.trust` **axiom**, which then shows up in `#print axioms`.
`mathematica_ring` does **not**.  Mathematica only *discovers* a certificate — a
linear combination of the local equality hypotheses that reduces the goal to a
ring identity — and Lean's own `ring1` / `linear_combination` *checks* it.  The
resulting proof is fully kernel-verified; `Mathematica.trust` never enters it.

This is the Mathematica analogue of `polyrith` (Lewis, Wu, et al.): use an
external CAS to *find* a `linear_combination` certificate that Lean *verifies*.
The difference from `polyrith` is only the oracle — here the certificate comes
from Mathematica's `PolynomialReduce` (a Gröbner-basis reduction) rather than
Sage's linear algebra.

How a free variable survives the round trip: `wolfram/lean_form.wl` passes a
reflected `LeanLocal[…]` through unchanged, so to Mathematica each Lean variable
is just an opaque atom.  `PolynomialReduce` computes with those atoms, and the
coefficients it returns still mention them — so they reconstruct back to the
*exact same* Lean fvars (see `Translate`/`Reflect`).

Scope: goals `a = b` over a commutative ring — best over a field (ℝ, ℚ), since
`PolynomialReduce` may return rational coefficients.  Equality hypotheses
`h : p = q` in the local context (over the same type) become certificate
generators; with none, the goal must be a bare ring identity and `ring1` closes it.
-/
import Mathematica.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace Mathematica

private def fromExcept' {α} : Except String α → MetaM α
  | .ok a    => pure a
  | .error e => throwError e

/-- A local equality hypothesis `h : lhs = rhs`. -/
private structure EqHyp where
  fvar : FVarId
  lhs  : Expr
  rhs  : Expr

/-- The local hypotheses that are equalities `p = q` whose sides live in `ty`. -/
private def eqHyps (ty : Expr) : MetaM (Array EqHyp) := do
  let mut out := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if let some (α, p, q) := ldecl.type.eq? then
      if ← isDefEq α ty then
        out := out.push { fvar := ldecl.fvarId, lhs := p, rhs := q }
  return out

/-- Render a coefficient `MMExpr` (a polynomial in the goal's variables, as
    returned by `PolynomialReduce`) as a Lean **term** — kept syntactic so its
    numerals stay type-polymorphic and elaborate at the goal's ring.  Variables
    arrive as `LeanLocal[id, …]` atoms and become the fvar's own identifier. -/
private partial def coeffTerm (m : MMExpr) : MetaM (TSyntax `term) := do
  match m with
  | .int i =>
      let lit := Syntax.mkNumLit (toString i.natAbs)
      if i < 0 then `(-$lit) else `($lit)
  | .real _ => throwError "mathematica_ring: unexpected real coefficient"
  | .app (.sym "Rational") [p, q] => `($(← coeffTerm p) / $(← coeffTerm q))
  | .app (.sym "Power") [b, e]    => `($(← coeffTerm b) ^ $(← coeffTerm e))
  | .app (.sym "Subtract") [a, b] => `($(← coeffTerm a) - $(← coeffTerm b))
  | .app (.sym "Plus") (a :: rest) =>
      rest.foldlM (fun acc x => do `($acc + $(← coeffTerm x))) (← coeffTerm a)
  | .app (.sym "Times") (a :: rest) =>
      rest.foldlM (fun acc x => do `($acc * $(← coeffTerm x))) (← coeffTerm a)
  | .app (.sym "LeanLocal") (nm :: _) =>
      let fid : FVarId := ⟨← fromExcept' (nameOfMMExpr nm)⟩
      pure (mkIdent (← fid.getUserName))
  | .sym s => pure (mkIdent (Name.mkSimple s))
  | _ => throwError m!"mathematica_ring: cannot render coefficient as a Lean term: {toString m}"

/-- `mathematica_ring` proves an equality `a = b` over a commutative ring by
    asking Mathematica for a certificate and checking it in Lean — **soundly**,
    with no `Mathematica.trust` axiom (contrast `mathematica_simp`).

    With no equality hypotheses it closes a bare ring identity via `ring1`; with
    hypotheses `hᵢ : pᵢ = qᵢ` it asks `PolynomialReduce` for coefficients `cᵢ`
    with `a - b = Σ cᵢ (pᵢ - qᵢ)` and closes via `linear_combination Σ cᵢ * hᵢ`.
    Configure the kernel through the `MATHEMATICA_BRIDGE_*` env vars (see
    `defaultTransport`). -/
elab "mathematica_ring" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let goalType ← goal.getType
    let some (α, a, b) := goalType.eq?
      | throwError m!"mathematica_ring: the goal must be an equality `a = b`, got{indentExpr goalType}"
    let t ← defaultTransport
    let hyps ← eqHyps α
    -- Reflect the goal difference and each hypothesis difference; ask Mathematica
    -- to reduce d = a - b modulo the generators pᵢ - qᵢ.  LeanLocal atoms are
    -- swapped for fresh symbols for the reduction, then swapped back so the
    -- returned coefficients mention the original Lean variables.
    let dStr ← formatExpr (← mkAppM ``HSub.hSub #[a, b])
    let genStrs ← hyps.mapM fun h => do formatExpr (← mkAppM ``HSub.hSub #[h.lhs, h.rhs])
    let genList := "{" ++ String.intercalate ", " genStrs.toList ++ "}"
    let cmd :=
      "Module[{d = Activate[LeanForm[" ++ dStr ++ "]], " ++
             "gens = Activate[Map[LeanForm, " ++ genList ++ "]], atoms, syms, fwd, bwd}, " ++
        "atoms = DeleteDuplicates[Cases[Prepend[gens, d], _LeanLocal, {0, Infinity}]]; " ++
        "syms = Table[Unique[\"lv\"], {Length[atoms]}]; " ++
        "fwd = Thread[atoms -> syms]; bwd = Thread[syms -> atoms]; " ++
        "PolynomialReduce[d /. fwd, gens /. fwd, syms] /. bwd]"
    let res ← executeAndEval t cmd
    let (coeffMMs, remMM) ← match res with
      | .app (.sym "List") [.app (.sym "List") cs, rem] => pure (cs, rem)
      | _ => throwError m!"mathematica_ring: could not read a PolynomialReduce certificate \
              from Mathematica's response:{indentD (toString res)}"
    unless remMM == .int 0 do
      throwError m!"mathematica_ring: Mathematica could not reduce the goal to a ring \
        identity over the hypotheses (remainder {toString remMM} ≠ 0). If the goal is \
        nonetheless true it may need more hypotheses or lie outside `ring`'s equational \
        theory (e.g. trigonometric) — try `mathematica_simp`."
    if hyps.isEmpty then
      evalTactic (← `(tactic| ring1))
    else
      unless coeffMMs.length == hyps.size do
        throwError m!"mathematica_ring: certificate has {coeffMMs.length} coefficients \
          for {hyps.size} hypotheses"
      let mut terms : Array (TSyntax `term) := #[]
      for (cMM, h) in coeffMMs.zip hyps.toList do
        let cT ← coeffTerm cMM
        let hId := mkIdent (← h.fvar.getUserName)
        terms := terms.push (← `($cT * $hId))
      match terms[0]? with
      | none       => evalTactic (← `(tactic| ring1))
      | some first =>
          let combo ← (terms.toList.drop 1).foldlM (fun acc x => `($acc + $x)) first
          evalTactic (← `(tactic| linear_combination $combo:term))

/-! ## Tests (kernel-free: only the pure coefficient renderer) -/

#eval show MetaM Unit from do
  -- reprint keeps source-info spacing, so normalise whitespace before matching
  let render (m : MMExpr) : MetaM String := do
    pure (((← coeffTerm m).raw.reprint.getD "").replace " " "")
  let assertHas (lbl : String) (m : MMExpr) (needle : String) : MetaM Unit := do
    let s ← render m
    unless (s.splitOn (needle.replace " " "")).length > 1 do
      throwError m!"{lbl}: rendered {s}, expected to contain {needle}"
  -- 3 * x + 1  (bare symbols stand in for LeanLocal atoms here)
  let poly : MMExpr := .app (.sym "Plus")
    [.app (.sym "Times") [.int 3, .sym "x"], .int 1]
  assertHas "coeff: product" poly "3 * x"
  assertHas "coeff: sum"     poly "+ 1"
  -- -2 * x ^ 2
  let poly2 : MMExpr := .app (.sym "Times")
    [.int (-2), .app (.sym "Power") [.sym "x", .int 2]]
  assertHas "coeff: neg"   poly2 "-2"
  assertHas "coeff: power" poly2 "x ^ 2"
  -- rational 1/2
  assertHas "coeff: rational" (.app (.sym "Rational") [.int 1, .int 2]) "1 / 2"

end Mathematica
