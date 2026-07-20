/-
The translation engine: `MMExpr → MetaM Expr`.  Port of `expr_of_mmexpr` /
`pexpr_of_mmexpr` and the translation-rule instances from the Lean 3
`mathematica.lean`.

Design notes (MIGRATION.md §5–§7):
  · Lean 4 has one `Expr`; the Lean 3 pexpr/expr split disappears.  The Lean 3
    "pexpr" rules (which produced under-specified pre-terms for elaboration to
    finish) are realised here with `mkAppM`, which infers implicit type/instance
    arguments and synthesises instances — the same job elaboration did.  So no
    Qq is needed for these rule bodies.
  · Binder rules (Function/ForAll/Exists) are `MetaM` telescopes
    (`withLocalDeclD` + `mkLambdaFVars`/`mkForallFVars`), replacing the Lean 3
    `local_const`-placeholder juggling.
  · The bound-variable environment (Lean 3 `trans_env`) is a small assoc list:
    Mathematica symbol → the `fvar` a binder introduced for it.

For now the rule set is built in (a fixed table).  The Lean 3 *extensibility*
(user-tagged rules via `@[app_to_..._rule]`) maps to Lean 4 environment
extensions + attributes; that layer is a follow-up and does not change this
dispatcher.

Two Lean 3 bugs fixed while porting:
  · `LeanPi` now builds `.forallE` (Lean 3 `mmexpr_pi_to_expr` built a `lam`).
  · `LeanLevelParam`/`Meta` args parsed as names (see `Unreflect.lean`).
-/
import Lean
import Mathematica.MMExpr
import Mathematica.Unreflect

open Lean Lean.Meta

namespace Mathematica

/-- Bound-variable environment: Mathematica symbol → the `fvar` standing for it
    (introduced by a binder rule).  Small, so a plain assoc list. -/
abbrev TransEnv := List (String × Expr)

private def fromExcept {α} : Except String α → MetaM α
  | .ok a    => pure a
  | .error e => throwError e

/-- Build a `Name` from a dotted string ("Nat.succ" → ``Nat.succ). -/
private def strToName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n part => if part.isEmpty then n else .str n part) .anonymous

/-- Left-fold a binary operator over args (port of `pexpr_fold_op`):
    `[]→dflt`, `[x]→x`, `x::xs → ((x⊕y₁)⊕y₂)…`. -/
private def foldBinL (op : Name) (dflt : Expr) : List Expr → MetaM Expr
  | []      => pure dflt
  | x :: xs => xs.foldlM (fun acc y => mkAppM op #[acc, y]) x

/-- Symbol rules that translate to a bare constant / sort (port of the simpler
    `sym_to_pexpr`/`sym_to_expr` rules). -/
private def symConst : String → Option (MetaM Expr)
  | "Type"  => some (pure (.sort (.succ .zero)))   -- Type 0 = Sort 1
  | "Prop"  => some (pure (.sort .zero))
  | "True"  => some (pure (mkConst ``True))
  | "False" => some (pure (mkConst ``False))
  | _       => none

/-- `F[…, Hold[p,q], …] = F[…, p, q, …]` (port of `app_mvar_hold_to_pexpr`). -/
private def flattenHold (args : List MMExpr) : List MMExpr :=
  args.flatMap fun
    | .app (.sym "Hold") hs => hs
    | a                     => [a]

/-- Translate a Mathematica expression to a Lean `Expr`. -/
partial def exprOfMMExpr (env : TransEnv) (m : MMExpr) : MetaM Expr := do
  match m with
  | .str s  => pure (mkStrLit s)
  | .int i  => pure (if i ≥ 0 then mkNatLit i.toNat else toExpr i)
  | .real _ => throwError "Mathematica reals are not yet supported"
  | .sym s  =>
      match env.lookup s with
      | some e => pure e
      | none =>
        match symConst s with
        | some mk => mk
        | none =>
          let n := strToName s
          if (← getEnv).contains n then mkConstWithFreshMVarLevels n
          else throwError s!"no translation for symbol '{s}'"
  | .app hd rawArgs =>
      let args := flattenHold rawArgs
      match hd with
      | .app (.sym "Inactive") [t] => exprOfMMExpr env (.app t args)   -- Inactive[t][…] = t[…]
      | .sym s => appSym env s args
      | _ =>
          let f ← exprOfMMExpr env hd
          let as ← args.mapM (exprOfMMExpr env)
          mkAppM' f as.toArray
where
  /-- Dispatch a symbol-headed application `s[args]`. -/
  appSym (env : TransEnv) (s : String) (args : List MMExpr) : MetaM Expr := do
    let tr := exprOfMMExpr env
    match s with
    -- raw unreflection: inverse of `Reflect.formatExpr`
    | "LeanVar" => match args with
        | [.int i] => pure (.bvar i.toNat)
        | _        => throwError "LeanVar: expected [int]"
    | "LeanSort" => match args with
        | [l] => pure (.sort (← fromExcept (levelOfMMExpr l)))
        | _   => throwError "LeanSort: expected [level]"
    | "LeanConst" => match args with
        | [nm, ls] => pure (.const (← fromExcept (nameOfMMExpr nm)) (← fromExcept (levelListOfMMExpr ls)))
        | _        => throwError "LeanConst: expected [name, levels]"
    | "LeanApp" => match args with
        | [f, a] => pure (.app (← tr f) (← tr a))
        | _      => throwError "LeanApp: expected [fn, arg]"
    | "LeanLambda" => match args with
        | [nm, bi, tp, bd] =>
            pure (.lam (← fromExcept (nameOfMMExpr nm)) (← tr tp) (← tr bd) (← fromExcept (binderInfoOfMMExpr bi)))
        | _ => throwError "LeanLambda: expected [name, binderInfo, type, body]"
    | "LeanPi" => match args with
        | [nm, bi, tp, bd] =>   -- Lean 3 bug: built `lam`; correct is `forallE`
            pure (.forallE (← fromExcept (nameOfMMExpr nm)) (← tr tp) (← tr bd) (← fromExcept (binderInfoOfMMExpr bi)))
        | _ => throwError "LeanPi: expected [name, binderInfo, type, body]"
    | "LeanLocal" => match args with
        | [nm, _, _, _] => pure (.fvar ⟨← fromExcept (nameOfMMExpr nm)⟩)   -- id reconstructs the fvar
        | _ => throwError "LeanLocal: expected [name, ppname, binderInfo, type]"
    | "LeanMetaVar" => match args with
        | [nm, _] => pure (.mvar ⟨← fromExcept (nameOfMMExpr nm)⟩)
        | _       => throwError "LeanMetaVar: expected [name, type]"
    | "LeanLitNat" => match args with
        | [.int n] => pure (mkNatLit n.toNat)
        | _        => throwError "LeanLitNat: expected [int]"
    | "LeanLitStr" => match args with
        | [.str str] => pure (mkStrLit str)
        | _          => throwError "LeanLitStr: expected [string]"
    | "LeanProj" => match args with
        | [tp, .int i, s'] => pure (.proj (← fromExcept (nameOfMMExpr tp)) i.toNat (← tr s'))
        | _                => throwError "LeanProj: expected [type, idx, struct]"
    -- arithmetic / logic / comparison (semantic rules; `mkAppM` fills implicits+instances)
    | "Plus"     => foldBinL ``HAdd.hAdd (mkNatLit 0) (← args.mapM tr)
    | "Times"    => foldBinL ``HMul.hMul (mkNatLit 1) (← args.mapM tr)
    | "And"      => foldBinL ``And (mkConst ``True) (← args.mapM tr)
    | "Or"       => foldBinL ``Or (mkConst ``False) (← args.mapM tr)
    | "Power"    => match args with
        | [b, e] => mkAppM ``HPow.hPow #[← tr b, ← tr e]
        | _      => throwError "Power: expected [base, exp]"
    | "Rational" => match args with
        | [p, q] => mkAppM ``HDiv.hDiv #[← tr p, ← tr q]
        | _      => throwError "Rational: expected [num, den]"
    | "Equal"    => match args with
        | [a, b] => mkAppM ``Eq #[← tr a, ← tr b]
        | _      => throwError "Equal: expected [a, b]"
    | "Less"     => match args with
        | [a, b] => mkAppM ``LT.lt #[← tr a, ← tr b]
        | _      => throwError "Less: expected [a, b]"
    | "LessEqual" => match args with
        | [a, b] => mkAppM ``LE.le #[← tr a, ← tr b]
        | _      => throwError "LessEqual: expected [a, b]"
    | "Greater"  => match args with           -- a > b  ≡  b < a  (avoids needing a GT instance)
        | [a, b] => mkAppM ``LT.lt #[← tr b, ← tr a]
        | _      => throwError "Greater: expected [a, b]"
    | "GreaterEqual" => match args with       -- a ≥ b  ≡  b ≤ a
        | [a, b] => mkAppM ``LE.le #[← tr b, ← tr a]
        | _      => throwError "GreaterEqual: expected [a, b]"
    | "Not"      => match args with
        | [a] => mkAppM ``Not #[← tr a]
        | _   => throwError "Not: expected [a]"
    | "Implies"  => match args with
        | [h, c] => mkArrow (← tr h) (← tr c)
        | _      => throwError "Implies: expected [hyp, concl]"
    | "List"     => do
        let es ← args.mapM tr
        match es with
        | [] =>   -- empty list: element type is genuinely unknown, so leave a mvar
            let u ← mkFreshLevelMVar
            let α ← mkFreshExprMVar (some (.sort u))
            pure (mkApp (.const ``List.nil [u]) α)
        | e0 :: _ =>   -- element type is concrete (from the first element)
            let nil ← mkAppOptM ``List.nil #[some (← inferType e0)]
            es.foldrM (fun h t => mkAppM ``List.cons #[h, t]) nil
    | "Hold"     => match args with
        | [a] => tr a
        | _   => throwError "Hold: expected [a] (multi-arg Hold is flattened in argument position)"
    -- binders (MetaM telescopes; multi-binder List forms desugar to nested singles)
    | "Function" => match args with
        | [.sym x, body] =>
            withLocalDeclD (.mkSimple x) (← mkFreshTypeMVar) fun fv => do
              mkLambdaFVars #[fv] (← exprOfMMExpr ((x, fv) :: env) body)
        | [.app (.sym "List") [], body] => tr body
        | [.app (.sym "List") (v :: vs), body] =>
            tr (.app (.sym "Function") [v, .app (.sym "Function") [.app (.sym "List") vs, body]])
        | _ => throwError "Function: expected [var|List[vars], body]"
    | "ForAll" => match args with
        | [.sym x, body] =>
            withLocalDeclD (.mkSimple x) (← mkFreshTypeMVar) fun fv => do
              mkForallFVars #[fv] (← exprOfMMExpr ((x, fv) :: env) body)
        | [.sym x, t, body] =>   -- ∀ x, t → body
            withLocalDeclD (.mkSimple x) (← mkFreshTypeMVar) fun fv => do
              mkForallFVars #[fv] (← exprOfMMExpr ((x, fv) :: env) (.app (.sym "Implies") [t, body]))
        | [.app (.sym "List") [], body] => tr body
        | [.app (.sym "List") (v :: vs), body] =>
            tr (.app (.sym "ForAll") [v, .app (.sym "ForAll") [.app (.sym "List") vs, body]])
        | _ => throwError "ForAll: expected [var|List[vars], body] or [var, hyp, body]"
    | "ForAllTyped" => match args with
        | [.sym x, t, body] =>
            withLocalDeclD (.mkSimple x) (← tr t) fun fv => do
              mkForallFVars #[fv] (← exprOfMMExpr ((x, fv) :: env) body)
        | [.app (.sym "List") [], _, body] => tr body
        | [.app (.sym "List") (v :: vs), t, body] =>
            tr (.app (.sym "ForAllTyped") [v, t, .app (.sym "ForAllTyped") [.app (.sym "List") vs, t, body]])
        | _ => throwError "ForAllTyped: expected [var|List[vars], type, body]"
    | "Exists" => match args with
        | [.sym x, body] =>
            -- untyped binder ⇒ domain type is a placeholder mvar; build @Exists
            -- manually since `mkAppM` rejects a result that still has mvars.
            let α ← mkFreshTypeMVar
            let lam ← withLocalDeclD (.mkSimple x) α fun fv => do
              mkLambdaFVars #[fv] (← exprOfMMExpr ((x, fv) :: env) body)
            pure (mkApp2 (.const ``Exists [← getDecLevel α]) α lam)
        | [.app (.sym "List") [], body] => tr body
        | [.app (.sym "List") (h :: t), body] =>
            tr (.app (.sym "Exists") [h, .app (.sym "Exists") [.app (.sym "List") t, body]])
        | _ => throwError "Exists: expected [var|List[vars], body]"
    -- fallback: translate the head symbol (bound var / sym-const / global name), then apply
    | _ =>
        let f ← exprOfMMExpr env (.sym s)
        let as ← args.mapM tr
        mkAppM' f as.toArray

/-! ## Tests (run at build time via `#eval`; a thrown error fails the build) -/

section Tests

open MMExpr in
private def anon : MMExpr := .sym "LeanNameAnonymous"
/-- A simple (single-segment) reflected `Name`. -/
private def nmMM (s : String) : MMExpr := .app (.sym "LeanNameMkString") [.str s, anon]
/-- A two-segment reflected `Name`, e.g. `nm2 "Nat" "succ"` = `Nat.succ`. -/
private def nm2MM (a b : String) : MMExpr :=
  .app (.sym "LeanNameMkString") [.str b, .app (.sym "LeanNameMkString") [.str a, anon]]
private def nilLvls : MMExpr := .sym "LeanLevelListNil"
private def leanConstMM (name lvls : MMExpr) : MMExpr := .app (.sym "LeanConst") [name, lvls]

#eval show MetaM Unit from do
  let assert (lbl : String) (b : Bool) : MetaM Unit :=
    unless b do throwError m!"{lbl}: failed"
  let assertEq (lbl : String) (got want : Expr) : MetaM Unit :=
    unless got == want do throwError m!"{lbl}: got {got}, want {want}"
  let head (lbl : String) (e : Expr) (n : Name) : MetaM Unit :=
    unless e.isAppOf n do throwError m!"{lbl}: {e} is not an application of {n}"
  let isConst (lbl : String) (e : Expr) (n : Name) : MetaM Unit :=
    unless e.isConstOf n do throwError m!"{lbl}: {e} is not the constant {n}"
  let natC := leanConstMM (nmMM "Nat") nilLvls
  let eqXX : MMExpr := .app (.sym "Equal") [.sym "x", .sym "x"]
  -- raw unreflection round-trips
  assertEq "raw: LeanConst Nat" (← exprOfMMExpr [] natC) (mkConst ``Nat)
  assertEq "raw: LeanConst Nat.succ"
    (← exprOfMMExpr [] (leanConstMM (nm2MM "Nat" "succ") nilLvls)) (mkConst ``Nat.succ)
  assertEq "raw: LeanApp"
    (← exprOfMMExpr [] (.app (.sym "LeanApp") [leanConstMM (nm2MM "Nat" "succ") nilLvls, .app (.sym "LeanVar") [.int 0]]))
    (.app (mkConst ``Nat.succ) (.bvar 0))
  assertEq "raw: LeanLambda"
    (← exprOfMMExpr [] (.app (.sym "LeanLambda") [nmMM "x", .sym "BinderInfoDefault", natC, .app (.sym "LeanVar") [.int 0]]))
    (.lam `x (mkConst ``Nat) (.bvar 0) .default)
  -- LeanPi must build forallE, not lam (the fixed Lean 3 bug)
  let piE ← exprOfMMExpr [] (.app (.sym "LeanPi") [nmMM "x", .sym "BinderInfoDefault", natC, .app (.sym "LeanVar") [.int 0]])
  assertEq "raw: LeanPi (bug fix)" piE (.forallE `x (mkConst ``Nat) (.bvar 0) .default)
  assert "raw: LeanPi is forall" piE.isForall
  -- semantic rules
  assert "sem: Plus defeq 1+2"
    (← isDefEq (← exprOfMMExpr [] (.app (.sym "Plus") [.int 1, .int 2])) (← mkAppM ``HAdd.hAdd #[mkNatLit 1, mkNatLit 2]))
  head "sem: Times" (← exprOfMMExpr [] (.app (.sym "Times") [.int 2, .int 3])) ``HMul.hMul
  head "sem: Power" (← exprOfMMExpr [] (.app (.sym "Power") [.int 2, .int 3])) ``HPow.hPow
  head "sem: Equal" (← exprOfMMExpr [] (.app (.sym "Equal") [.int 1, .int 1])) ``Eq
  head "sem: Less"  (← exprOfMMExpr [] (.app (.sym "Less") [.int 1, .int 2])) ``LT.lt
  head "sem: List"  (← exprOfMMExpr [] (.app (.sym "List") [.int 1, .int 2])) ``List.cons
  let eqMM : MMExpr := .app (.sym "Equal") [.int 1, .int 1]
  head "sem: And" (← exprOfMMExpr [] (.app (.sym "And") [eqMM, eqMM])) ``And
  assert "sem: Implies is arrow" (← exprOfMMExpr [] (.app (.sym "Implies") [eqMM, eqMM])).isForall
  -- Hold flattening: Plus[Hold[1,2],3] = Plus[1,2,3]
  head "sem: Hold flatten"
    (← exprOfMMExpr [] (.app (.sym "Plus") [.app (.sym "Hold") [.int 1, .int 2], .int 3])) ``HAdd.hAdd
  -- binders
  assert "bind: Function is lam" (← exprOfMMExpr [] (.app (.sym "Function") [.sym "x", eqXX])).isLambda
  assert "bind: ForAll is forall" (← exprOfMMExpr [] (.app (.sym "ForAll") [.sym "x", eqXX])).isForall
  head "bind: Exists" (← exprOfMMExpr [] (.app (.sym "Exists") [.sym "x", eqXX])) ``Exists
  -- symbol resolution + decomposition
  isConst "sym: True const" (← exprOfMMExpr [] (.sym "True")) ``True
  isConst "sym: global name" (← exprOfMMExpr [] (.sym "Nat.succ")) ``Nat.succ
  head "sym: decomp apply" (← exprOfMMExpr [] (.app (.sym "Nat.succ") [.int 0])) ``Nat.succ

end Tests

end Mathematica
