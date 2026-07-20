/-
Reflection: `Expr → String`, emitting the `Lean…[…]` head symbols the
Mathematica side (`src/lean_form.m`) pattern-matches on.  Port of
`form_of_name` / `form_of_lvl` / `form_of_lvl_list` / `form_of_binder_info` /
`form_of_expr` from the Lean 3 `mathematica.lean`.

Runs in `MetaM`: unlike Lean 3, a Lean 4 `Expr.fvar`/`.mvar` carries only an id
— the user name, binder info and type live in the local/metavar context — so
faithfully emitting `LeanLocal[n, pn, bi, tp]` / `LeanMetaVar[n, tp]` means
looking the declaration up (MIGRATION.md §4, §7).

Lean 4 constructors with no Lean 3 counterpart get faithful raw heads:
  · `.lit`   → `LeanLitNat[n]` / `LeanLitStr["s"]`   (native literals; the
              `bit0`/`bit1` towers are gone, MIGRATION.md §8 — the matching
              `LeanForm` rules on the `.m` side are the numeral work in phase 3)
  · `.proj`  → `LeanProj[type, idx, struct]`
  · `.mdata` → transparent (annotations are dropped)

Dependency-light on purpose: only `import Lean` (ships with the toolchain);
mathlib + Qq arrive with the translation layer.
-/
import Lean

open Lean Lean.Meta

namespace Mathematica

/-- Escape `"` and `\` so a string can sit inside a Mathematica string literal.
    (The Lean 3 code emitted raw strings; escaping is a correctness fix — for
    ordinary names with no special characters the output is unchanged.) -/
private def escapeMathematicaString (s : String) : String :=
  s.toList.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | _    => acc.push c

/-- Reflect a `Name` (port of `form_of_name`).  Wire order is string-first then
    parent, matching `lean_form.m`'s `LeanNameMkString[s, parent]`. -/
def formatName : Name → String
  | .anonymous => "LeanNameAnonymous"
  | .str p s   => s!"LeanNameMkString[\"{escapeMathematicaString s}\", {formatName p}]"
  | .num p i   => s!"LeanNameMkNum[{i}, {formatName p}]"

/-- Reflect a universe `Level` (port of `form_of_lvl`). -/
def formatLevel : Level → String
  | .zero       => "LeanZeroLevel"
  | .succ l     => s!"LeanLevelSucc[{formatLevel l}]"
  | .max l₁ l₂  => s!"LeanLevelMax[{formatLevel l₁}, {formatLevel l₂}]"
  | .imax l₁ l₂ => s!"LeanLevelIMax[{formatLevel l₁}, {formatLevel l₂}]"
  | .param nm   => s!"LeanLevelParam[{formatName nm}]"
  | .mvar id    => s!"LeanLevelMeta[{formatName id.name}]"

/-- Reflect a `List Level` (port of `form_of_lvl_list`). -/
def formatLevelList : List Level → String
  | []      => "LeanLevelListNil"
  | l :: ls => s!"LeanLevelListCons[{formatLevel l}, {formatLevelList ls}]"

/-- Reflect a `BinderInfo` (port of `form_of_binder_info`; Lean 4 has no
    `aux_decl`/"other" case). -/
def formatBinderInfo : BinderInfo → String
  | .default        => "BinderInfoDefault"
  | .implicit       => "BinderInfoImplicit"
  | .strictImplicit => "BinderInfoStrictImplicit"
  | .instImplicit   => "BinderInfoInstImplicit"

/-- Reflect an `Expr` into Mathematica head-symbol syntax (port of
    `form_of_expr`).  `let` is unfolded before translation (`expand_let`);
    `fvar`/`mvar` are resolved against the ambient context. -/
partial def formatExpr (e : Expr) : MetaM String := do
  match e with
  | .bvar i          => return s!"LeanVar[{i}]"
  | .sort l          => return s!"LeanSort[{formatLevel l}]"
  | .const nm us     => return s!"LeanConst[{formatName nm}, {formatLevelList us}]"
  | .lit (.natVal n) => return s!"LeanLitNat[{n}]"
  | .lit (.strVal s) => return s!"LeanLitStr[\"{escapeMathematicaString s}\"]"
  | .app f a =>
      let sf ← formatExpr f
      let sa ← formatExpr a
      return s!"LeanApp[{sf}, {sa}]"
  | .lam nm ty bd bi =>
      let sty ← formatExpr ty
      let sbd ← formatExpr bd
      return s!"LeanLambda[{formatName nm}, {formatBinderInfo bi}, {sty}, {sbd}]"
  | .forallE nm ty bd bi =>
      let sty ← formatExpr ty
      let sbd ← formatExpr bd
      return s!"LeanPi[{formatName nm}, {formatBinderInfo bi}, {sty}, {sbd}]"
  | .letE _ _ val bd _ =>
      -- unfold the let before translating (port of `expand_let`)
      formatExpr (bd.instantiate1 val)
  | .mdata _ e' => formatExpr e'
  | .proj tp i s =>
      let ss ← formatExpr s
      return s!"LeanProj[{formatName tp}, {i}, {ss}]"
  | .fvar fvarId =>
      let d ← fvarId.getDecl
      let sty ← formatExpr d.type
      return s!"LeanLocal[{formatName fvarId.name}, {formatName d.userName}, {formatBinderInfo d.binderInfo}, {sty}]"
  | .mvar mvarId =>
      let d ← mvarId.getDecl
      let sty ← formatExpr d.type
      return s!"LeanMetaVar[{formatName mvarId.name}, {sty}]"

/-! ## Golden tests (run at build time; a thrown error fails the build) -/

section Tests

private def strContains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

-- Closed terms reflect to exact golden strings (no `fvar`/`mvar` involved).
#eval show MetaM Unit from do
  let cases : List (Expr × String) :=
    [ (.sort .zero, "LeanSort[LeanZeroLevel]"),
      (.sort (.succ .zero), "LeanSort[LeanLevelSucc[LeanZeroLevel]]"),
      (mkConst ``Nat, "LeanConst[LeanNameMkString[\"Nat\", LeanNameAnonymous], LeanLevelListNil]"),
      (.lit (.natVal 5), "LeanLitNat[5]"),
      (.lit (.strVal "hi"), "LeanLitStr[\"hi\"]"),
      (.bvar 3, "LeanVar[3]"),
      (mkApp (mkConst ``Nat.succ) (.bvar 0),
        "LeanApp[LeanConst[LeanNameMkString[\"succ\", LeanNameMkString[\"Nat\", LeanNameAnonymous]], LeanLevelListNil], LeanVar[0]]"),
      (.lam `x (mkConst ``Nat) (.bvar 0) .default,
        "LeanLambda[LeanNameMkString[\"x\", LeanNameAnonymous], BinderInfoDefault, LeanConst[LeanNameMkString[\"Nat\", LeanNameAnonymous], LeanLevelListNil], LeanVar[0]]") ]
  for (e, want) in cases do
    let got ← formatExpr e
    unless got == want do
      throwError m!"formatExpr mismatch\n  got:      {got}\n  expected: {want}"

-- `fvar`/`mvar` resolve against the context (ids are fresh, so check structure
-- and the resolved type/binder-info rather than an exact golden).
#eval show MetaM Unit from do
  withLocalDeclD `h (mkConst ``Nat) fun x => do
    let got ← formatExpr x
    unless got.startsWith "LeanLocal[" && strContains got "BinderInfoDefault"
           && strContains got "LeanNameMkString[\"Nat\", LeanNameAnonymous]" do
      throwError m!"fvar reflection unexpected: {got}"
  let m ← mkFreshExprMVar (mkConst ``Nat)
  let got ← formatExpr m
  unless got.startsWith "LeanMetaVar[" && strContains got "LeanNameMkString[\"Nat\", LeanNameAnonymous]" do
    throwError m!"mvar reflection unexpected: {got}"

end Tests

end Mathematica
