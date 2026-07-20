/-
Unreflection leaves: translate the `Lean…[…]` forms Mathematica sends back into
`Level` / `Name` / `BinderInfo`.  Port of `name_of_mmexpr`, `level_of_mmexpr`,
`level_list_of_mmexpr`, `binder_info_of_mmexpr` from the Lean 3 `mathematica.lean`.

These are pure structural translations (`Except String _`) — no `MetaM` needed.
That comes with the `MMExpr → Expr` engine (rule databases + local context).
`unsigned_of_int` collapses to `Int.toNat`.

Two faithfulness fixes vs. the Lean 3 original:
  · `LeanLevelParam`/`LeanLevelMeta` carry a *name* reflection (that is what the
    reflection side emits), so they are parsed with `nameOfMMExpr`; the Lean 3
    code matched a bare `mstr s` and would have failed on real round-trip input.
  · Lean 4 `BinderInfo` has no `aux_decl`/"other" case, so it is dropped.
-/
import Lean
import Mathematica.MMExpr

open Lean

namespace Mathematica

/-- Unreflect a `Name` (port of `name_of_mmexpr`). -/
def nameOfMMExpr : MMExpr → Except String Name
  | .sym "LeanNameAnonymous"                    => .ok .anonymous
  | .app (.sym "LeanNameMkString") [.str s, m]  => (Name.str · s) <$> nameOfMMExpr m
  | .app (.sym "LeanNameMkNum")    [.int i, m]  => (Name.num · i.toNat) <$> nameOfMMExpr m
  | e => .error s!"not a LeanName: {e.format}"

/-- Unreflect a universe `Level` (port of `level_of_mmexpr`). -/
def levelOfMMExpr : MMExpr → Except String Level
  | .sym "LeanZeroLevel"               => .ok .zero
  | .app (.sym "LeanLevelSucc") [m]    => (Level.succ ·) <$> levelOfMMExpr m
  | .app (.sym "LeanLevelMax")  [a, b] => do return .max  (← levelOfMMExpr a) (← levelOfMMExpr b)
  | .app (.sym "LeanLevelIMax") [a, b] => do return .imax (← levelOfMMExpr a) (← levelOfMMExpr b)
  | .app (.sym "LeanLevelParam") [m]   => (Level.param ·) <$> nameOfMMExpr m
  | .app (.sym "LeanLevelMeta")  [m]   => (fun n => .mvar ⟨n⟩) <$> nameOfMMExpr m
  | e => .error s!"not a LeanLevel: {e.format}"

/-- Unreflect a `List Level` (port of `level_list_of_mmexpr`). -/
def levelListOfMMExpr : MMExpr → Except String (List Level)
  | .sym "LeanLevelListNil"                => .ok []
  | .app (.sym "LeanLevelListCons") [h, t] => do return (← levelOfMMExpr h) :: (← levelListOfMMExpr t)
  | e => .error s!"not a LeanLevelList: {e.format}"

/-- Unreflect a `BinderInfo` (port of `binder_info_of_mmexpr`). -/
def binderInfoOfMMExpr : MMExpr → Except String BinderInfo
  | .sym "BinderInfoDefault"        => .ok .default
  | .sym "BinderInfoImplicit"       => .ok .implicit
  | .sym "BinderInfoStrictImplicit" => .ok .strictImplicit
  | .sym "BinderInfoInstImplicit"   => .ok .instImplicit
  | e => .error s!"not a BinderInfo: {e.format}"

/-! ## Tests (run at build time via `#eval`; a thrown error fails the build) -/

#eval show MetaM Unit from do
  let checks : List (Bool × String) :=
    [ ((nameOfMMExpr (.sym "LeanNameAnonymous")).toOption == some .anonymous, "name: anonymous"),
      ((nameOfMMExpr (.app (.sym "LeanNameMkString") [.str "Nat", .sym "LeanNameAnonymous"])).toOption
        == some (.str .anonymous "Nat"), "name: Nat"),
      ((nameOfMMExpr (.app (.sym "LeanNameMkString")
          [.str "succ", .app (.sym "LeanNameMkString") [.str "Nat", .sym "LeanNameAnonymous"]])).toOption
        == some (.str (.str .anonymous "Nat") "succ"), "name: Nat.succ"),
      ((nameOfMMExpr (.app (.sym "LeanNameMkNum") [.int 7, .sym "LeanNameAnonymous"])).toOption
        == some (.num .anonymous 7), "name: numeral"),
      ((levelOfMMExpr (.sym "LeanZeroLevel")).toOption == some .zero, "level: zero"),
      ((levelOfMMExpr (.app (.sym "LeanLevelSucc") [.sym "LeanZeroLevel"])).toOption
        == some (.succ .zero), "level: succ zero"),
      ((levelOfMMExpr (.app (.sym "LeanLevelParam")
          [.app (.sym "LeanNameMkString") [.str "u", .sym "LeanNameAnonymous"]])).toOption
        == some (.param (.str .anonymous "u")), "level: param u"),
      ((levelListOfMMExpr (.app (.sym "LeanLevelListCons")
          [.sym "LeanZeroLevel", .sym "LeanLevelListNil"])).toOption
        == some [.zero], "levellist: [zero]"),
      ((binderInfoOfMMExpr (.sym "BinderInfoDefault")).toOption == some .default, "bi: default"),
      ((binderInfoOfMMExpr (.sym "BinderInfoInstImplicit")).toOption == some .instImplicit, "bi: inst"),
      -- error cases return .error, never crash
      ((nameOfMMExpr (.sym "Nope")).toOption == none, "name: error case"),
      ((levelOfMMExpr (.int 3)).toOption == none, "level: error case") ]
  for (b, lbl) in checks do
    unless b do throwError m!"unreflect test failed: {lbl}"

end Mathematica
