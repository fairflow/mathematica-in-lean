/-
`MMExpr` — a Lean 4 reflection of Mathematica expression syntax, plus the
`MFloat` arbitrary-precision-float record.

Port of the `mmexpr` / `mfloat` types from the Lean 3 `mathematica_parser.lean`.
Naming follows Lean 4 house style (UpperCamelCase type, lowerCamelCase fields);
`mstr`/`mint`/`mreal` become `str`/`int`/`real` since the `MMExpr.` qualifier
already disambiguates from `String`/`Int`.
-/

namespace Mathematica

/-- Mathematica's arbitrary-precision float as three naturals
    (sign, mantissa, exponent).  Vestigial in the current wire protocol —
    `OutputFormat` never emits reals — but kept for completeness/round-tripping. -/
structure MFloat where
  sign     : Nat
  mantissa : Nat
  exponent : Nat
deriving Repr, BEq, Inhabited

/-- Reflected Mathematica expression syntax (was Lean 3 `inductive mmexpr`). -/
inductive MMExpr where
  | sym  : String → MMExpr
  | str  : String → MMExpr
  | int  : Int → MMExpr
  | app  : MMExpr → List MMExpr → MMExpr
  | real : MFloat → MMExpr
deriving Repr, BEq, Inhabited

namespace MMExpr

/- Human-readable rendering `head[a, b, …]` (port of `mmexpr_to_format`).
   The `…Args` companion makes the recursion through `List MMExpr` structural. -/
mutual
  def format : MMExpr → String
    | .sym s    => s
    | .str s    => s!"\"{s}\""
    | .int i    => toString i
    | .real f   => s!"({f.sign}, {f.mantissa}, {f.exponent})"
    | .app hd a => hd.format ++ "[" ++ formatArgs a ++ "]"
  def formatArgs : List MMExpr → String
    | []      => ""
    | [x]     => x.format
    | x :: xs => x.format ++ ", " ++ formatArgs xs
end

/- Serialize to the terse wire format — the exact grammar Mathematica's
   `OutputFormat` emits (see `src/lean_form.m`).  Having it Lean-side lets us
   test `parse ∘ toWire = id` with no live kernel. -/
mutual
  def toWire : MMExpr → String
    | .sym s    => s!"Y[{s}]"
    | .str s    => s!"T[\"{s}\"]"
    | .int i    => s!"I[{i}]"
    | .real f   => s!"R[{f.sign},{f.mantissa},{f.exponent}]"  -- placeholder; not in protocol
    | .app hd a => "A" ++ hd.toWire ++ "[" ++ toWireArgs a ++ "]"
  def toWireArgs : List MMExpr → String
    | []      => ""
    | [x]     => x.toWire
    | x :: xs => x.toWire ++ "," ++ toWireArgs xs
end

instance : ToString MMExpr := ⟨format⟩

end MMExpr
end Mathematica
