/-
Wire-protocol parser: the terse serialization Mathematica's `OutputFormat`
emits, parsed back into `MMExpr`.  Port of `parse_mmexpr` and its helpers from
the Lean 3 `mathematica_parser.lean`.

Grammar (no whitespace inside a message):

    expr := "I[" "-"? digit* "]"                        -- integer
          | "T[\"" (¬'"')* "\"]"                         -- string
          | "Y[" (¬']')* "]"                             -- symbol
          | "A" expr "[" (expr ("," expr)*)? "]"         -- application

TODO(efficiency, MIGRATION.md §9): this runs over `List Char` for a faithful,
obviously-correct first port.  Messages are small so it is not a hot path, but
a `String.Iterator` / `Std.Internal.Parsec` version is the eventual target.
-/
import Mathematica.MMExpr

namespace Mathematica
namespace Wire

/-- Newlines / tabs / CR → spaces (port of `make_monospaced`). -/
def monospace (s : String) : String :=
  s.map fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c

/-- Preprocess a raw kernel response before parsing: normalise interior control
    chars to spaces.  The socket's trailing newline thus becomes a trailing
    space, which `parse` tolerates (no separate right-trim needed). -/
def preprocess (s : String) : String :=
  monospace s

private def expectChar (c : Char) : List Char → Except String (List Char)
  | x :: rest => if x == c then .ok rest else .error s!"expected '{c}', got '{x}'"
  | []        => .error s!"expected '{c}', got end of input"

private def natOfDigits (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

mutual

partial def parseExpr : List Char → Except String (MMExpr × List Char)
  | 'I' :: '[' :: rest => do
      let (neg, rest) := match rest with
        | '-' :: r => (true, r)
        | _        => (false, rest)
      let (digits, rest) := rest.span Char.isDigit
      let rest ← expectChar ']' rest
      let n : Int := natOfDigits digits
      pure (.int (if neg then -n else n), rest)
  | 'T' :: '[' :: '"' :: rest => do
      let (chars, rest) := rest.span (· != '"')
      let rest ← expectChar '"' rest
      let rest ← expectChar ']' rest
      pure (.str (String.ofList chars), rest)
  | 'Y' :: '[' :: rest => do
      let (chars, rest) := rest.span (· != ']')
      let rest ← expectChar ']' rest
      pure (.sym (String.ofList chars), rest)
  | 'A' :: rest => do
      let (hd, rest) ← parseExpr rest
      let rest ← expectChar '[' rest
      let (args, rest) ← parseArgs rest
      pure (.app hd args, rest)
  | c :: _ => .error s!"unexpected character '{c}'"
  | []     => .error "unexpected end of input"

partial def parseArgs : List Char → Except String (List MMExpr × List Char)
  | ']' :: rest => pure ([], rest)
  | cs => do
      let (e, cs) ← parseExpr cs
      match cs with
      | ',' :: rest => do
          let (es, rest) ← parseArgs rest
          pure (e :: es, rest)
      | ']' :: rest => pure ([e], rest)
      | c :: _      => .error s!"expected ',' or ']' in argument list, got '{c}'"
      | []          => .error "unterminated argument list"

end

/-- Parse a raw Mathematica wire response into an `MMExpr`
    (port of `parse_mmexpr_tac`). -/
def parse (s : String) : Except String MMExpr := do
  let (e, rest) ← parseExpr (preprocess s).toList
  if rest.all (· == ' ') then pure e
  else .error s!"unexpected trailing input: {String.ofList rest}"

/-! ## Round-trip tests (checked at build time; a false `#guard` fails the build) -/

private def okEq (r : Except String MMExpr) (e : MMExpr) : Bool :=
  match r with
  | .ok e'   => e' == e
  | .error _ => false

#guard okEq (parse "I[42]") (.int 42)
#guard okEq (parse "I[-7]") (.int (-7))
#guard okEq (parse "I[0]")  (.int 0)
#guard okEq (parse "Y[Plus]") (.sym "Plus")
#guard okEq (parse "T[\"hello\"]") (.str "hello")
#guard okEq (parse "AY[f][]") (.app (.sym "f") [])
#guard okEq (parse "AY[Plus][I[1],I[2]]") (.app (.sym "Plus") [.int 1, .int 2])
#guard okEq (parse "AY[List][I[1],AY[Times][I[2],I[3]]]")
            (.app (.sym "List") [.int 1, .app (.sym "Times") [.int 2, .int 3]])
-- a trailing newline from the socket is tolerated
#guard okEq (parse "I[5]\n") (.int 5)
-- malformed input is a structured error, not a crash
#guard (parse "AY[Plus][I[1]").toOption.isNone
#guard (parse "Q[7]").toOption.isNone

-- round-trip: parse ∘ toWire = id  (toWire mirrors Mathematica's OutputFormat)
private def sample : MMExpr :=
  .app (.sym "Plus") [.int 1, .app (.sym "Times") [.int (-2), .sym "x"], .str "s"]
#guard okEq (parse sample.toWire) sample

end Wire
end Mathematica
