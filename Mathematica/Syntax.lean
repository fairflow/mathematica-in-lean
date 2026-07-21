/-
Custom syntax for embedding Mathematica in a Lean file — Rob Lewis's first
suggested Lean 4 improvement.  Lean 3 could only do this hackishly; Lean 4's
`syntax`/`elab` makes it clean.

  · `mathematica% "cmd"`  (term)    — evaluate `cmd`, elaborate to the translated
                                       Lean term.  Best for closed/numeric results.
  · `#mathematica "code"` (command) — run `code` at the top level and log the result
                                       in Mathematica InputForm.  Definitions persist
                                       in the kernel across commands (it is one
                                       long-lived session), so a file can build up a
                                       full Mathematica program.
-/
import Mathematica.Tactic

open Lean Elab Meta

namespace Mathematica

/-- `mathematica% "cmd"` evaluates `cmd` in Mathematica and elaborates to the
    translated Lean term.  Best for closed / numeric results — e.g.
    `(mathematica% "Prime[100]" : Nat)` reduces to `541`, and
    `mathematica% "2^31 - 1"` is a Lean numeral. -/
syntax (name := mathematicaTerm) "mathematica% " str : term

elab_rules : term
  | `(mathematica% $s:str) => do evalMathematica (← defaultTransport) s.getString

/-- `#mathematica "code"` runs Mathematica `code` at the top level and logs the
    result in Mathematica `InputForm`.  Works for symbolic results too — e.g.
    `#mathematica "Factor[x^2 - 1]"` logs `(-1 + x) (1 + x)`.  Because the kernel is
    one long-lived session, definitions persist: a later `#mathematica` sees them. -/
syntax (name := mathematicaCmd) "#mathematica " str : command

elab_rules : command
  | `(#mathematica $s:str) => Command.liftTermElabM do
      let out ← executeAndEval (← defaultTransport) ("ToString[InputForm[" ++ s.getString ++ "]]")
      match out with
      | .str result => logInfo result
      | other        => logInfo (toString other)

end Mathematica
