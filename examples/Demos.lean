/-
examples/Demos.lean — non-trivial theorems the Mathematica bridge proves.

These are NOT part of `lake build` (they call a live Mathematica kernel).  Run:

  MATHEMATICA_BRIDGE_KERNEL=/Applications/Wolfram.app/Contents/MacOS/WolframKernel \
  MATHEMATICA_BRIDGE_LEANFORM="$(pwd)/wolfram/lean_form.wl" \
  lake env lean examples/Demos.lean

Each `mathematica_simp` reflects the goal, asks Mathematica to `FullSimplify` it,
and closes the goal if the kernel returns `True` — trusting `Mathematica.trust`
(an oracle axiom; see `#print axioms`).  One persistent `WolframKernel` serves the
whole file (no Python, no per-call startup).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathematica

open Mathematica

/-- The Pythagorean identity — real analysis, one line via Mathematica. -/
theorem pythagorean (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by mathematica_simp

/-- Binomial expansion. -/
theorem binomial (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by mathematica_simp

/-- Difference of squares. -/
theorem diff_of_squares (x : ℝ) : (x + 1) * (x - 1) = x ^ 2 - 1 := by mathematica_simp

/-- A concrete arithmetic fact. -/
theorem arith : (10 - 3 : Nat) = 7 := by mathematica_simp

/-- With a variable — Mathematica knows `x + 0 = x`. -/
theorem add_zero' (x : Nat) : x + 0 = x := by mathematica_simp

-- Raw evaluation: compute a value in Mathematica and bring it back as a Lean term.
run_cmd do
  let e ← Lean.Elab.Command.liftTermElabM do
    let t ← defaultTransport
    evalMathematica t "Prime[100]"          -- the 100th prime
  Lean.logInfo m!"Mathematica: Prime[100] = {e}"

-- Embedding Mathematica with custom syntax (Rob Lewis's first suggestion).
#mathematica "Factor[x^2 - 1]"              -- ⇒ (-1 + x)*(1 + x)
#mathematica "fib[n_] := Fibonacci[n]"      -- a definition — persists in the kernel
#mathematica "fib[20]"                      -- ⇒ 6765  (uses the definition above)
#eval (mathematica% "Prime[100]" : Nat)     -- ⇒ 541
#eval (mathematica% "GCD[126, 84]" : Nat)   -- ⇒ 42

#print axioms pythagorean
