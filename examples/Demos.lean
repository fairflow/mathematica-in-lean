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

/-! ### `mathematica_ring` — certificate mode (SOUND: no `Mathematica.trust`)

`mathematica_ring` uses Mathematica only to *discover* a certificate; Lean's own
`ring1` / `linear_combination` *checks* it, so the proof is kernel-verified and
`Mathematica.trust` never enters `#print axioms` (contrast `mathematica_simp`).
It is the Mathematica analogue of `polyrith`. -/

/-- A pure ring identity — closed by `ring1` after Mathematica confirms it. -/
theorem binomial_sound (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  mathematica_ring

/-- Uses a hypothesis — Mathematica finds the multiplier `(x + y + 1)`, and
    `linear_combination` verifies it.  Plain `ring` CANNOT prove this (it needs
    `h`); `mathematica_ring` can, and soundly. -/
theorem with_hyp (x y : ℝ) (h : x = y + 1) : x ^ 2 = y ^ 2 + 2 * y + 1 := by
  mathematica_ring

-- The soundness payoff: only the standard mathlib axioms, no `Mathematica.trust`.
#print axioms binomial_sound   -- [propext, Classical.choice, Quot.sound]
#print axioms with_hyp         -- [propext, Classical.choice, Quot.sound]

/-! ### `mathematica_rw` — sound Mathematica-assisted rewriting (Mathematica proposes, Lean disposes)

Simplify each side in Mathematica, validate each step with a Lean certificate tactic.
Also sound (no `Mathematica.trust`), and broader than `ring`. -/

theorem rw_poly (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by mathematica_rw
/-- A rational function — validated by `field_simp`, which plain `ring` cannot do. -/
theorem rw_rational (x : ℝ) (h : x - 1 ≠ 0) : (x ^ 2 - 1) / (x - 1) = x + 1 := by mathematica_rw
theorem rw_numeric : (2 ^ 10 : ℝ) = 1024 := by mathematica_rw
/-- The fixed-point subterm loop: only the buried `(x²-1)/(x-1)` is rewritten
    (to `x+1`), the surrounding `x +` untouched, via `kabstract` navigation. -/
theorem rw_subterm (x : ℝ) (h : x - 1 ≠ 0) :
    x + (x ^ 2 - 1) / (x - 1) = x + (x + 1) := by mathematica_rw
#print axioms rw_rational       -- [propext, Classical.choice, Quot.sound]
#print axioms rw_subterm        -- [propext, Classical.choice, Quot.sound]

/-! ### `mathematica_telescope` — fetch a WZ certificate through the bridge, then close

Each proof fetches its creative-telescoping certificate live via the bridge (`WZCert`)
and closes the binomial-sum identity. -/

theorem tele_choose (n : ℕ) : ∑ k ∈ Finset.range (n + 1), n.choose k = 2 ^ n := by
  mathematica_telescope
theorem tele_choose_sq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 2 = (2 * n).choose n := by
  mathematica_telescope

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

-- Graphics in the infoview (open this file in the Lean infoview to see the plots).
#mathematica_plot "Plot[Sin[x], {x, 0, 2 Pi}]"
#mathematica_plot "Plot3D[Sin[x y], {x, 0, 3}, {y, 0, 3}]"

#print axioms pythagorean
