/-
Case study L0 — creative telescoping, the Lean-side certificate mechanism.

The flagship case study (see docs/… / the proposal) is: Mathematica *discovers* a
creative-telescoping certificate for a sum identity, and Lean *verifies* it — soundly,
no `Mathematica.trust`.  This file wires the **Lean side** of that pipeline on two
rungs, and is pure Lean (no kernel needed to build it).

The reusable skeleton is always the same:
  1. a **certificate** `G` (a summand-shaped function) such that the summand equals
     `G(k+1) − G(k)` — an identity checked by `ring` (this is the part Mathematica
     finds and Lean verifies);
  2. **telescoping** the sum of `G(k+1) − G(k)` to boundary terms (`Finset.sum_range_sub`);
  3. reading off the closed form / recurrence.

L1 (next) swaps the hand-known certificates here for ones Mathematica's Zeilberger
algorithm produces, and richer summands (binomial squares → the C(2n,n) identity).
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Defs

open Finset

namespace Mathematica.Telescoping

/-! ### Rung 0a — plain telescoping, the certificate skeleton in miniature

`∑_{k<n} (2k+1) = n²`.  Certificate `G k = k²`: the summand `2k+1` is exactly
`G(k+1) − G(k)`, an identity `ring` checks; the sum then telescopes to `G n − G 0`. -/

/-- The certificate. -/
private def G0 (k : ℕ) : ℤ := (k : ℤ) ^ 2

theorem odd_sum (n : ℕ) : ∑ k ∈ range n, (2 * (k : ℤ) + 1) = (n : ℤ) ^ 2 := by
  have cert : ∀ k : ℕ, (2 * (k : ℤ) + 1) = G0 (k + 1) - G0 k := by
    intro k; simp only [G0]; push_cast; ring
  calc ∑ k ∈ range n, (2 * (k : ℤ) + 1)
      = ∑ k ∈ range n, (G0 (k + 1) - G0 k) := by simp_rw [cert]
    _ = G0 n - G0 0 := Finset.sum_range_sub G0 n
    _ = (n : ℤ) ^ 2 := by simp [G0]

/-! ### Rung 0b — the first *creative* telescoping: `∑_{k=0}^{n} C(n,k) = 2ⁿ`

Here the certificate lives in the `k` direction while the sum produces a **recurrence
in `n`** — this is what Zeilberger's algorithm does, and what needs a CAS in general.
The recurrence is `S(n+1) = 2·S(n)`; Mathematica finds it, Lean verifies it here via
Pascal's rule (the content of the WZ certificate), and induction gives the closed
form.  Sound: `#print axioms` below shows no `Mathematica.trust`.

Mathematica side, confirmed live via the bridge's kernel (the discovery half):
    Sum[Binomial[n,k],{k,0,n}]                                     ⇒  2^n
    FullSimplify[ Sum[Binomial[n+1,k],{k,0,n+1}]
                    == 2 Sum[Binomial[n,k],{k,0,n}], n>=0 ]        ⇒  True
So the CAS supplies the recurrence + closed form; Lean supplies the proof. -/

/-- `S n = ∑_{k=0}^{n} C(n,k)`. -/
def S (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose k

/-- The Mathematica-discovered recurrence, verified in Lean by Pascal's rule. -/
theorem S_succ (n : ℕ) : S (n + 1) = 2 * S n := by
  unfold S
  rw [Finset.sum_range_succ']            -- peel k=0 and reindex the tail as k+1
  simp only [Nat.choose_succ_succ, Nat.choose_zero_right, Nat.succ_eq_add_one]
  rw [Finset.sum_add_distrib]
  -- goal: (∑ C(n,k) + ∑ C(n,k+1)) + 1 = 2 * ∑ C(n,k)   over range (n+1)
  -- reindex the shifted tail: ∑_{range(n+2)} C(n,i) split two ways.
  have key : ∑ i ∈ range (n + 1 + 1), n.choose i
           = (∑ i ∈ range (n + 1), n.choose (i + 1)) + 1 := by
    rw [Finset.sum_range_succ' (fun i => n.choose i) (n + 1), Nat.choose_zero_right]
  have top : ∑ i ∈ range (n + 1 + 1), n.choose i = ∑ i ∈ range (n + 1), n.choose i := by
    rw [Finset.sum_range_succ]
    simp
  have tail := key.symm.trans top   -- (∑ C(n,k+1)) + 1 = ∑ C(n,k)
  omega

theorem sum_choose (n : ℕ) : S n = 2 ^ n := by
  induction n with
  | zero => simp [S]
  | succ n ih => rw [S_succ, ih]; ring

/-! ### Rung 1 — a *non-trivial* certificate, found by Mathematica, checked by Lean

Target: `∑_{k=0}^{n} C(n,k)² = C(2n,n)` (not a one-line Pascal argument).  For
`F(n,k) = C(n,k)²`, Zeilberger's recurrence is `(n+1)·S(n+1) = (4n+2)·S(n)`, and the
**creative-telescoping certificate** (which needs a CAS) is

  Mathematica ⇒   R(n,k) = k²·(2k − 3n − 3) / (n + 1 − k)²

so that `G(n,k) = R(n,k)·F(n,k)` telescopes `(n+1)F(n+1,k) − (4n+2)F(n,k)`.  Dividing
that certificate identity by `F(n,k)` (using the exact binomial ratios
`F(n,k+1)/F(n,k) = ((n−k)/(k+1))²` and `F(n+1,k)/F(n,k) = ((n+1)/(n+1−k))²`) turns it
into a **rational-function identity in n,k** — which Lean discharges by `field_simp;
ring`.  That is the certificate check, sound and axiom-free: the CAS *found* it, the
Lean kernel *verifies* it.  (Mathematica independently reported residual 0.)

Summing this over `k` telescopes `G` to the boundary — and `R(n,0) = 0` (the `k²`
factor) while `F` vanishes past `k = n` — giving the recurrence, whence
`S(n) = C(2n,n)` by induction.  Building that `Finset`-telescoping glue is L1b (next);
this file lands the certificate verification, the heart of the pipeline. -/

/-- The WZ certificate for `∑ C(n,k)² = C(2n,n)`, as found by Mathematica. -/
def Rc (n k : ℚ) : ℚ := k ^ 2 * (2 * k - 3 * n - 3) / (n + 1 - k) ^ 2

/-- **Mathematica's certificate, verified sound in Lean by `field_simp; ring`.**
    The telescoping identity for `(n+1)S(n+1) = (4n+2)S(n)`, divided by `F(n,k)`. -/
theorem wz_cert (n k : ℚ) (hk1 : k + 1 ≠ 0) (hnk : n - k ≠ 0) (hnk1 : n + 1 - k ≠ 0) :
    (n + 1) * ((n + 1) / (n + 1 - k)) ^ 2 - (4 * n + 2)
      = Rc n (k + 1) * ((n - k) / (k + 1)) ^ 2 - Rc n k := by
  have hk1' : n + 1 - (k + 1) ≠ 0 := by
    rw [show n + 1 - (k + 1) = n - k from by ring]; exact hnk
  unfold Rc
  field_simp
  ring

end Mathematica.Telescoping

-- The soundness payoff: the certificate-verified identities carry NO trust axiom.
#print axioms Mathematica.Telescoping.odd_sum
#print axioms Mathematica.Telescoping.sum_choose
#print axioms Mathematica.Telescoping.wz_cert
