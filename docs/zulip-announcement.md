# Lean Zulip post — mathematica-in-lean (draft)

*Before posting: pick the stream (suggestions below), and — the community will check —
re-confirm the axiom claims still hold (`#print axioms` clean on the examples you
cite). Everything below is the message.*

**Stream / topic suggestions** (leanprover.zulipchat.com):
- `#general` → topic *"Sound Mathematica bridge for Lean 4"*, or
- a metaprogramming / tactics stream (e.g. `#metaprogramming / tactics`), or
- `#Machine Learning for Theorem Proving` (the AI-for-math / CAS-oracle angle).

Keep it to one stream; cross-posting is frowned on.

---

## Post

**A sound Mathematica bridge for Lean 4 — the CAS discovers, the kernel verifies**

Hi all — I'd like to share a Lean 4 ↔ Mathematica bridge I've been building. The design
principle is that the tactics are **sound**: Mathematica proposes a certificate or a
simplification, and Lean *checks* it, so nothing rests on trusting the CAS.
`#print axioms` on the results shows only the usual `[propext, Classical.choice,
Quot.sound]`.

The tactics:

- **`mathematica_ring`** — Mathematica finds a `PolynomialReduce` certificate and
  `ring` / `linear_combination` verifies it (a Mathematica-powered `polyrith`).
- **`mathematica_rw`** — a fixed-point subterm-rewriting loop: simplify a subterm in
  Mathematica, validate the step with `ring` / `field_simp` / `norm_num` / `simp`,
  rewrite it in place via `kabstract`, and repeat.
- **`mathematica_telescope`** — fetch a Wilf–Zeilberger certificate through the bridge
  and close a binomial sum.
- **`LeanCheck`** (on the Wolfram side) — the reverse direction: verify a Mathematica
  claim in Lean's kernel, from a notebook.

```lean
-- sound: a rational-function identity plain `ring` cannot do
example (x : ℝ) (h : x - 1 ≠ 0) : (x^2 - 1) / (x - 1) = x + 1 := by mathematica_rw

-- sound: a binomial sum whose certificate is found by Mathematica
example (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (n.choose k)^2 = (2 * n).choose n := by
  mathematica_telescope
```

The flagship is a certified, end-to-end proof of `∑ C(n,k)² = C(2n,n)`: Mathematica
discovers the WZ certificate `R(n,k) = k²(2k − 3n − 3)/(n+1 − k)²`, Lean verifies it
(`field_simp; ring`), telescopes the finite sum, and inducts — axiom-clean.

Two things I want to be upfront about:

1. **The identity itself is already in mathlib** (`Nat.sum_range_choose_sq`). The point
   is the *method* — a CAS-discovered certificate that the kernel checks — not the
   result.
2. **`mathematica_telescope` currently fetches-and-closes the `C(n,k)^{1,2}` family.**
   Generating a boundary-correct closed-form proof term for an *arbitrary* summand is
   future work; the one genuinely fiddly bit was the WZ boundary term (`G = R·F` blows
   up at `k = n`), which I handle by a boundary-safe reformulation of the certificate.

Transport is a persistent `WolframKernel` over stdio — no Python, no sockets.
`mathematica_simp` (a `FullSimplify` that closes via an explicit `Mathematica.trust`
oracle axiom) is the one *trusting* tactic, kept separate and clearly labelled.

Repo + write-up: https://github.com/fairflow/mathematica-in-lean . Feedback very welcome
— especially on the reverse direction's in-process prover, and on whether general
certificate-driven proof synthesis is something people here have tackled.
