# mathematica-in-lean

A **bidirectional Lean 4 ↔ Wolfram (Mathematica) bridge** with **sound**, CAS-assisted tactics.
Reflect a Lean term, run any Wolfram command on it (`Simplify`, `Factor`, `Solve`,
…), and translate the result back — over a persistent `WolframKernel` driven on
stdin/stdout (**no Python, no sockets**). A Lean 4 + mathlib4 port and major extension
of Lewis & Wu's Lean 3 *MM-Lean* interface.

The principle throughout: **Wolfram discovers, Lean's kernel verifies.** Most
tactics here are *sound* — Wolfram proposes a certificate or a simplification and
Lean *checks* it, so `#print axioms` stays free of any trust axiom.

```lean
import Mathlib.Data.Real.Basic   -- your file imports the mathlib it uses (ℝ here);
import Mathematica               -- the bridge stays light and doesn't re-export Mathlib
-- sound: a rational-function identity plain `ring` cannot do
example (x : ℝ) (h : x - 1 ≠ 0) : (x^2 - 1)/(x - 1) = x + 1 := by mathematica_rw
-- sound: a binomial sum whose certificate is found by Mathematica
example (n : ℕ) : ∑ k ∈ Finset.range (n+1), (n.choose k)^2 = (2*n).choose n := by
  mathematica_telescope
```

## The tactics

| tactic | direction | what it does | sound? |
|---|---|---|---|
| `mathematica_ring` | Lean → MM | CAS finds a `PolynomialReduce` certificate; `ring`/`linear_combination` checks it | ✅ |
| `mathematica_rw` | Lean → MM | fixed-point subterm rewriting — simplify a subterm in MM, validate the step (`ring`/`field_simp`/`norm_num`/`simp`), rewrite in place, repeat | ✅ |
| `mathematica_telescope` | Lean → MM | fetch a Wilf–Zeilberger certificate through the bridge for a binomial sum and close | ✅ |
| `mathematica_simp` | Lean → MM | `FullSimplify`; closes via the `Mathematica.trust` axiom | ✗ (oracle) |
| `LeanCheck` (Wolfram) | MM → Lean | verify a Wolfram claim in Lean's kernel, from a notebook | ✅ |

Plus `evalWolfram` / `runCommandOn*` (call a command on Lean terms), the embedding
syntax `mathematica%` / `#mathematica`, `#mathematica_plot` (a Wolfram graphic in
the infoview), and `WZCert` on the Wolfram side (a creative-telescoping certificate
finder callable through the bridge).

## Flagship: certified creative telescoping

[`examples/CreativeTelescoping.lean`](examples/CreativeTelescoping.lean) proves
`∑ C(n,k)² = C(2n,n)` **end to end, sound**: Wolfram's `WZCert` *discovers* the
Wilf–Zeilberger certificate `R(n,k) = k²(2k−3n−3)/(n+1−k)²`; Lean *verifies* it
(`field_simp; ring`), telescopes the finite sum (handling the boundary), and inducts —
with `#print axioms` free of any trust axiom.
[`examples/ZeilbergerBridge.lean`](examples/ZeilbergerBridge.lean) shows the discovery
half live through the bridge.

This is the "**experimental-mathematics → formal-proof**" pipeline: the CAS finds a
certificate no elementary Lean tactic gives, and the kernel checks it. (cf. the Coq
formalisation of ζ(3)'s irrationality via creative telescoping — this is the first such
pipeline in Lean 4, and via Wolfram.)

## Both directions

- **Forward** (Lean → Wolfram) — the tactics above.
- **Reverse** (Wolfram → Lean) — `LeanCheck[claim]` from a Wolfram session ships a
  claim to a headless Lean service (`lake exe lean_verify`), which verifies it in the
  kernel and returns the verdict with its axioms. The *sound* direction: Lean's kernel
  is the trusted party. See [docs/REVERSE_BRIDGE_DESIGN.md](docs/REVERSE_BRIDGE_DESIGN.md).

## Quick start

```sh
lake exe cache get && lake build
export MATHEMATICA_BRIDGE_LEANFORM="$(pwd)/wolfram/lean_form.wl"
# MATHEMATICA_BRIDGE_KERNEL defaults to the macOS WolframKernel path; override elsewhere.
lake env lean examples/Demos.lean
```

The examples need a live kernel, so they're run with `lake env lean` (they are not part
of the default `lake build`, which builds the library alone).

## Docs

- **[USER_GUIDE.md](USER_GUIDE.md)** — setup, every tactic, transports, and **how it
  works under the hood**.
- **[examples/CreativeTelescoping.lean](examples/CreativeTelescoping.lean)** — the
  certified creative-telescoping case study (L0 → the full `∑ C(n,k)² = C(2n,n)`).
- **[docs/REVERSE_BRIDGE_DESIGN.md](docs/REVERSE_BRIDGE_DESIGN.md)** — the reverse
  bridge (`LeanCheck` + the `lean_verify` service).
- **[MIGRATION.md](MIGRATION.md)** — the Lean 3 → Lean 4 port map and design notes.
- **[wolfram/README.md](wolfram/README.md)** — the Wolfram side (`lean_form.wl`).

## Layout

- `Mathematica/` — the Lean side: wire AST + parser, reflection (`Expr → String`), the
  `MMExpr → Expr` translation engine, transports, and the tactics
  (`Tactic`, `Ring`, `Rewrite`, `Telescope`, `Syntax`, `Widget`).
- `Reverse/` — the reverse bridge: `lean_verify`, a headless Lean verification service.
- `wolfram/` — the Wolfram side: `lean_form.wl` (translation rules, `OutputFormat`,
  `WZCert`), `lean_verify.wl` (`LeanCheck`), and tests.
- `examples/` — demos and the case study (need a live kernel).
- `src/` — the original Lean 3 sources, kept for reference.

## Trust model

**Sound by default.** `mathematica_ring`, `mathematica_rw`, `mathematica_telescope`,
and the reverse `LeanCheck` all yield **kernel-checked** proofs — Wolfram supplies
a certificate or simplification and Lean verifies it, so no trust axiom enters
(`#print axioms` shows only the standard mathlib axioms). The one exception is
`mathematica_simp`, which *trusts* Wolfram via the `Mathematica.trust` axiom
(handy for exploration; it shows up in `#print axioms`).

---

*Began as a fork (2024) to port the Lean 3 bridge to Lean 4 + mathlib4; since extended
into a sound, bidirectional CAS-oracle bridge with a certified creative-telescoping
case study.*
