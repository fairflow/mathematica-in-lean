# mathematica-in-lean

A **Lean 4 ↔ Mathematica** bridge: call Mathematica from Lean 4 (mathlib4) —
reflect a Lean term, run any Mathematica command on it (`Simplify`, `Factor`,
`Solve`, …), and translate the result back to a Lean `Expr`. It runs on a
persistent `WolframKernel` driven over stdin/stdout — **no Python, no sockets**.

A port of Lewis & Wu's Lean 3 *MM-Lean* interface to Lean 4 + mathlib4.

```lean
import Mathematica
open Mathematica

theorem pythag (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by mathematica_simp
```

## Quick start

```sh
lake exe cache get && lake build
export MATHEMATICA_BRIDGE_LEANFORM="$(pwd)/wolfram/lean_form.wl"
# MATHEMATICA_BRIDGE_KERNEL defaults to the macOS WolframKernel path; override elsewhere.
lake env lean examples/Demos.lean
```

## Docs

- **[USER_GUIDE.md](USER_GUIDE.md)** — setup, the `mathematica_simp` tactic,
  `runCommandOn` / `evalMathematica`, transports, and **how it works under the hood**.
- **[MIGRATION.md](MIGRATION.md)** — the Lean 3 → Lean 4 port map and design notes.
- **[wolfram/README.md](wolfram/README.md)** — the Mathematica side (`lean_form.wl`).
- **[examples/Demos.lean](examples/Demos.lean)** — non-trivial proofs the bridge closes.

## Layout

- `Mathematica/` — the Lean side: AST + wire parser, reflection (`Expr → String`),
  the `MMExpr → Expr` translation engine, transports, and the tactic.
- `wolfram/` — the Mathematica side: `lean_form.wl` translation rules + tests.
- `src/` — the original Lean 3 sources, kept for reference until fully retired.

> **Trust model:** Mathematica is an oracle; `mathematica_simp` closes goals via the
> `Mathematica.trust` axiom (visible in `#print axioms`). It's for exploration and
> computation, not kernel-checked proofs.

---

*This began as a fork (2024) to port the Lean 3 bridge to Lean 4 + mathlib4 and,
where useful, to Mathematica 14.*
