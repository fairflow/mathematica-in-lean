# Lean 4 ↔ Mathematica — User Guide

A bridge that lets **Lean 4 call Mathematica**: reflect a Lean term into
Mathematica syntax, run any Mathematica command on it (`Simplify`, `Factor`,
`Solve`, `Integrate`, …), and translate the result back into a Lean `Expr`.
It runs on a **persistent `WolframKernel`** driven over stdin/stdout — no Python,
no sockets, no per-call kernel startup.

A Lean-4/mathlib4 port of Lewis & Wu's Lean 3 *MM-Lean* interface.

> **Trust model.** Mathematica is an **oracle**: what it returns is *trusted*, not
> proven in Lean. The `mathematica_simp` tactic closes goals via the
> `Mathematica.trust` axiom, which shows up in `#print axioms`. This is a tool for
> **exploration and computation**, not for producing kernel-checked proofs — use
> Mathematica's answer as a guide, then discharge it properly with `ring`/`simp`/…
> if you need a trusted proof.

---

## 1. Prerequisites

- This repo's toolchain: Lean 4 `v4.31.0` + mathlib4 (`lake exe cache get && lake build`).
- A Mathematica / Wolfram Engine install providing `WolframKernel`
  (macOS default: `/Applications/Wolfram.app/Contents/MacOS/WolframKernel`).

## 2. Setup

Two environment variables point the bridge at the kernel and the translation rules:

```sh
# Path to the kernel (defaults to the macOS location, so often optional):
export MATHEMATICA_BRIDGE_KERNEL=/Applications/Wolfram.app/Contents/MacOS/WolframKernel
# Absolute path to wolfram/lean_form.wl (REQUIRED):
export MATHEMATICA_BRIDGE_LEANFORM="$(pwd)/wolfram/lean_form.wl"
```

Then `import Mathematica` in your file. Smoke-test with the bundled demos:

```sh
MATHEMATICA_BRIDGE_LEANFORM="$(pwd)/wolfram/lean_form.wl" \
  lake env lean examples/Demos.lean
```

You should see the theorems elaborate and `Mathematica: Prime[100] = 541`.

## 3. Using it

### `mathematica_simp` — prove a goal

Reflects the goal, `FullSimplify`s it in Mathematica, and closes it if the kernel
returns `True` (otherwise it replaces the goal with the simplified proposition).

```lean
import Mathematica
open Mathematica

theorem pythag (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by mathematica_simp
example (a b : ℝ)   : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by mathematica_simp
example (x : ℝ)     : (x + 1) * (x - 1) = x ^ 2 - 1           := by mathematica_simp
example (n : Nat)   : n + 0 = n                                := by mathematica_simp
```

### `evalMathematica` — compute a value

Run any Mathematica command and bring the result back as a Lean term:

```lean
run_cmd do
  let e ← Lean.Elab.Command.liftTermElabM do
    evalMathematica (← defaultTransport) "Prime[100]"
  Lean.logInfo m!"{e}"            -- 541
```

### Embedding Mathematica — `mathematica%` and `#mathematica`

Two custom-syntax forms let you write Mathematica directly in a Lean file:

```lean
-- term: pull a computed value into Lean
#eval (mathematica% "Prime[100]" : Nat)       -- 541
def mersenne31 : Nat := mathematica% "2^31 - 1"

-- command: run code at the top level, logging the InputForm result
#mathematica "Factor[x^2 - 1]"                 -- (-1 + x)*(1 + x)
#mathematica "fib[n_] := Fibonacci[n]"         -- a definition …
#mathematica "fib[20]"                         -- … usable later: 6765
```

Because the bridge is **one long-lived kernel session**, definitions made in one
`#mathematica` command are visible to later ones — so a file can build up a full
Mathematica program. `mathematica%` is best for closed / numeric results (a free
Mathematica symbol like `x` has no Lean counterpart); `#mathematica` shows
Mathematica's own `InputForm`, so it works for symbolic results too.

### Graphics — `#mathematica_plot`

Render a Mathematica graphic in the Lean infoview:

```lean
#mathematica_plot "Plot[Sin[x], {x, 0, 2 Pi}]"
#mathematica_plot "Plot3D[Sin[x y], {x, 0, 3}, {y, 0, 3}]"
```

The (headless) kernel rasterises the graphic to a PNG, base64-encodes it, and the
bridge shows it as an `<img>` via ProofWidgets (which ships with mathlib — no new
dependency). Works for anything Mathematica can `Export` to PNG: `Plot`, `Plot3D`,
`ContourPlot`, `Graphics`, `Histogram`, …. The image appears in the **infoview**
(VS Code / your Lean editor) at the command; a headless `lean` run just shows the
alt text.

### `runCommandOn` — apply a command to a Lean term (the programmatic core)

Reflect `e`, wrap it with a Mathematica command, translate the result back:

```lean
open Lean Lean.Meta in
-- factor a Lean polynomial with Mathematica, get a Lean `Expr` back
def factor (e : Expr) : MetaM Expr := do
  runCommandOn (← defaultTransport)
    (fun s => "Activate[LeanForm[" ++ s ++ "]] // Factor") e
```

The full family (ports of the Lean 3 `run_command_on*`):

| function | reflects | notes |
|---|---|---|
| `runCommandOn t cmd e` | one `Expr` | |
| `runCommandOn2 t cmd e₁ e₂` | two `Expr`s | `cmd : String → String → String` |
| `runCommandOnList t cmd es` | a `List Expr` | reflected as a Mathematica `{…}` list |
| `runCommandOn2Using` / `runCommandOnListUsing` | + `Get` a file first | for your own Mathematica defns |
| `loadFile t dir path` | — | load a `.wl` into the kernel's context |
| `evalMathematica t cmd` | — | raw command, no Lean input |

`defaultTransport : IO Transport` gives the shared persistent kernel.

## 4. Transports

`Transport` abstracts the kernel connection (`Mathematica/Tactic.lean`):

- **`Transport.persistentKernel kernel leanForm`** — the default. One long-lived
  `WolframKernel` over stdin/stdout, mutex-guarded (safe under Lean's parallel
  elaboration). Spawned once, lazily, and reused. `defaultTransport` and
  `mathematica_simp` use it.
- **`Transport.wolframScript wolframscript leanForm`** — stateless: a fresh
  `wolframscript -code` per call. Simple, but slower and parallel calls can exceed
  a Wolfram concurrent-kernel license limit.
- **`mockTransport response`** — returns a fixed response, for kernel-free tests.

## 5. Under the hood

What happens for `by mathematica_simp` on a goal `⊢ P`:

```
         P : Expr
           │  Reflect.formatExpr           Expr → "LeanConst[…]" string
           ▼
   "Activate[LeanForm[<P>]] // FullSimplify"        (the command)
           │  Transport.send                → WolframKernel stdin
           ▼
   lean_form.wl:  LeanForm  rewrites reflected Lean → idiomatic Mathematica
                  FullSimplify evaluates
                  OutputFormat serialises the answer to the wire form
           │                                ← WolframKernel stdout, framed <MMS>…<MME>
           ▼
   "Y[True]"   (wire)
           │  Wire.parse                    wire → MMExpr
           ▼
         MMExpr
           │  Translate.exprOfMMExpr        MMExpr → Expr   (`True`)
           ▼
         P' : Expr   →  goal closed if P' = True   (via `Mathematica.trust`)
```

The pieces (all under `Mathematica/`, each with build-time tests):

| module | direction | role |
|---|---|---|
| `MMExpr`, `Wire` | MM → Lean | the Mathematica-expr AST + parser for the terse wire grammar `I[n] T["s"] Y[sym] A hd[args]` |
| `Reflect` | Lean → MM | `Expr → String`, emitting `LeanConst/App/Lambda/Pi/Sort/Lit/…`. In `MetaM`, so free vars & metavars resolve against the context |
| `Unreflect` | MM → Lean | leaf translators for `Name` / `Level` / `BinderInfo` |
| `Translate` | MM → Lean | `MMExpr → MetaM Expr`: raw unreflection + semantic rules (`Plus→HAdd`, `List`, binders via `MetaM` telescopes). Uses `mkAppM` to infer implicits + synthesise instances (no Qq) |
| `Tactic` | — | transports, `runCommandOn*`, `evalMathematica`, `mathematica_simp` |
| `Syntax` | — | `mathematica%` (term) + `#mathematica` (command) — embedding |
| `Widget` | — | `#mathematica_plot` — a Mathematica graphic in the infoview (ProofWidgets) |
| `wolfram/lean_form.wl` | both | `LeanForm` (reflected Lean → Mathematica) + `OutputFormat` (Mathematica → wire) |

**Why two-sided translation?** A Lean term is raw: `x + y` is
`@HAdd.hAdd ℝ ℝ ℝ inst x y` — six arguments deep. `LeanForm.wl` collapses that to
`Plus[x, y]` so Mathematica can do algebra; then `OutputFormat` + `Translate` turn
Mathematica's answer back into a Lean `Expr`. Anything `LeanForm` doesn't recognise
passes through as raw `Lean…[…]` and reconstructs verbatim on the Lean side, so no
information is lost in a round trip.

**Numerals.** mathlib numerals are `OfNat.ofNat n` (the `bit0`/`bit1` towers are
gone), reflecting with the raw literal as `LeanLitNat[n]`; `lean_form.wl` maps both
`OfNat.ofNat[_, LeanLitNat[n], _]` and `LeanLitNat[n]` to the plain number `n`.

**The persistent kernel.** `persistentKernel` spawns `WolframKernel -noprompt`,
loads `lean_form.wl` once, then for each command writes
`WriteString["stdout","<MMS>"<>OutputFormat[cmd]<>"<MME>\n"]` to the kernel's stdin
and reads its stdout until the `<MME>` marker. A `Std.Mutex` serialises this so
concurrent tactic invocations (Lean elaborates declarations in parallel) can't
interleave on the shared pipe.

## 6. Extending it

To support a new operator in both directions:

1. **Lean → Mathematica** — add a rule to `wolfram/lean_form.wl`:
   ```wolfram
   LeanForm[LeanApp[…LeanConst[LeanName["Foo", "bar"], _]…], v_] := <Mathematica>
   ```
   Get the exact nesting/arg-count from the reflection probe below.
2. **Mathematica → Lean** — add a case for the Mathematica head in
   `exprOfMMExpr`'s `appSym` (`Mathematica/Translate.lean`).

**Reflection probe** — see exactly what a term reflects to (so you can write the
`.wl` pattern):

```lean
import Mathematica
open Lean Lean.Meta Mathematica
#eval show MetaM Unit from do
  Lean.logInfo (← formatExpr (← mkAppM ``HAdd.hAdd #[mkNatLit 1, mkNatLit 2]))
```

`wolfram/lean_form_test.wls` (run: `wolframscript -file wolfram/lean_form_test.wls`)
unit-tests the `.wl` rules against captured reflected forms.

## 7. Limitations

- **Trust:** `mathematica_simp` trusts Mathematica (`Mathematica.trust` in
  `#print axioms`) — not for verified proofs.
- **Operator coverage** in `lean_form.wl` is the common arithmetic/logic/relational
  set + `Real.sin/cos/tan/pi`; extend as in §6.
- **Numerals** come back typed as the simplification produces them (usually
  inferred fine); fully general polymorphic-numeral handling is a known rough edge.
- **Rule extensibility** (user-tagged translation rules, the Lean 3
  `@[user_attribute]` mechanism) is not yet ported — the rule set is built in.

See `MIGRATION.md` for the full port map and design notes.
