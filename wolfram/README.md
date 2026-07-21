# Mathematica side of the bridge

This directory is the Mathematica half: the translation rules and their tests.
How to *use* the bridge from Lean (transports, the `mathematica_simp` tactic,
`runCommandOn`, …) is in **[../USER_GUIDE.md](../USER_GUIDE.md)**.

## Files

| File | Role |
|------|------|
| `lean_form.wl` | `LeanForm` — reflected Lean (mathlib4) → idiomatic Mathematica — plus the `OutputFormat` wire serialiser. |
| `lean_form_test.wls` | unit tests for the rules. Run: `wolframscript -file lean_form_test.wls`. |

## What `lean_form.wl` does

`LeanForm[reflected]` rewrites a reflected Lean term into a Mathematica expression
Mathematica can compute with:

- operators → Mathematica heads: `HAdd.hAdd → Plus`, `HMul.hMul → Times`,
  `HSub.hSub → Subtract`, `HDiv.hDiv → Divide`, `HPow.hPow → Power`,
  `Neg.neg → -1·`, `LT.lt → Less` (and `LE`/`GT`/`GE`), `Eq → Equal`,
  `And`/`Or`/`Not`, `Real.sin/cos/tan → Sin/Cos/Tan`, `Real.pi → Pi`;
- numerals: `OfNat.ofNat[_, LeanLitNat[n], _]` and `LeanLitNat[n]` → `n`;
- anything unrecognised passes through as raw `Lean…[…]` so the Lean side can
  reconstruct it verbatim (nothing is lost in a round trip).

`OutputFormat[expr]` serialises a Mathematica expression to the terse wire grammar
(`I[n]  T["s"]  Y[sym]  A hd[args]`) that `Mathematica.Wire.parse` reads back.

## How it's driven (no Python, no socket server)

The Lean side spawns a persistent `WolframKernel -noprompt`, does
`Get["lean_form.wl"]` once, and for each request writes
`WriteString["stdout","<MMS>"<>OutputFormat[<cmd>]<>"<MME>\n"]` to the kernel's
stdin, reading stdout up to the `<MME>` marker. See `Transport.persistentKernel`
in `../Mathematica/Tactic.lean`. (The Lean 3 design used a Python socket client +
server; both are gone.)

## Pinning the rules to reality

The `LeanForm` patterns must match exactly what `Mathematica.Reflect.formatExpr`
emits — e.g. `a + b` is `@HAdd.hAdd α β γ inst a b`, i.e. **six nested `LeanApp`**,
and `2` is `@OfNat.ofNat Nat (nat_lit 2) inst`. Use the reflection probe in the user
guide (§6) to capture the exact form before writing a new rule.
