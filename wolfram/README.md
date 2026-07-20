# Mathematica side of the bridge

Lean reaches a Mathematica kernel through `Mathematica.Transport` (see
`Mathematica/Tactic.lean`). Two transports are provided.

## `Transport.wolframScript` — simplest

A fresh `wolframscript -code` per call. No server, no socket.

```lean
open Mathematica
def t : Transport := .wolframScript
  "/Applications/Wolfram.app/Contents/MacOS/wolframscript"   -- wolframscript path
  "/abs/path/to/wolfram/lean_form.wl"                        -- this dir's lean_form.wl

-- Simplify x*x  ⇝  x^2, translated back to a Lean `Expr`:
#eval show Lean.MetaM _ from do
  let x := ...
  runCommandOn t (fun s => "Activate[LeanForm[" ++ s ++ "]] // Simplify") (← someExpr)
```

## `Transport.pythonClient` — persistent socket (faster for many calls)

Start the server once, **from this directory**:

```sh
/Applications/Wolfram.app/Contents/MacOS/wolfram -noprompt -run '<<server.wl'
```

then use `Transport.pythonClient "wolfram/client.py"` (or set
`MATHEMATICA_BRIDGE_CLIENT` and use `Transport.fromEnv`).

## How it fits together

```
Expr ─formatExpr→ "LeanConst[…]" ─Transport→ LeanForm+OutputFormat ─→ wire ─Wire.parse→ MMExpr ─exprOfMMExpr→ Expr
```

- `LeanForm[…]` (in `lean_form.wl`) rewrites reflected Lean (mathlib4) terms into
  idiomatic Mathematica (`HAdd.hAdd → Plus`, `OfNat n → n`, …); unrecognised
  subterms pass through as raw `Lean…[…]` so they round-trip.
- `OutputFormat[…]` serialises the result to the terse wire grammar
  (`I[…] T[…] Y[…] A…[…]`) that `Mathematica.Wire.parse` reads.

## Files

| File | Role |
|------|------|
| `lean_form.wl` | Lean(mathlib4) → Mathematica rules + `OutputFormat` serialiser |
| `server.wl`    | persistent socket server (port of Lean 3 `server2.m`) |
| `client.py`    | Python socket relay (Lean-version-agnostic) |
| `lean_form_test.wls` | unit tests — `wolframscript -file lean_form_test.wls` |
