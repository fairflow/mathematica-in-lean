# Design: the reverse bridge — Mathematica users calling Lean

*Status: design draft. Nothing here is built yet. This is the write-up of "big
bet #2": letting someone who lives in a Wolfram notebook get Lean-level certainty
without leaving Mathematica.*

---

## 1. Motivation

Everything the bridge does today is **Lean calling Mathematica**, with Mathematica
as an *unsound oracle* — `mathematica_simp` even records a `Mathematica.trust`
axiom. That serves a Lean user reaching out for computation. It does nothing for a
**Mathematica-native user**, who never opens a `.lean` file.

The reverse bridge flips the roles. Mathematica is famously willing to hand you an
answer with **no guarantee** — `Integrate` returns a closed form, `Simplify`
asserts an identity, `Solve` gives roots — and the user has no cheap way to know
it is *correct* (branch cuts, domain assumptions, silent edge cases). Lean, with
mathlib, is a trusted checker. So:

> **Mathematica computes; Lean certifies.** The notebook user gets a machine-checked
> yes/no on the thing Mathematica just claimed, from inside Mathematica.

This is also the *sound* direction. In `mathematica_simp`, Mathematica is trusted.
Here, **Lean is the trusted party** — its kernel checks the proof — and the trust
axiom disappears entirely. `mathematica_ring` already showed the appetite for this
on the Lean side; the reverse bridge brings it to the Mathematica side.

## 2. What already exists (the pleasant surprise)

The Mathematica → Lean *data path is already built and tested*, because the current
bridge needs it to read Mathematica's answers back:

| stage | module (existing) | direction |
|---|---|---|
| serialise a Mathematica expr to the wire form | `wolfram/lean_form.wl` — `OutputFormat` | MM → wire |
| parse the wire form into an AST | `Mathematica/Wire.lean` — `Wire.parse` | wire → `MMExpr` |
| translate the AST to a Lean `Expr` | `Mathematica/Translate.lean` — `exprOfMMExpr` | `MMExpr` → `Expr` |
| reflect a Lean answer back out | `Mathematica/Reflect.lean` + `LeanForm` | Lean → wire → MM |

`exprOfMMExpr` already maps `Plus/Times/Power/Equal/Less/And/ForAll/…` to the right
mathlib operators and builds binder telescopes. So a Mathematica claim like
`x^2 == y^2 + 2 y + 1`, once serialised by `OutputFormat`, becomes a Lean `Expr` **with
today's code**. What is missing is not translation — it is (a) a way to *run* Lean as
a service, and (b) a Mathematica-side front end.

## 3. The two new components

```
  Wolfram notebook                          Lean service (headless, mathlib loaded once)
  ────────────────                          ────────────────────────────────────────────
  LeanCheck[claim]                          reads a wire-form claim on stdin
     │  auto-bind free symbols                 │  Wire.parse → exprOfMMExpr → Expr : Prop
     │  ForAll[{x,y}, claim]  (type ℝ)         │  run a proving pipeline (see §5)
     │  OutputFormat[…]  → wire string   ─────▶│  build proof term; collect #print axioms
     │                                         │  serialise a verdict (Association)
     ◀──────────────────────────────────────  │
  <| "status"->"Verified",                     ▼
     "axioms"->{…}, "ms"->12 |>            writes the verdict to stdout
```

### 3a. Lean-side: a persistent verification server

A new executable (`lean-verify`, a Lake `@[default_target]` or `lake exe`) that:

1. **Imports mathlib once at startup** and then loops — this is the crucial cost
   amortisation, exactly mirroring `Transport.persistentKernel` but in the other
   direction (there, one long-lived `WolframKernel`; here, one long-lived Lean
   process). Cold mathlib import is seconds; per-query must be milliseconds.
2. Reads a framed wire-form claim on stdin (reuse the `<MMS>…<MME>` markers).
3. `Wire.parse` → `exprOfMMExpr [] ·` → an `Expr`. Elaborate/typecheck it as a
   `Prop` (`isProp`; synthesise instances via the existing `mkAppM`-based rules).
4. Runs the **proving pipeline** (§5) inside `MetaM`/`TacticM` on the goal.
5. Writes back a verdict: status ∈ {`Verified`, `Refuted`, `Unknown`}, the axiom
   set from the constructed proof (so the user sees `trust` is *absent*), the
   tactic that closed it, and timing.

Reuses verbatim: `Wire`, `Translate`, `Unreflect`, `Reflect`, the transport marker
framing. New Lean code is small: the `main` loop, the elaboration wrapper, the
pipeline driver, and verdict serialisation.

### 3b. Mathematica-side: a small paclet

A `Lean` package exposing notebook-level functions. Sketch:

```wolfram
Needs["Lean`"]

LeanCheck[x^2 - 1 == (x-1)(x+1)]        (* ⇒ "Verified" (∀ x ∈ ℝ)          *)
LeanCheck[Sin[x]^2 + Cos[x]^2 == 1]     (* ⇒ "Verified"                     *)
LeanCheck[x^2 >= 0]                      (* ⇒ "Verified" (nlinarith)         *)
LeanCheck[x + 1 == x]                    (* ⇒ "Refuted"                      *)

LeanVerify[Integrate[2 x, x], x^2]       (* did Mathematica integrate right? *)
LeanValueQ[GCD[126, 84] == 42]           (* closed numeric fact via decide   *)
```

Responsibilities of the paclet:

- **Free-symbol handling.** `exprOfMMExpr` needs closed props (a bare `x` has no
  Lean meaning). `LeanCheck` detects free symbols, wraps the claim in
  `ForAll[{vars}, claim]`, and picks a domain type (default ℝ; overridable
  `LeanCheck[claim, Integers]`). `ForAll`/`ForAllTyped` already exist in
  `exprOfMMExpr`, which builds the `∀ x : ℝ, …` telescope.
- **Serialise + transport.** `OutputFormat[claim']` → wire; send to the Lean
  service; read the verdict; present it as an `Association` (or a coloured
  `Verified`/`Refuted` label in the notebook).
- **Manage the service.** Start `lean-verify` on first use, keep the handle in a
  package symbol, reuse it (mirror of `defaultTransport`'s lazy `kernelRef`).

The verdict crosses back as a Mathematica-readable `Association` string the paclet
`ToExpression`s — no new parser needed on the Wolfram side.

## 4. Transport

Reuse the persistent-process-over-stdio pattern already proven for the kernel, run
in reverse:

- **Persistent Lean service** (default): one `lean-verify`, mathlib loaded once,
  stdio framed with `<MMS>…<MME>`, one query at a time (a WL-side lock if the
  notebook parallelises). This is the direct dual of `Transport.persistentKernel`.
- **One-shot** (`lake env lean` per call): trivial to implement, but pays the
  mathlib import every call — fine for a demo, unusable interactively. Dual of
  `Transport.wolframScript`.

No Python, no socket — same justification as the forward bridge.

## 5. The proving pipeline

Given the elaborated goal `⊢ P`, try a fixed ladder and report the first success
(and which rung won):

1. `decide` / `Nat`/`Int` `norm_num` — closed decidable & numeric facts
   (`GCD[126,84]==42`, `Prime[97]`).
2. `ring1` — commutative-ring identities (`x^2-1 == (x-1)(x+1)`). *Sound, no oracle.*
3. `field_simp; ring1` — rational-function identities.
4. `norm_num [Real.sin_sq_add_cos_sq]` / targeted `simp` sets — the standard
   trig/special-function identities.
5. `positivity` / `nlinarith` — inequalities (`x^2 >= 0`).
6. (optional, later) `polyrith` / `mathematica_ring`'s own certificate search —
   closing the loop: Lean asks Mathematica for a certificate to verify Mathematica.

Everything the pipeline closes yields a real proof term, so the returned axiom set
is the actual trust story — kernel-checked, no oracle. A goal nothing closes comes
back `Unknown` (not a false "Refuted"). `Refuted` is reserved for goals whose
**negation** the pipeline proves (e.g. `decide` on a false decidable prop, or a
`norm_num`-refuted numeric claim).

**Counterexamples (stretch).** For a refuted decidable/finite claim, mathlib's
`decide`/`Finset` search can sometimes surface a witness; report it via the same
Lean → wire → `LeanForm` path so it lands back in the notebook as a Mathematica
expression. General counterexample synthesis is out of scope for v1.

## 6. Trust model (the whole point)

- **Forward bridge:** Lean trusts Mathematica → `Mathematica.trust` axiom.
- **Reverse bridge:** Mathematica trusts **Lean's kernel** → *no* new axiom; the
  verdict carries the exact `#print axioms` list so the user sees it resting only
  on `propext / Classical.choice / Quot.sound`.

The one caveat to surface in the UI: correctness is *modulo the translation* — the
guarantee is "the Lean proposition `exprOfMMExpr` produced is a theorem," and that
proposition must faithfully mean what the notebook wrote. The
default-type and free-symbol wrapping (`∀ x : ℝ`) are part of that contract and
must be shown to the user (e.g. echo the elaborated Lean statement back). This is
the reverse-direction analogue of the forward bridge's operator-coverage limit.

## 7. Phased plan

- **P0 — spike: ✅ built** (`Reverse/LeanVerify.lean`, `lake exe lean_verify`). A
  stdio loop that imports mathlib **once**, then per line: `Wire.parse` →
  `exprOfMMExpr` → a core-tactic pipeline → **adds the proof to the kernel** →
  prints a verdict with the axiom set. Verified live:

  ```text
  $ lake exe lean_verify   (feeding wire-form claims on stdin)
  AY[Equal][AY[Plus][I[1],I[1]],I[2]]            ⇒ VERIFIED by=decide axioms=[]
  AY[Equal][AY[Plus][I[1],I[1]],I[3]]            ⇒ REFUTED  by=¬·decide
  ∀ n m : ℕ, n + m = m + n   (as wire)           ⇒ VERIFIED by=omega axioms=[propext,Quot.sound]
  ```

  No `Mathematica.trust` in any axiom set — the reverse direction is sound by
  construction. **Two findings that shape P1:**
  1. `importModules` must be called with `loadExts := true` (after
     `enableInitializersExecution`), or the instance discrimination tree is empty
     and even `HAdd Nat Nat` fails to synthesise.
  2. **Imported mathlib `elab` tactics (`ring1`, `norm_num`, `nlinarith`) do not
     dispatch in a standalone `importModules` process** — the elaborator is found,
     but its generated quotation-matcher throws `unsupportedSyntax` under the
     interpreter (and the delaborator can segfault). Only core/builtin tactics
     (`decide`, `omega`, `rfl`) are reliable here. So P1 must **host the prover
     inside the real elaboration frontend** (drive a persistent `lean` worker via
     `Language.process`, or compile the wanted tactic set into the service binary)
     rather than extend this hand-rolled loop. The same `evalTactic ring1` runs
     fine under `lean` itself, confirming the frontend is the fix.
- **P1 — MVP paclet:** `LeanCheck[expr]` with free-symbol → `ForAll[…,ℝ]` wrapping,
  persistent service management, `Verified/Refuted/Unknown` + axiom list. Ships the
  headline demo: verify a Mathematica identity from a notebook.
- **P2 — coverage:** the full pipeline (§5), `LeanVerify[result, expected]` for
  checking `Integrate`/`Solve` output, domain-type option, elaborated-statement
  echo-back.
- **P3 — polish:** counterexamples where decidable, notebook-friendly formatting,
  batch `LeanCheck /@ {…}`, and (fun) `mathematica_ring`-style certificate check so
  Lean verifies Mathematica *using* Mathematica.

## 8. Open questions (good ones to put to Rob)

1. **Default domain.** Auto-wrap free symbols as `∀ _ : ℝ`? Offer ℚ/ℤ/ℂ? Infer from
   the expression (e.g. `Mod`/`GCD` ⇒ ℤ)? Getting this wrong makes a true claim
   look false, so the elaborated statement must always be shown.
2. **Scope of "Refuted".** Only when the negation is *proved*, never on pipeline
   failure — agreed? (Avoids calling a hard-but-true claim false.)
3. **Elaboration hardening.** Running `exprOfMMExpr` on arbitrary notebook input is
   more adversarial than on Mathematica's own answers. Where do we cap
   depth/time, and how do parse/elaboration failures present in the notebook?
4. **Distribution.** Ship the paclet on the Wolfram side and a prebuilt
   `lean-verify` — or expect users to `lake build` it? Affects how "out of the box"
   this feels to a pure-Mathematica user.

---

*Cross-refs: forward transport & persistence — [`Mathematica/Tactic.lean`](../Mathematica/Tactic.lean);
MM→Lean translation reused wholesale — [`Mathematica/Translate.lean`](../Mathematica/Translate.lean),
[`Mathematica/Wire.lean`](../Mathematica/Wire.lean); the sound-checking precedent —
[`Mathematica/Ring.lean`](../Mathematica/Ring.lean); serialisation rules —
[`wolfram/lean_form.wl`](../wolfram/lean_form.wl).*
