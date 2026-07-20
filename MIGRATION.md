# Lean 3 → Lean 4 Migration Map — MM-Lean Bridge

Status: **phases 1–3 (translation core) landed.** Wire protocol, reflection
(`Expr → String`), unreflection leaves, and the **`MMExpr → MetaM Expr`
translation engine** (`Mathematica/Translate.lean`) are ported and build clean
on Lean 4 `v4.31.0` with build-time tests. The engine covers raw unreflection
(`LeanConst`/`App`/`Lambda`/`Pi`/…), semantic rules (`Plus`/`Times`/`Power`/
`Equal`/`Less`/`And`/`Or`/`Not`/`Implies`/`List`/…) via `mkAppM` (chosen over Qq
— it infers implicits + synthesises instances directly), and `MetaM` binder
telescopes (`Function`/`ForAll`/`ForAllTyped`/`Exists`). Remaining: rule
*extensibility* via env-extensions+attributes (currently a built-in table), the
user-facing tactics + transport, `lean_form.m` → mathlib4, and type-polymorphic
numerals. Target: Lean 4 (v4.31.0) + mathlib4, Mathematica 14.
Working branch: `lean4-port`. Upstream (Lean 3, dormant since 2022): `robertylewis/mathematica`.

This document maps every component to its Lean 4 equivalent, flags the structural
redesigns, folds in efficiency improvements, and proposes an ordering.

---

## 1. What the system actually does (data flow)

```
        Lean expr ──form_of_expr──▶ "LeanApp[LeanConst[LeanNameMkString[...]]]"  (a Mathematica string)
                                              │
                        execute (shell → python3 client2.py → TCP :10000)
                                              ▼
   server2.m  ── LeanForm[…] (lean_form.m) ──▶ nice MM expr (Plus/Times/…) ── evaluate ──▶ result
                                              │
                              OutputFormat  ▶  compact wire form:  A hd[args] | I[n] | T["s"] | Y[sym]
                                              ▼
        Lean mmexpr  ◀──parse_mmexpr──  wire string  (back over the socket)
                                              │
                     expr_of_mmexpr / pexpr_of_mmexpr (rule DBs) ──▶ Lean expr / pexpr
```

Two directions, two serialization formats:
- **Lean → MM (reflection):** `form_of_*` emit `Lean…[…]` head symbols; `lean_form.m` rewrites those into idiomatic Mathematica.
- **MM → Lean (unreflection):** `OutputFormat` emits the terse `A/I/T/Y` grammar; `parse_mmexpr` parses it to `mmexpr`; rule databases translate `mmexpr` → `expr`/`pexpr`.

---

## 2. File-by-file migration

| Lean 3 file | Lean 4 target | Nature of change |
|---|---|---|
| `src/mathematica_parser.lean` | `Mathematica/Wire.lean` (+ `Mathematica/MMExpr.lean`) | Parser rewrite (Parsec), `String` not `list char`, drop `char_buffer` |
| `src/mathematica.lean` | split: `Reflect.lean`, `Translate.lean`, `Rules.lean`, `Tactic.lean` | Deep metaprogramming rewrite (see §3–§7) |
| `src/lean_form.m` | `wolfram/LeanForm.wl` | mathlib4 name changes, drop bit0/bit1, `.wl` (see §8) |
| `src/server2.m` | `wolfram/Server.wl` | Keep protocol; `.wl`; de-dup `OutputFormat`; MM14 check |
| `src/client2.py` | `wolfram/client.py` (or delete — see §7) | Path fix; consider replacing with native Lean socket |
| `leanpkg.toml` | `lakefile.toml` + `lean-toolchain` | Lake + `require mathlib` |
| `.github/workflows/*` | new Lake CI | Remove `leanprover-contrib` version-bumpers; add `lake build` + `lake exe cache get` |

Naming convention shift: types → `UpperCamelCase` (`mmexpr`→`MMExpr`, `mfloat`→`MFloat`);
the `mathematica`/`tactic.mathematica` namespaces → `Mathematica` with the tactic entry points
under `Mathematica.Tactic`.

---

## 3. Lean 3 → Lean 4 core cheat-sheet (applies throughout)

| Lean 3 | Lean 4 | Note |
|---|---|---|
| `meta def` | `def` | No `meta` keyword; meta code is normal code in `MetaM`/`TacticM`/`CoreM` |
| `tactic α` | `TacticM α` / `MetaM α` | Prefer `MetaM` for pure elaboration; `TacticM` only at the tactic edge |
| `λ x, e` / `match … := …` | `fun x => e` / `match … => …` | `:=`→`=>` in lambdas & match arms |
| `expr` | `Lean.Expr` | Constructors renamed & reordered (§4) |
| `pexpr` | **(removed)** | Use `Syntax`/`TSyntax term` + `elabTerm`, or **Qq** `q(…)` (§5) |
| `` `(x) `` (expr quote) / `` ```(x) `` (pexpr quote) | `` `(x) `` → `Syntax`; `q(x)` (Qq) → `Expr` | `%%e` antiquote → `$e` |
| `rb_map`, `rb_lmap` | `Std.HashMap`, `Std.HashMap k (List v)` | O(1) avg; string keys (§6 efficiency) |
| `native` / `unsigned` | gone | Name numerals take `Nat` |
| `monad.mapm`, `list.for` | `List.mapM`, `for`/`List.map` | |
| `string` (= `list char`), `char_buffer` | `String` (UTF-8), `ByteArray`/`String` | Big efficiency change (§9) |
| `io.*`, `unsafe_run_io` | `IO.*`, direct `(← …)` in `MetaM` | No `unsafe_run_io`; meta monads lift `IO` |
| `reflect`, `string.reflect`, `nat.reflect` | `Lean.ToExpr` / `toExpr`, `mkNatLit`, `mkStrLit` | |
| `has_to_format`, `to_fmt` | `ToFormat`, `Std.Format`, `repr` | |
| `data.buffer.parser` | `Std.Internal.Parsec` (or hand-rolled) | (§ parser) |

---

## 4. `Expr` constructor mapping (exact — this is where bugs hide)

| Lean 3 | Lean 4 | Trap |
|---|---|---|
| `var i` | `.bvar i` | rename |
| `sort l` | `.sort l` | — |
| `const nm lvls` | `.const nm lvls` | — |
| `mvar nm ppnm tp` | `.mvar mvarId` | **Value no longer carries name+type** — must `mkFreshExprMVar` in `MetaM` |
| `local_const nm ppnm bi tp` | `.fvar fvarId` | **Value no longer carries data** — fvars live in `LocalContext`; build via `withLocalDecl` |
| `app f e` | `.app f e` | — |
| `lam nm bi tp bod` | `.lam nm tp bod bi` | **arg order changes** (bi moves to the end) |
| `pi nm bi tp bod` | `.forallE nm tp bod bi` | rename **and** reorder |
| `elet nm tp val bod` | `.letE nm tp val bod nonDep` | extra `nonDep : Bool` |
| `macro md args` | **(removed)** | Replaced by `.lit`, `.mdata`, `.proj` |
| — | `.lit (.natVal n)` / `.lit (.strVal s)` | **New**: native literals ⇒ drop bit0/bit1 (§ numerals) |

`Name`: `mk_string s nm` → `.str nm s` (**parent first**); `mk_numeral i nm` → `.num nm i.toNat`.
`Level`: `zero/succ/max/imax/param/mvar` map 1:1 (`level.mvar` → `.mvar : LMVarId`).
`BinderInfo`: `default/implicit/strict_implicit/inst_implicit` → `.default/.implicit/.strictImplicit/.instImplicit`.
Lean 3's `binder_info.aux_decl` (used for `BinderInfoOther`) **has no Lean 4 equivalent** — drop that case.

> **Latent bug to fix while porting:** `mmexpr_pi_to_expr` (line ~461) builds a `lam`, not a `pi`.
> Port it as `.forallE`, and add a round-trip test that would have caught it.

The `mvar`/`local_const`-as-plain-value assumption is baked into: `form_of_expr`, `pexpr.to_raw_expr`,
`pexpr.of_raw_expr`, `mk_local_const*`, `mmexpr_mvar_to_expr`, `mmexpr_local_to_expr`, and every binder
rule. This is the **single biggest redesign** — see §7.

---

## 5. The `pexpr`/`expr` split disappears

Lean 3 keeps two types: `expr` (fully elaborated) and `pexpr` (pre-terms with placeholders), plus the
`pexpr.to_raw_expr`/`of_raw_expr` bridges and `pexpr_fold_op`/`pexpr_mk_app` builders. Lean 4 has **one**
`Expr`; "pre-terms" are either `Syntax` (elaborate later) or `Expr` with metavariables.

Recommendation: adopt **Qq** (`import Qq`). Rule bodies become dramatically simpler and type-safe:

```lean
-- Lean 3:  return ``(%%base ^ %%exp)
-- Lean 4:  return q($base ^ $exp)          -- base exp : Q(…)
```

Consequences:
- Collapse the six rule databases (§6) from 3×{pexpr,expr} to **two families** keyed/unkeyed, each
  producing `Expr` (via Qq/elab). Keep the *keyed vs unkeyed* split — it's a real dispatch optimization
  (hash lookup by head symbol vs. linear scan of fallbacks).
- `pexpr_of_mmexpr` and `expr_of_mmexpr` merge into one `MMExpr → MetaM Expr` (elaboration handles the
  "unelaborated" cases). `resolve_name`/`parse_name_tac` → `Lean.resolveGlobalConstNoOverload` / `realizeGlobalName`.

---

## 6. Rule databases: user_attribute → environment extension + attribute

Lean 3 uses `@[user_attribute]` with `cache_cfg` to build cached `rb_lmap` DBs from tagged decls, and
`after_set := ensure_has_type …` to type-check taggees. Lean 4 pattern (same as `@[simp]`):

1. `initialize ext : SimpleScopedEnvExtension … ← registerSimpleScopedEnvExtension …` per DB.
2. `initialize registerBuiltinAttribute { name := `app_to_expr_keyed, add := fun decl stx kind => …}`
   — the `add` handler replaces `ensure_has_type` (check the decl's type, then `ext.add`).
3. Read back with `ext.getState (← getEnv)` instead of `attr.get_cache`.

The current six attributes:
`sym_to_pexpr`, `sym_to_expr`, `app_to_pexpr_keyed`, `app_to_expr_keyed`,
`app_to_pexpr_unkeyed`, `app_to_expr_unkeyed` → collapse to
`sym_rule`, `app_keyed_rule`, `app_unkeyed_rule` (each `Expr`-valued; §5).

`eval_expr sym_trans_pexpr_rule` (loading a decl's *value* as a runtime function) →
`Lean.Meta.evalConst` / `evalConstCheck` (unsafe; guard by the type check in `add`). Alternatively store
the taggee `Name` in the extension and `mkConst`+`elabTerm` on demand.

Efficiency: back the keyed DBs with `Std.HashMap String …` (avg O(1)); the `trans_env` (bound-var map,
Lean 3 `rb_map string expr`) → `Std.HashMap String Expr`.

---

## 7. Binder handling: the deep redesign (`MetaM` telescopes)

Lean 3 conjures free variables as *values* (`mk_local_const_placeholder`, `local_const n n bi t`) and
folds them with `lambdas`/`pis`. Lean 4 free variables are `FVarId`s that only exist inside a
`LocalContext`. The idiomatic, correct, and faster approach:

```lean
-- Function[x, body] :
withLocalDeclD xName xType fun x => do
  let b ← translate (env.insert xStr x) body
  mkLambdaFVars #[x] b          -- replaces mk_lambda'/mk_lambdas + pexpr.to_raw_expr juggling
-- ForAll → mkForallFVars ; ForAllTyped → withLocalDeclD with the given type
```

This removes `pexpr.to_raw_expr`, `pexpr.of_raw_expr`, `mk_local_const*`, `mk_lambdas`, `mk_pis`,
`mk_lambda'`, `mk_pi'`, and the `sym_to_lcp`/`sym_to_lcs_using` placeholder dance entirely, and runs in
`MetaM`. Affected rules: `Function`, `ForAll`, `ForAllTyped`, `Exists`.

`execute`/IO layer: `unsafe_run_io` → direct IO in `MetaM`; `io.buffer_cmd` → `IO.Process.output`;
`write_file`/`temp_file_name`/`exists_file` → `IO.FS.writeFile` / `IO.FS.createTempFile` /
`System.FilePath.pathExists`. The hardcoded dep path `_target/deps/mathematica/src/client2.py`
(leanpkg) must become a Lake-relative path (`.lake/packages/…` or resolve via the running module).

**Decision to make:** keep the `python3 client2.py` middleman, or have Lean 4 talk to the socket
directly (a `Socket` FFI lib) or call `wolframscript -code` per request. Native socket removes the
Python dependency and a process-spawn per call — recommended as a fast follow, not a day-one blocker.

---

## 8. Mathematica side (`.wl`, names, numerals, v14)

**Format:** the current `.m` files are already plain packages (`(* ::Package:: *)`), loaded with `<<` —
not `.nb` notebooks — so `CellChangeTimes`/`TrackCellChangeTimes` don't affect *these* files today.
Nonetheless, **standardize on `.wl`** (rename `server2.m`→`Server.wl`, `lean_form.m`→`LeanForm.wl`):
plain-text, diff-friendly, `wolframscript -file` / `<<`-runnable, and immune to notebook cell-metadata
churn by construction. Update the `<<` reference in the server and the path in the client.
For any `.nb` we *do* generate elsewhere, set `TrackCellChangeTimes -> False` (see open question in §12).

**mathlib4 name changes** — every `LeanForm` pattern in `lean_form.m` and every `sym_to_pexpr` rule in
Lean matches Lean 3 mathlib names that were renamed *and re-structured* in mathlib4:

| Lean 3 name matched | mathlib4 | Structural note |
|---|---|---|
| `has_add.add` / `add` | `HAdd.hAdd` (`Add.add`) | heterogeneous op: extra type/inst args ⇒ more `LeanApp` layers |
| `has_mul.mul`, `has_div.div`, `has_sub.sub` | `HMul.hMul`, `HDiv.hDiv`, `HSub.hSub` | as above |
| `has_neg.neg` | `Neg.neg` | |
| `has_pow.pow` / `npow` / `nat.pow` | `HPow.hPow` | one unified rule; arity differs |
| `has_one.one`/`one`, `has_zero.zero`/`zero` | `One.one`, `Zero.zero` | |
| `bit0`, `bit1` | **removed** — use `OfNat.ofNat` literals | rewrite the two numeral rules entirely |
| `list.nil`, `list.cons` | `List.nil`, `List.cons` | |
| `has_lt.lt`/`lt`, `has_le.le`/`le`, `gt`, `ge` | `LT.lt`, `LE.le`, `GT.gt`, `GE.ge` | |
| `eq` | `Eq` | |
| `real.sin/cos/tan/pi` | `Real.sin/cos/tan/pi` | verify exact mathlib4 paths |

Because mathlib4 numerals are `OfNat.ofNat n` (native `Nat` literal) rather than `bit0/bit1` towers,
**both** the Lean-side numeral emit/parse (`pexpr_of_nat`/`pexpr_of_int` → `mkNatLit`/`Int` lit) **and**
the `LeanForm` numeral rules must be rewritten. Net simplification on both sides.

**v14:** `SocketOpen`/`SocketListen`/`StringRiffle`/`StringToByteArray`/`BinaryWrite` are all fine in 14.
`OutputFormat` is duplicated in `Server.wl` and `LeanForm.wl` — keep one copy. Smoke-test the socket
server under a v14 kernel via `wolframscript`.

---

## 9. Efficiency improvements (fold into the port, don't bolt on later)

1. **Native numerals** — drop `bit0`/`bit1`/`unsigned_of_int`; `mkNatLit`, `Int` literals. Fewer nodes, faster elaboration, simpler MM rules. (biggest win)
2. **`String` over `list char`/`char_buffer`** — Lean 4 `String` is UTF-8; kills the O(n) list ops in the parser and `nat_of_string` (use `String.toNat!`/iterator).
3. **Serialization** — `form_of_*` is left-nested `++` (risking O(n²)). Build with `Std.Format` or accumulate into `Array String` + `String.intercalate`, or `s!"…"` interpolation.
4. **`Std.HashMap`** for rule DBs and `trans_env` (was `rb_map`/`rb_lmap`, O(log n)).
5. **`MetaM` telescopes** (`withLocalDeclD`/`mkLambdaFVars`) replace the `local_const` placeholder juggling — correct *and* less allocation.
6. **Parser on `String.Iterator`** (Parsec) instead of building intermediate `list char`.
7. **Process/transport** — one `python3` spawn per `execute` is the dominant latency. Options: native socket from Lean (persistent), or batch. Defer but design `execute` behind a small `Transport` interface so it can be swapped.
8. **De-dup** — `write_file`/`OutputFormat` are each defined twice; single source of truth.

---

## 10. Build system

- `lean-toolchain` pinning a Lean 4 release matched to the target mathlib4.
- `lakefile.toml`:
  ```toml
  [[require]]
  name = "mathlib"
  git  = "https://github.com/leanprover-community/mathlib4"
  # rev pinned to match lean-toolchain
  ```
- CI: replace both `leanprover-contrib` workflows (Lean-3 community version-bumping) with
  `lake exe cache get` + `lake build`.
- If Qq isn't transitively available, add `require Qq`.

---

## 11. Suggested ordering (each step independently testable)

1. ✅ **Scaffold** — `lean-toolchain` (v4.31.0), `lakefile.toml`, `Mathematica/` modules, `.gitignore`. mathlib4 + Qq intentionally deferred to the translation layer (phase 1 is dependency-free, builds offline in ~1s). CI still TODO.
2. ✅ **Wire + MMExpr** — `Mathematica/MMExpr.lean` (`MMExpr`, `MFloat`, `format`, `toWire`) + `Mathematica/Wire.lean` (hand-rolled `List Char` recursive-descent parser + `preprocess`). Build-time `#guard` round-trip tests pass, no Mathematica kernel needed. Parsec/`String.Iterator` rewrite deferred to the efficiency pass (§9).
3. ✅ **Reflection** — `Mathematica/Reflect.lean`: `formatName` / `formatLevel` / `formatBinderInfo` / `formatExpr` (`Expr → String`) in `MetaM` (resolves `fvar`/`mvar` against the context). Handles Lean 4-only `.lit`→`LeanLitNat/Str`, `.proj`→`LeanProj`, transparent `.mdata`; `let` unfolded (`expand_let`). Build-time golden `#eval` tests on closed terms + fvar/mvar structure checks. No Mathematica, no mathlib.
4. **Transport** (`execute` + `.wl` server + client): get a live round-trip echoing through Mathematica 14. Prove the socket path end-to-end before translation.
5. ⏳ **Rule infra (extensibility)** — DEFERRED. The engine currently uses a built-in rule table; porting Lean 3's `@[user_attribute]` caches to env-extensions + attributes (so users can tag their own rules) is a follow-up. The dispatcher is structured so this is a later drop-in.
6. ✅ **Unreflection + rules** — `Mathematica/Unreflect.lean` (name/level/binderInfo leaves) + `Mathematica/Translate.lean` (`exprOfMMExpr : MMExpr → MetaM Expr`): raw unreflection, semantic rules via `mkAppM`, `MetaM` binder telescopes. Build-time `#eval` tests over closed terms. `mmexpr_pi_to_expr` bug (built `lam`) fixed → `forallE`.
7. **`LeanForm.wl`**: port patterns to mathlib4 names + `OfNat` numerals.
8. **User tactics**: `run_command_on*`, `load_file`; end-to-end examples (a `Simplify`/`Solve` demo).
9. **Efficiency pass + native-socket transport** (optional).

Milestone check after step 4: a Lean term reflects out, Mathematica echoes/《LeanForm》s it, and the
wire response parses back to `MMExpr` — the plumbing is proven before the hard translation work.

---

## 12. Open questions

- **Notebook creation with `TrackCellChangeTimes`:** the bridge repo itself only ships `.m` packages, so
  the `.nb` files Matthew wants to fix must come from a *different* repo/session (his local run harness?).
  Need those pointers to set the right convention (see chat — Matthew offered to find them).
- **Transport:** keep Python client, native Lean socket, or `wolframscript -code`? (affects §7)
- **Qq vs raw `Syntax`+`elabTerm`:** confirm Qq is acceptable as a dependency (recommended).
- **mathlib4 target:** which Lean/mathlib4 release to pin?
- **Scope for v1:** full parity, or a minimal `Simplify`/`Solve`/`Plot` slice first?
