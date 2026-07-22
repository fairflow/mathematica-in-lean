(* ::Package:: *)

(* wolfram/lean_verify.wl

   Mathematica-side driver for the REVERSE bridge: verify a claim in Lean from a
   Wolfram session.  Pairs with the `lean_verify` executable
   (`Reverse/LeanVerify.lean`): this serialises a claim to the wire form, ships it,
   and returns the kernel-checked verdict.

   `LeanCheck[claim]`  — checks `claim`, wrapping any free (Global`) symbols in a
   `∀ … : domain` (default `"Nat"`).  Nothing is evaluated on the Wolfram side
   (`Inactivate`), so `x + y == y + x` is shipped as a claim, not collapsed to True.

   Requires `lean_form.wl` loaded first (for `OutputFormat`, `LeanName`, `LeanConst`).
   Set `$LeanRepoDir` to the repo root (default: current directory).

   Scope note: the P0 service proves with core/builtin tactics (decide, omega, rfl),
   so this checks the decidable / linear-arithmetic fragment over `Nat`/`Int`.
   Ring identities over `Real` need the richer (frontend-hosted) prover — future work. *)

If[! ValueQ[$LeanRepoDir], $LeanRepoDir = Directory[]];

(* Reflected Lean constant for the quantifier domain. *)
leanDomainType["Nat"]  := LeanConst[LeanName["Nat"], LeanLevelListNil];
leanDomainType["Int"]  := LeanConst[LeanName["Int"], LeanLevelListNil];
leanDomainType["Real"] := LeanConst[LeanName["Real"], LeanLevelListNil];

(* Free (user, i.e. Global`) symbols in a claim. *)
leanFreeVars[expr_] := DeleteDuplicates[
  Cases[expr, s_Symbol /; Context[s] === "Global`" :> s, {0, Infinity}, Heads -> False]];

(* Build the wire form: inactivate (so nothing evaluates), wrap free vars in
   ForAllTyped over `domain`, then serialise with OutputFormat.  The Lean side
   strips `Inactive` and reads the semantic heads (Equal/Plus/…). *)
SetAttributes[leanClaimWire, HoldFirst];
leanClaimWire[claim_, domain_String] := Module[{ic, vars, ty, wrapped},
  ic = Inactivate[claim];
  vars = leanFreeVars[ic];
  ty = leanDomainType[domain];
  wrapped = Fold[Inactive[ForAllTyped][#2, ty, #1] &, ic, Reverse[vars]];
  OutputFormat[wrapped]];

(* Drive the lean_verify service (one-shot; a persistent process is the
   production form).  Uses `lake env` so the executable finds its oleans. *)
leanVerifyWire[wire_String] := Module[{r},
  r = RunProcess[
    {"lake", "env", FileNameJoin[{".lake", "build", "bin", "lean_verify"}]},
    "StandardOutput", wire <> "\n", ProcessDirectory -> $LeanRepoDir];
  StringTrim[r]];

SetAttributes[LeanCheck, HoldFirst];
LeanCheck[claim_, domain_String : "Nat"] := leanVerifyWire[leanClaimWire[claim, domain]];
