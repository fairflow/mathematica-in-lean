(* ::Package:: *)

(* wolfram/lean_form.wl

   Lean 4 (mathlib4) -> Mathematica translation rules, plus the OutputFormat
   serialiser.  Port of src/lean_form.m, updated for:
     - mathlib4 operator names: HAdd.hAdd / HMul.hMul / LT.lt / ... (was
       has_add.add / has_mul.mul / has_lt.lt / ...);
     - native OfNat numerals (was bit0/bit1 towers): a numeral reflects as
       @OfNat.ofNat type (nat_lit n) inst, with the raw literal LeanLitNat[n];
     - the extra Lean-4 heterogeneous type arguments (a+b is
       @HAdd.hAdd a b g inst x y -- six arguments, so six nested LeanApp).

   The exact reflected structure is pinned against Mathematica.Reflect.formatExpr
   (see wolfram/lean_form_test.wls). *)

(* ----------------------------------------------------------------- *)
(* Name helpers                                                       *)
(* ----------------------------------------------------------------- *)

LeanName[s_String] := LeanNameMkString[s, LeanNameAnonymous];
LeanName[s_String, t_String] := LeanNameMkString[t, LeanName[s]];
LeanName[s_String, t_String, u_String] := LeanNameMkString[u, LeanName[s, t]];

UnderscoreName[LeanNameMkString[s_String, t_]] := LeanNameMkString[s <> "_1", t];
UnderscoreName[LeanNameMkNum[i_, t_]] := LeanNameMkNum[1, LeanNameMkNum[i, t]];

StringOfName[LeanNameAnonymous] := "";
StringOfName[LeanNameMkString[s_String, LeanNameAnonymous]] := s;
StringOfName[LeanNameMkString[s_String, t_]] := s <> "." <> StringOfName[t];
StringOfName[LeanNameMkNum[i_, LeanNameAnonymous]] := ToString[i];
StringOfName[LeanNameMkNum[i_, t_]] := ToString[i] <> "." <> StringOfName[t];

(* ----------------------------------------------------------------- *)
(* Numerals: @OfNat.ofNat type (nat_lit n) inst  ->  n ; raw lit -> n *)
(* ----------------------------------------------------------------- *)

LeanForm[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["OfNat", "ofNat"], _], _], LeanLitNat[n_]], _], v_] := n;
LeanForm[LeanLitNat[n_], v_] := n;

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["One", "one"], _], _], _], v_] := 1;
LeanForm[LeanApp[LeanApp[LeanConst[LeanName["Zero", "zero"], _], _], _], v_] := 0;

(* ----------------------------------------------------------------- *)
(* Binary heterogeneous arithmetic: @HOp.hOp a b g inst x y (6 args)  *)
(* ----------------------------------------------------------------- *)

LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["HAdd", "hAdd"], _], _], _], _], _], x_], y_], v_] :=
  Inactive[Plus][LeanForm[x, v], LeanForm[y, v]];

LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["HMul", "hMul"], _], _], _], _], _], x_], y_], v_] :=
  Inactive[Times][LeanForm[x, v], LeanForm[y, v]];

LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["HSub", "hSub"], _], _], _], _], _], x_], y_], v_] :=
  Inactive[Subtract][LeanForm[x, v], LeanForm[y, v]];

LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["HDiv", "hDiv"], _], _], _], _], _], x_], y_], v_] :=
  Inactive[Divide][LeanForm[x, v], LeanForm[y, v]];

LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["HPow", "hPow"], _], _], _], _], _], x_], y_], v_] :=
  Inactive[Power][LeanForm[x, v], LeanForm[y, v]];

(* unary negation: @Neg.neg a inst x  (3 args) *)
LeanForm[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["Neg", "neg"], _], _], _], x_], v_] :=
  Inactive[Times][-1, LeanForm[x, v]];

(* ----------------------------------------------------------------- *)
(* Relations                                                          *)
(* ----------------------------------------------------------------- *)

(* @Eq a x y  (3 args) *)
LeanForm[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["Eq"], _], _], x_], y_], v_] :=
  Inactive[Equal][LeanForm[x, v], LeanForm[y, v]];

(* @LT.lt a inst x y  (4 args) ; likewise LE/GT/GE *)
LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["LT", "lt"], _], _], _], x_], y_], v_] :=
  Inactive[Less][LeanForm[x, v], LeanForm[y, v]];
LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["LE", "le"], _], _], _], x_], y_], v_] :=
  Inactive[LessEqual][LeanForm[x, v], LeanForm[y, v]];
LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["GT", "gt"], _], _], _], x_], y_], v_] :=
  Inactive[Greater][LeanForm[x, v], LeanForm[y, v]];
LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[
   LeanConst[LeanName["GE", "ge"], _], _], _], x_], y_], v_] :=
  Inactive[GreaterEqual][LeanForm[x, v], LeanForm[y, v]];

(* ----------------------------------------------------------------- *)
(* Propositional connectives: And/Or (2 args), Not (1 arg)           *)
(* ----------------------------------------------------------------- *)

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["And"], _], x_], y_], v_] :=
  Inactive[And][LeanForm[x, v], LeanForm[y, v]];
LeanForm[LeanApp[LeanApp[LeanConst[LeanName["Or"], _], x_], y_], v_] :=
  Inactive[Or][LeanForm[x, v], LeanForm[y, v]];
LeanForm[LeanApp[LeanConst[LeanName["Not"], _], x_], v_] :=
  Inactive[Not][LeanForm[x, v]];

(* ----------------------------------------------------------------- *)
(* Real elementary functions                                          *)
(* ----------------------------------------------------------------- *)

LeanForm[LeanApp[LeanConst[LeanName["Real", "sin"], _], x_], v_] := Inactive[Sin][LeanForm[x, v]];
LeanForm[LeanApp[LeanConst[LeanName["Real", "cos"], _], x_], v_] := Inactive[Cos][LeanForm[x, v]];
LeanForm[LeanApp[LeanConst[LeanName["Real", "tan"], _], x_], v_] := Inactive[Tan][LeanForm[x, v]];
LeanForm[LeanConst[LeanName["Real", "pi"], _], v_] := Pi;

(* ----------------------------------------------------------------- *)
(* Constants                                                          *)
(* ----------------------------------------------------------------- *)

LeanForm[LeanConst[LeanName["True"], _], v_] := True;
LeanForm[LeanConst[LeanName["False"], _], v_] := False;

(* ----------------------------------------------------------------- *)
(* Structural pass-throughs (kept reconstructable on the Lean side)   *)
(* ----------------------------------------------------------------- *)

LeanForm[LeanSort[l_], v_] := LeanSort[l];
LeanForm[LeanMetaVar[a_, b_], v_] := LeanMetaVar[a, b];
LeanForm[LeanLocal[n_, pn_, b_, t_], v_] := LeanLocal[n, pn, b, t];
LeanForm[LeanPi[nm_, bi_, tp_, bod_], v_] := LeanPi[nm, bi, tp, bod];

LeanForm[LeanLambda[nm_, bi_, tp_, bd_], v_] :=
  If[MemberQ[v, Symbol[StringOfName[nm]]],
    LeanForm[LeanLambda[UnderscoreName[nm], bi, tp, bd], v],
    Apply[Function,
      List[Symbol[StringOfName[nm]],
        LeanForm[bd, Prepend[v, Symbol[StringOfName[nm]]]]]]];

LeanForm[LeanVar[i_], v_] := If[Length[v] > i, v[[i + 1]], LeanVar[i]];

(* unrecognised constant -> itself (must come after the specific const rules) *)
LeanForm[LeanConst[a_, b_], v_] := LeanConst[a, b];

(* unrecognised application -> recurse but keep the LeanApp wrapper so the Lean
   side can reconstruct it verbatim (the specific operator rules above are more
   specific and take precedence). *)
LeanForm[LeanApp[f_, e_], v_] := LeanApp[LeanForm[f, v], LeanForm[e, v]];

LeanForm[e_] := LeanForm[e, {}];

(* ----------------------------------------------------------------- *)
(* OutputFormat: serialise a Mathematica expression to the wire form  *)
(* consumed by Mathematica.Wire.parse.                                *)
(* ----------------------------------------------------------------- *)

OutputFormat[i_Integer] := "I[" <> ToString[i] <> "]";
OutputFormat[s_String] := "T[\"" <> s <> "\"]";
OutputFormat[s_Symbol] := "Y[" <> ToString[s] <> "]";
OutputFormat[h_[args___]] :=
  "A" <> OutputFormat[h] <> "[" <>
    StringRiffle[Map[OutputFormat, List[args]], ","] <> "]";

(* ----------------------------------------------------------------- *)
(* Graphics helpers (from the Lean 3 file; used by plotting examples) *)
(* ----------------------------------------------------------------- *)

MakeDataUrlFromImage[img_] :=
  "data:image/png;base64," <> ExportString[ExportString[Graphics[img], "PNG"], "Base64"];

PlotOverX[f_, {X_, lb_, ub_}] := Module[{nv, re},
  re = f /. X -> nv; Plot[re, {nv, lb, ub}]];

(* ----------------------------------------------------------------- *)
(* Creative telescoping (Zeilberger by ansatz)                        *)
(*                                                                    *)
(* WZCert[F, n, k] finds a first-order recurrence a0(n) F(n,k) +      *)
(* a1(n) F(n+1,k) = G(n,k+1) - G(n,k) with G = R(n,k) F(n,k), by      *)
(* undetermined coefficients (no RISC package needed): it solves for  *)
(* the recurrence coefficients a0,a1 AND the certificate R together   *)
(* (null space of the linear system), so given only the summand it    *)
(* returns {a0(n), a1(n), R(n,k)}.  Ratios are taken with             *)
(* Simplify[FunctionExpand[...]] so binomial terms reduce to rational *)
(* functions.  Certificate ansatz: cubic-in-k numerator over          *)
(* (n+1-k)^2, coefficients linear in n (enough for the binomial and   *)
(* binomial-square sums).                                             *)
(* ----------------------------------------------------------------- *)

WZCert[Fh_, n_, k_] := Module[
  {rk, rn, a0, a1, Rf, eq, num, ck, cn, vars, mat, ns, vec,
   a00, a01, a10, a11, b00, b01, b10, b11, b20, b21, b30, b31},
  rk = Simplify[FunctionExpand[Fh[n, k + 1]/Fh[n, k]]];
  rn = Simplify[FunctionExpand[Fh[n + 1, k]/Fh[n, k]]];
  a0 = a00 + a01 n;  a1 = a10 + a11 n;
  Rf[j_] := ((b30 + b31 n) j^3 + (b20 + b21 n) j^2 + (b10 + b11 n) j + (b00 + b01 n))/(n + 1 - j)^2;
  eq  = Together[a0 + a1 rn - (Rf[k + 1] rk - Rf[k])];
  num = Collect[Numerator[eq], k];
  vars = {a00, a01, a10, a11, b00, b01, b10, b11, b20, b21, b30, b31};
  ck = CoefficientList[num, k];
  cn = Flatten[CoefficientList[#, n] & /@ ck];
  mat = Normal[CoefficientArrays[cn, vars][[2]]];
  ns  = NullSpace[mat];
  If[Length[ns] =!= 1, Return[$Failed]];
  vec = First[ns];
  vec = vec * (LCM @@ (Denominator /@ vec));
  {Expand[a0 /. Thread[vars -> vec]],
   Expand[a1 /. Thread[vars -> vec]],
   Together[Rf[k] /. Thread[vars -> vec]]}];
