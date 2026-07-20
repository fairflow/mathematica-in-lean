#!/usr/bin/env wolframscript
(* wolfram/lean_form_test.wls
   Unit tests for lean_form.wl: feed it exact Mathematica.Reflect.formatExpr
   outputs (captured from the Lean side) and check LeanForm + OutputFormat.
   Run:  wolframscript -file wolfram/lean_form_test.wls *)

$dir = DirectoryName[$InputFileName] <> "/";
Get[$dir <> "lean_form.wl"];

allOk = True; n = 0;
assert[lbl_, b_] := (n++; If[! TrueQ[b], allOk = False];
  Print[If[TrueQ[b], "ok   ", "FAIL "], lbl]);

(* ---- exact reflected inputs (Nat), from Mathematica.Reflect.formatExpr ---- *)

ofNat1 = LeanApp[LeanApp[LeanApp[LeanConst[LeanNameMkString["ofNat", LeanNameMkString["OfNat", LeanNameAnonymous]], LeanLevelListCons[LeanZeroLevel, LeanLevelListNil]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanLitNat[1]], LeanApp[LeanConst[LeanNameMkString["instOfNatNat", LeanNameAnonymous], LeanLevelListNil], LeanLitNat[1]]];

hAdd12 = LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[LeanConst[LeanNameMkString["hAdd", LeanNameMkString["HAdd", LeanNameAnonymous]], LeanLevelListCons[LeanZeroLevel, LeanLevelListCons[LeanZeroLevel, LeanLevelListCons[LeanZeroLevel, LeanLevelListNil]]]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanApp[LeanApp[LeanConst[LeanNameMkString["instHAdd", LeanNameAnonymous], LeanLevelListCons[LeanZeroLevel, LeanLevelListNil]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanConst[LeanNameMkString["instAddNat", LeanNameAnonymous], LeanLevelListNil]]], LeanApp[LeanApp[LeanApp[LeanConst[LeanNameMkString["ofNat", LeanNameMkString["OfNat", LeanNameAnonymous]], LeanLevelListCons[LeanZeroLevel, LeanLevelListNil]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanLitNat[1]], LeanApp[LeanConst[LeanNameMkString["instOfNatNat", LeanNameAnonymous], LeanLevelListNil], LeanLitNat[1]]]], LeanApp[LeanApp[LeanApp[LeanConst[LeanNameMkString["ofNat", LeanNameMkString["OfNat", LeanNameAnonymous]], LeanLevelListCons[LeanZeroLevel, LeanLevelListNil]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanLitNat[2]], LeanApp[LeanConst[LeanNameMkString["instOfNatNat", LeanNameAnonymous], LeanLevelListNil], LeanLitNat[2]]]];

eq11 = LeanApp[LeanApp[LeanApp[LeanConst[LeanNameMkString["Eq", LeanNameAnonymous], LeanLevelListCons[LeanLevelSucc[LeanZeroLevel], LeanLevelListNil]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanApp[LeanApp[LeanApp[LeanConst[LeanNameMkString["ofNat", LeanNameMkString["OfNat", LeanNameAnonymous]], LeanLevelListCons[LeanZeroLevel, LeanLevelListNil]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanLitNat[1]], LeanApp[LeanConst[LeanNameMkString["instOfNatNat", LeanNameAnonymous], LeanLevelListNil], LeanLitNat[1]]]], LeanApp[LeanApp[LeanApp[LeanConst[LeanNameMkString["ofNat", LeanNameMkString["OfNat", LeanNameAnonymous]], LeanLevelListCons[LeanZeroLevel, LeanLevelListNil]], LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil]], LeanLitNat[1]], LeanApp[LeanConst[LeanNameMkString["instOfNatNat", LeanNameAnonymous], LeanLevelListNil], LeanLitNat[1]]]];

lamXX = LeanLambda[LeanNameMkString["x", LeanNameAnonymous], BinderInfoDefault, LeanConst[LeanNameMkString["Nat", LeanNameAnonymous], LeanLevelListNil], LeanVar[0]];

(* ---- LeanForm ---- *)
Print["== LeanForm =="];
assert["OfNat 1 -> 1", LeanForm[ofNat1] === 1];
assert["HAdd 1 2 -> Inactive[Plus][1,2]", LeanForm[hAdd12] === Inactive[Plus][1, 2]];
assert["HAdd activates to 3", Activate[LeanForm[hAdd12]] === 3];
assert["Eq 1 1 -> Inactive[Equal][1,1]", LeanForm[eq11] === Inactive[Equal][1, 1]];
assert["lambda x.x -> Function[...]", Head[LeanForm[lamXX]] === Function];

(* ---- OutputFormat ---- *)
Print["== OutputFormat =="];
assert["OF integer", OutputFormat[5] === "I[5]"];
assert["OF string", OutputFormat["hi"] === "T[\"hi\"]"];
assert["OF symbol", OutputFormat[Plus] === "Y[Plus]"];
assert["OF application", OutputFormat[foo[1, "x"]] === "AY[foo][I[1],T[\"x\"]]"];
(* a full serialisable answer: Plus[1,2] activated then re-emitted *)
assert["OF on Plus[1,2]", OutputFormat[Plus[1, 2]] === "I[3]"];

Print[""];
Print[If[allOk, "ALL OK (" <> ToString[n] <> " assertions)", "*** FAILURES ***"]];
If[! allOk, Exit[1]];
