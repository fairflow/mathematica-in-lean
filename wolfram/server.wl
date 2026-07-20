(* ::Package:: *)

(* wolfram/server.wl — persistent socket server (port of src/server2.m).

   The Transport.wolframScript path (a fresh `wolframscript -code` per call) needs
   none of this and is the simplest way to use the bridge.  This server is the
   faster alternative when issuing many calls: one long-lived kernel that the
   Python client (wolfram/client.py) relays to over a socket.

   Start it headless:
     /Applications/Wolfram.app/Contents/MacOS/wolfram -noprompt -run '<<"server.wl"'
   (run from this directory, or pass an absolute path).  It listens on TCP 10000;
   the client sends an `&!`-terminated command plus a global-context flag digit,
   and reads back a length-prefixed, OutputFormat-serialised response. *)

$ContextPath = Append[$ContextPath, "MyGlobalContext`"];
$Context = "MyGlobalContext`";
mgc = "MyGlobalContext`";
ClearAll["Global`*"];

(* Relative load: run this server from the wolfram/ directory (client.py does,
   launching `wolfram ... -run '<<server.wl'` from here). *)
Get["lean_form.wl"];

(* Windows drive-path handling (kept from the Lean 3 server). *)
WindowsDirQ[s_String] := StringTake[s, 1] != "/";
ToWindowsDir[s_String] :=
  If[WindowsDirQ[s], s,
    With[{t = StringTake[s, {2}]}, FileNameJoin[{t <> ":" <> StringDrop[s, 2]}]]];
DirectoryFormat[s_String] := If[WindowsDirQ[Directory[]], ToWindowsDir[s], s];

sock = SocketOpen[10000];
Print["lean-mathematica server listening on port 10000"];

resp = "";

(* Socket "Data" arrives as a ByteArray; accumulate its text. *)
AccumulateResponse[data_] :=
  resp = resp <> If[Head[data] === ByteArray, ByteArrayToString[data], ToString[data]];

(* A full command ends with "&!" followed by the one-char global flag. *)
ResponseCompleteQ[] := StringLength[resp] >= 3 && StringTake[resp, {-3, -2}] == "&!";

CreateResponse[] :=
  Module[{o, g = ToExpression[StringTake[resp, -1]], xct},
    xct = If[g == 0, "LeanLinkCtx`", mgc];
    $Context = xct;
    o = ToExpression[StringDrop[StringReplace[resp, "&&" -> "&"], -3]] // OutputFormat;
    $Context = mgc;
    ClearAll["Global`*"];
    ClearAll["LeanLinkCtx`*"];
    resp = "";
    StringToByteArray[o]];

SocketListen[sock,
  (AccumulateResponse[#["Data"]];
   If[ResponseCompleteQ[],
     With[{out = CreateResponse[]},
       WriteString[#["SourceSocket"], ToString[Length[out]] <> " "];
       BinaryWrite[#["SourceSocket"], out]]])&];
