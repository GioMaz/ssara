Require Import Ssara.Core.Syntax.
Require Import Ssara.Core.Vm.
Require Import Ssara.Core.RegAlloc.
Require Import Ssara.Core.LivenessInfo.
Require Import Ssara.Core.InterfGraph.

Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".

(* Extract using OCaml built-in types *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "( * )" [ "" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive nat =>
  "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n = 0 then zero () else succ (n - 1))"
.
From Stdlib Require Import ExtrOcamlZInt.

(* Extract *)
Extraction "ssara.ml"
  Syntax.get_insts
  Vm.run
  Syntax.successors
.