Require Import Ssara.Core.Vm.
Require Import Ssara.Core.LivenessAnalysis.

Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".

(* Extract using OCaml built-in types *)
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => "int" [ "0" "(fun x -> x + 1)" ] "(fun zero succ n -> if n = 0 then zero () else succ (n - 1))".

(* Extract *)
Extraction "ssara.ml" Vm.run LivenessAnalysis.get_ig.