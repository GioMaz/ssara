From Ssara.Core Require Import Vm.
From Ssara.Core Require Import IR.
From Ssara.Core Require Import LivenessInfo.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Peo.
From Ssara.Core Require Import Color.
From Ssara.Core Require Import Destruct.

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
  [ "0" "(fun x -> x + 1)" ]                                      (* A translation for each constructor *)
  "(fun zero succ n -> if n = 0 then zero () else succ (n - 1))"  (* Pattern matching translation *)
.                                                                 (* zero () is the branch | O => ... *)
                                                                  (* succ (n-1) is the branch | S n' => ...  or S (n-1) => ... *)
From Stdlib Require Import ExtrOcamlZInt.

(* Extract *)
Extraction "ssara.ml"

  (* Virtual machine*)
  Vm.run
  Vm.vm_empty

  (* Regalloc pipeline *)
  LivenessInfo.analyze_program
  InterfGraph.get_ig
  Peo.eliminate
  Color.get_coloring
  Color.color_program
  Destruct.ssa_destruct

  (* Example programs *)
  Color.Example1.example_block_1
  Color.Example2.example_block_1
  Color.Example3.example_block_1
  Color.Example4.example_block_1
.