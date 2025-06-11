From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import RegSet.
From Ssara.Core Require Import LivenessInfo.
From Ssara.Core Require Import Dict.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.
Import ListNotations.

From Ssara.Core Require Import RegVregInstance.
Existing Instance reg_vreg_instance.

Instance dict_ig_instance : DictClass := {|
  key := reg;
  value := set reg;
  default := nil;
  key_eq_dec := Nat.eq_dec;
|}.
Definition ig : Type := dict.

Definition ig_update_edge (f : reg -> set reg -> set reg) (r : reg) (r' : reg) (g : ig) : ig :=
  let regs  := dict_map g r in
  let g'    := dict_update g r (f r' regs) in
  let regs' := dict_map g' r' in
  dict_update g' r' (f r regs')
.
Definition ig_remove_edge := ig_update_edge regs_remove.
Definition ig_insert_edge := ig_update_edge regs_add.

Definition ig_remove_node (g : ig) (r : reg) : ig :=
  let (v, nbors) := fold_left
    (fun g_acc r' =>
      ig_remove_edge r r' g_acc)
    (dict_keys g)
    g
  in
  (regs_remove r v, nbors)
.

Definition ig_insert_edges (g : ig) (r : reg) (regs : list reg) : ig :=
  fold_left
    (fun g_acc r' => if r =? r' then g else ig_insert_edge r r' g)
    regs
    g
.

Definition ig_insert_clique (g : ig) (regs : list reg) : ig :=
  fold_left
    (fun g_acc r => (ig_insert_edges g_acc r regs))
    regs
    g
.

Definition ig_insert_instinfo (g : ig) (ii : instinfo) : ig :=
  match ii with
  | InstInfo live_in live_out =>
    ig_insert_clique (ig_insert_clique g live_in) live_out 
  end
.

Definition ig_insert_instinfos (g : ig) (iis: list instinfo) : ig :=
  fold_left (fun g' ii => ig_insert_instinfo g' ii) iis g
.

Definition get_ig_programinfo (pi : programinfo) : ig :=
  let (ls, nbors) := pi in
  fold_left
    (fun g l =>
      match nbors l with
      | Some (BlockInfo iis) => ig_insert_instinfos g iis
      | None => g
      end
    )
    ls
    dict_empty
.

Definition get_ig (p : program) (fuel : nat) : ig :=
  let (pi, _) := analyze_program p fuel in
  get_ig_programinfo pi
.

Axiom get_ig_fixpoint : program -> ig.

(*
  +-----------+
  | r1 <- ... |
  | r2 <- ... |
  +-----------+
        |
        |     +-----------+
        |     |           |
  +-----------------+     |
  | r3 <- Φ(r1, r5) |     |
  | r4 <- Φ(r2, r6) |     |
  +-----------------+     |
         |                |
  +--------------+        |
  | r5 <- r3 + 1 |        |
  | r6 <- r4 + 1 |        |
  +--------------+        |
         |                |
         +----------------+
*)

Module Example3.
  CoFixpoint example_block_3 : block :=
    Block 3 [
    ] [
      r(5) <- r(3) + (Imm 1);
      r(6) <- r(4) + (Imm 1)
    ] (
      Jmp example_block_2
    )
  with example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(1, 1); (5, 3)];
      r(4) <- phi [(2, 1); (6, 3)]
    ] [
    ] (
      Jmp example_block_3
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(1) <- (Imm 34);
      r(2) <- (Imm 35)
    ] (
      Jmp example_block_2
    )
  .

  Definition fuel : nat := 4.

  Compute
    let g := get_ig example_block_1 fuel in
    dict_list g
  .
End Example3.

Module Example4.
  CoFixpoint example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(1, 1); (5, 4)];
      r(4) <- phi [(2, 1); (6, 4)]
    ] [
    ] (
      Jmp example_block_3
    )
  with example_block_3 : block :=
    Block 3 [
    ] [
      r(5) <- r(3) + (Imm 1);
      r(6) <- r(4) + (Imm 1)
    ] (
      Jmp example_block_4
    )
  with example_block_4 : block :=
    Block 4 [
    ] [
    ] (
      Jmp example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(1) <- (Imm 34);
      r(2) <- (Imm 35)
    ] (
      Jmp example_block_2
    )
  .

  Definition fuel : nat := 4.

  Compute
    let g := get_ig example_block_1 fuel in
    dict_list g
  .
End Example4.
