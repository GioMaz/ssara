Require Import Ssara.Core.Syntax.
Require Import Ssara.Core.Vm.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From QuickChick Require Import QuickChick.
Import ListNotations.

(* Example 1 *)

Module Example1.
  Definition example_block : block :=
    Block 0 [
    ] [
      r(2) <- (Imm 34);
      r(3) <- r(2) * (Imm 2);
      r(4) <- r(3) + (Imm 1);
      store (Ptr 5) r(4);
      r(5) <- load (Ptr 5);
      r(6) <- r(4) < (Imm 420)
    ] (
      Halt
    )
  .

  Example run_example :
    match Vm.run vm_new example_block 1 with
    | Vm _ cells => cells = [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 69%Z]
    end
  .
  Proof.
    reflexivity.
  Qed.
End Example1.

(* Example 2 *)

Module Exmaple2.
  CoFixpoint example_block_1 :=
    Block 0 nil nil (Jmp example_block_2)
  with example_block_2 :=
    Block 1 nil nil (Jmp (example_block_1))
  .

  Example run_example : Vm.run vm_new example_block_1 1000 = vm_new.
  Proof.
    reflexivity.
  Qed.
End Exmaple2.

(* Example 3 *)

Module Example3.
  Definition example_block_3 : block :=
    Block 3 [
      r(2) <- phi [(0, 1); (1, 2)]
    ] [
      store (Ptr 0) r(2)
    ] (
      Halt
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(0) <- (Imm 34)
    ] (
      Jmp example_block_3
    )
  .

  Definition example_block_2 : block :=
    Block 2 [
    ] [
      r(1) <- (Imm 35)
    ] (
      Jmp example_block_3
    )
  .

  Compute Vm.run vm_new example_block_1 10.
  Example run_example_1 :
    let (_, cells) := Vm.run vm_new example_block_1 10 in
    cells = [34%Z]
  .
  Proof.
    reflexivity.
  Qed.

  Example run_example_2 :
  let (_, cells) := Vm.run vm_new example_block_2 10 in
  cells = [35%Z]
  .
  Proof.
    reflexivity.
  Qed.
End Example3.

Definition set_reg_P (r : reg) (c : cell) : bool :=
  let (regs, _) := (set_reg vm_new r c) in
  Z.eqb (regs r) c
.

QuickChick set_reg_P.

Definition set_cell_P (i : nat) (c : cell) : bool :=
  let (_, cells) := (set_cell vm_new i c) in
  match nth_error cells i with
  | Some c' => Z.eqb c c'
  | _ => false
  end
.

QuickChick set_reg_P.

(*
  Check whether after a store the ith cell actually contains the intended value
*)
Definition store_P (i : nat) (c : cell) : bool :=
  let m := vm_new in
  let b := Block 0 nil [r(0) <- (Imm c); store (Ptr i) r(0)] Halt in
  let (_, cells) := Vm.run m b 10 in
  match nth_error cells i with
  | Some c' => Z.eqb c c'
  | _ => false
  end
.

QuickChick store_P.

(*
TODO: Look into QuickChick generators and QuickChick conversion from predicates to fixpoints
*)