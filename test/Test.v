From Ssara.Core Require Import IR.
Require Import Ssara.Core.Vm.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From QuickChick Require Import QuickChick.
Import ListNotations.

From Ssara.Core Require Import IRVregModule.
Import IRVreg.

(* Example 1 *)

Module Example1.
  Definition example_block : block :=
    Block 0 [
    ] [
      r(2) <- (Imm 34);
      r(3) <- r(2) * (Imm 2);
      r(4) <- r(3) + (Imm 1);
      r(5) <- Ptr 5;
      store r(5) r(4);
      r(6) <- load r(5)
    ] (
      Halt
    )
  .

  Example run_example :
    let (_, cells) := Vm.run vm_empty example_block 10 in
    cells = [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 69%Z]
  .
  Proof. reflexivity. Qed.
End Example1.

(* Example 2 *)

Module Exmaple2.
  CoFixpoint example_block_1 :=
    Block 0 nil nil (Jump example_block_2)
  with example_block_2 :=
    Block 1 nil nil (Jump example_block_1)
  .

  Example run_example : Vm.run vm_empty example_block_1 1000 = vm_empty.
  Proof. reflexivity. Qed.
End Exmaple2.

(* Example 3 *)

Module Example3.
  Definition example_block_3 : block :=
    Block 3 [
      r(2) <- phi [(0, 1); (1, 2)]
    ] [
      r(3) <- Ptr 0;
      store r(3) r(2)
    ] (
      Halt
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(0) <- (Imm 34)
    ] (
      Jump example_block_3
    )
  .

  Definition example_block_2 : block :=
    Block 2 [
    ] [
      r(1) <- (Imm 35)
    ] (
      Jump example_block_3
    )
  .

  Example run_example_1 :
    let (_, cells) := Vm.run vm_empty example_block_1 10 in
    cells = [34%Z]
  .
  Proof. reflexivity. Qed.

  Example run_example_2 :
    let (_, cells) := Vm.run vm_empty example_block_2 10 in
    cells = [35%Z]
  .
  Proof. reflexivity. Qed.
End Example3.

(* Example 4 *)
Module Example4.
  Definition example_block_3 : block :=
    Block 3 [
    ] [
      r(6) <- Ptr 0;
      store r(6) r(5)
    ] (
      Halt
    )
  .

  CoFixpoint example_block_2 : block :=
    Block 2 [
      r(2) <- phi [(0, 1); (4, 2)];  (* Iterator *)
      r(3) <- phi [(1, 1); (5, 2)]   (* Accumulator *)
    ] [
      r(4) <- r(2) - (Imm 1);
      r(5) <- r(3) * (Reg 4)
    ] (
      if r(4) <= (Imm 1) then example_block_3 else example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(0) <- Imm 6;  (* Iterator *)
      r(1) <- Reg 0   (* Accumulator *)
    ] (
      Jump example_block_2
    )
  .

  Compute
    let (regs, cells) := Vm.run vm_empty example_block_1 100 in
    (map regs [0; 1; 2; 3; 4; 5], cells)
  .
End Example4.

Definition set_reg_P (r : reg) (c : cell) : bool :=
  let (regs, _) := (set_reg vm_empty r c) in
  Z.eqb (regs r) c
.

QuickChick set_reg_P.

Definition set_cell_P (i : nat) (c : cell) : bool :=
  let (_, cells) := (set_cell vm_empty i c) in
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
  let m := vm_empty in
  let b := Block 0 nil [r(0) <- (Imm c); r(1) <- (Ptr i); store r(1) r(0)] Halt in
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
