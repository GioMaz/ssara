Require Import Ssara.Base.Vm.
Require Import Ssara.Base.Syntax.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From QuickChick Require Import QuickChick.

(* Example 1 *)

Module Example1.
  Definition example_block : block :=
    Block (
      nil
    ) (
      (r(2) <- (Imm 34)) ::
      (r(3) <- r(2) * (Imm 2)) ::
      (r(4) <- r(3) + (Imm 1)) ::
      (store (Ptr 5) r(4)) ::
      (r(5) <- load (Ptr 5)) ::
      (r(6) <- r(4) < (Imm 420)) ::
      nil
    ) (
      Halt
    )
  .

  Example run_example :
    run_aux (Vm nil nil) example_block 1 =
      Vm ((2, 34%Z) :: (3, 68%Z) :: (4, 69%Z) :: (5, 69%Z) :: (6, 1%Z) :: nil)
      (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 69%Z :: nil)
  .
  Proof.
    reflexivity.
  Qed.
End Example1.

Module Exmaple2.
  CoFixpoint example_block_1 :=
    Block nil nil (Jmp example_block_2)
  with example_block_2 :=
    Block nil nil (Jmp (example_block_1))
  .

  Example run_example : run_aux (Vm nil nil) example_block_1 1000 = (Vm nil nil).
  Proof.
    reflexivity.
  Qed.
End Exmaple2.

(* Example 3 *)

Module Example3.
  Definition example_block_1 : block :=
    Block (
      (r(2) <- phi (0 :: 1 :: nil)) ::
      nil
    ) (
      (store (Ptr 0) r(2)) ::
      nil
    ) (
      Halt
    )
  .

  Definition example_block_2 : block :=
    Block (
      nil
    ) (
      (r(0) <- (Imm 34)) ::
      nil
    ) (
      Jmp example_block_1
    )
  .

  Definition example_block_3 : block :=
    Block (
      nil
    ) (
      (r(1) <- (Imm 35)) ::
      nil
    ) (
      Jmp example_block_1
    )
  .

  Example run_example_1 :
    Vm.run (Vm nil nil) (example_block_3 :: example_block_2 :: example_block_1 :: nil) 10
    = Vm ((1, 35%Z) :: (2, 35%Z) :: nil) (35%Z :: nil)
  .
  Proof.
    reflexivity.
  Qed.

  Example run_example_2 :
    Vm.run (Vm nil nil) (example_block_2 :: example_block_3 :: example_block_1 :: nil) 10
    = Vm ((0, 34%Z) :: (2, 34%Z) :: nil) (34%Z :: nil)
  .
  Proof.
    reflexivity.
  Qed.
End Example3.

Definition set_reg_P (r : reg) (c : Z) : bool :=
  let (regs, _) := (set_reg (Vm nil nil) r c) in
  existsb (fun '(r', c') => Nat.eqb r r' && Z.eqb c c') regs
.

QuickChick set_reg_P.

Definition set_cell_P (i : nat) (c : cell) : bool :=
  let (_, cells) := (set_cell (Vm nil nil) i c) in
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
  let m := Vm nil nil in
  let p := (Block nil ((r(0) <- (Imm c)) :: (store (Ptr i) r(0)) :: nil) Halt) :: nil in
  let (_, cells) := Vm.run m p 10 in
  match nth_error cells i with
  | Some c' => Z.eqb c c'
  | _ => false
  end
.

QuickChick store_P.

(*
TODO: Look into QuickChick generators and QuickChick conversion from predicates to fixpoints
*)
