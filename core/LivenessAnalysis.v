From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Vm.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
Import ListNotations.

(*
  https://en.wikipedia.org/wiki/Live-variable_analysis
*)

Inductive metainst : Type :=
  | Metainst (use : list reg) (def : list reg) (live_out: list reg) (live_in: list reg)
.

CoInductive metablock : Type :=
  | Metablock (phi_args: list reg) (ms : list metainst) (succ : list metablock)
.

Definition contains (x : reg) (xs : list reg) : bool :=
  existsb (fun n => Nat.eqb x n) xs
.

Fixpoint regs_union (regs : list reg) (regs' : list reg) : list reg :=
  match regs' with
  | nil => regs
  | x :: xs =>
    if contains x regs then regs_union regs xs else x :: regs_union regs xs
  end
.

Notation "x 'U' y" :=
  (regs_union x y) (at level 50)
.

Fixpoint remove (r : reg) (regs : list reg) : list reg :=
  match regs with
  | nil => regs
  | x :: xs =>
    if Nat.eqb x r then remove r xs else x :: remove r xs
  end
.

Fixpoint regs_minus (regs : list reg) (regs' : list reg) : list reg :=
  match regs' with
  | nil => regs
  | x :: xs => regs_minus (remove x regs) xs
  end
.

Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.

(*
  This generic function is used to get the metadata of a section of
  instructions, it takes in the generic arguments, the list of instructions and
  the final live_out set which is live_out[final] := U in[j] with j ∈ succ[i].

  The function returns the list of instruction metadata and the live_out[j]
  where j is the predecessor of the first instruction of the list.
*)

Fixpoint analyze_As
  {A : Type}
  (get_args : A -> list reg)
  (get_use : A -> list reg)
  (get_def : A -> list reg)
  (is : list A)
  (final_live_out : list reg)
  : list metainst * list reg :=
  match is with
  | nil => (nil, final_live_out)
  | x :: xs =>
    let use := get_use x in
    let def := get_def x in
    let args := get_args x in
    let (is', live_out) := analyze_As get_args get_use get_def xs final_live_out in
    let live_in := args U (regs_minus live_out def) in (
      (Metainst use def live_out live_in) :: is',
      live_in
    )
  end
.

(*
  Liveness analysis of a phi instruction
  - use[i]      := {}
  - def[i]      := reg[i]
  - live_out[i] := U with j ∈ succ[i] of (live_in[j] U args[j])
  - live_in[i]  := use[i] U (live_out[i] - def[i])
*)
Definition analyze_phis (ps : list phi) (final_live_out : list reg) : list metainst * list reg :=
  analyze_As phi_args (fun _ => nil) (fun x => option_to_list (phi_reg x)) ps final_live_out
.

(*
  Liveness analysis of a generic instruction
  - use[i]      := args[i]
  - def[i]      := reg[i]
  - live_out[i] := U live_in[j] with j ∈ succ[i]
  - live_in[i]  := use[i] U (live_out[i] - def[i])
*)
Definition analyze_insts (is : list inst) (final_live_out : list reg) : list metainst * list reg :=
  analyze_As inst_args inst_args (fun x => option_to_list (inst_reg x)) is final_live_out
.

Definition analyze_jinst (j : jinst) (final_live_out : list reg) : list metainst * list reg :=
  let get_args_use (j : jinst) : list reg := option_to_list (jinst_args j) in
  analyze_As get_args_use get_args_use (fun _ => nil) (j :: nil) final_live_out
.

Module Example1.
  Definition ps: list phi := [
      r(0) <- phi [3; 4; 5];
      r(1) <- phi [6; 7; 8];
      r(2) <- phi [9; 10; 11]
    ]
  .

  Compute analyze_phis ps nil.
End Example1.

Module Example2.
  Definition is : list inst := [
      r(8) <- r(0) + (Imm 1);
      r(9) <- r(1) - (Imm 1)
    ]
  .
  (* TODO: fix this *)

  Compute analyze_insts is nil.
End Example2.

Definition analyze_block (b : block) (final_live_out : list reg) : list metainst * list reg :=
  match b with
  | Block ps is j =>
    let (m_3, final_live_out_3) := analyze_jinst j final_live_out in
    let (m_2, final_live_out_2) := analyze_insts is final_live_out_3 in
    let (m_1, final_live_out_1) := (analyze_phis ps final_live_out_2) in
    (m_1 ++ m_2 ++ m_3, final_live_out_1)
  end
.

Module Example3.
  Definition example_block : block := Block [
      r(0) <- phi [1; 2; 3]
    ] [
      r(4) <- r(0) + (Imm 1)
    ] (
      Halt
    )
  .

  Compute analyze_block example_block nil.
End Example3.

Module Example4.
  Definition example_block : block := Block [
      r(0) <- phi [2; 3; 4];
      r(1) <- phi [5; 6; 7]
    ] [
      r(8) <- r(0) + (Imm 1);
      r(9) <- r(1) - (Imm 1)
    ] (
      Halt
    )
  .

  Compute analyze_block example_block nil.
End Example4.

(* Definition analyze_program (p : program) : list metainst * list reg :=
  match p with
  | x :: nil => analyze_block
  | *)
