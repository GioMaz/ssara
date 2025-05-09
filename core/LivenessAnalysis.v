From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Vm.
From Stdlib Require Import Lists.List.

(*
  https://en.wikipedia.org/wiki/Live-variable_analysis
*)

Inductive metainst : Type :=
  | Metainst (use : list reg) (def : list reg) (live_out: list reg) (live_in: list reg)
.

CoInductive metablock : Type :=
  | Metablock (ms : list metainst) (succ : list metablock)
.

Definition contains (x : reg) (xs : list reg) : bool :=
  existsb (fun n => Nat.eqb x n) xs
.

Fixpoint reg_union (regs : list reg) (regs' : list reg) : list reg :=
  match regs' with
  | nil => regs
  | x :: xs =>
    if contains x regs then reg_union regs xs else x :: reg_union regs xs
  end
.

Fixpoint remove (r : reg) (regs : list reg) : list reg :=
  match regs with
  | nil => regs
  | x :: xs =>
    if Nat.eqb x r then remove r xs else x :: remove r xs
  end
.

Fixpoint reg_minus (regs : list reg) (regs' : list reg) : list reg :=
  match regs' with
  | nil => regs
  | x :: xs => reg_minus (remove x regs) xs
  end
.

Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.

(*
  Liveness analysis of a phi instruction
  - use[i]      := empty
  - def[i]      := reg[i]
  - live_out[i] := U in[j] with j ∈ succ[i]
  - live_in[i]  := use[i] U (out[i] - def[i])
*)

(*
  This generic function is used to get the metadata of a section of
  instructions, it takes in the generic arguments, the list of instructions and
  the final live_out set which is live_out[final] := U in[j] with j ∈ succ[i]
*)

Fixpoint analyze_As
  {A : Type}
  (get_reg : A -> list reg)
  (get_args : A -> list reg)
  (is : list A)
  (final_live_out : list reg)
  : list metainst * list reg :=
  match is with
  | nil => (nil, final_live_out)
  | x :: xs =>
    let use := get_args x in
    let def := get_reg x in
    let (is', live_out) := analyze_As get_reg get_args xs final_live_out in
    let live_in := reg_union use (reg_minus final_live_out def) in (
      (Metainst use def final_live_out live_in) :: is',
      live_in
    )
  end
.

Definition analyze_phis (ps : list phi) (final_live_out : list reg) : list metainst * list reg :=
  analyze_As (fun x => option_to_list (phi_reg x)) (fun _ => nil) ps final_live_out
.

Definition analyze_insts (is : list inst) (final_live_out : list reg) : list metainst * list reg :=
  analyze_As (fun x => option_to_list (inst_reg x)) inst_args is final_live_out
.

Definition analyze_jinst (j : jinst) (final_live_out : list reg) : list metainst * list reg :=
  analyze_As (fun _ => nil) (fun x => option_to_list (jinst_args x)) (j :: nil) final_live_out
.

Definition analyze_block (b : block) (final_live_out : list reg) : list metainst * list reg :=
  match b with
  | Block ps is j =>
    let (m_1, final_live_out_1) := analyze_jinst j final_live_out in
    let (m_2, final_live_out_2) := analyze_insts is final_live_out_1 in
    let (m_3, final_live_out_3) := (analyze_phis ps final_live_out_2) in
    (m_1 ++ m_2 ++ m_3, final_live_out_3)
  end
.

(* Definition analyze_program (p : program) : list metainst * list reg :=
  match p with
  | x :: nil => analyze_block
  |  *)

(* 
Fixpoint analyze_block : (b : block) (live_in : list reg) : metablock :=
  match b with
  | nil =>  *)