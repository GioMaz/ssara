From Ssara.Core Require Import RegAlloc.
From Ssara.Core Require Import RegClass.

(* https://xavierleroy.org/publi/parallel-move.pdf *)

From Ssara.Core Require Import RegPregInstance.
Existing Instance reg_preg_instance.

(*
  The parallel move type is defined as a list of assignments of type src -> dst
*)
Definition pmove : Type := list (reg * reg).

Inductive state : Type :=
  | State (l1 : pmove) (l2 : pmove) (l3 : pmove)
.

(* 
Function stepf (s : state) : state :=
  match s with
  | State nil nil _ => s
  | State ((src, dst) :: xs) nil l =>
    if preg_eqb src dst
    then State tl nil l
    else State tl ((src, dst) :: nil) l
  | State t ((src, dst) :: b) l =>
    match 
. *)

(* Definition phi_to_swaps (ps : list phi) (pred : block) : list inst :=
  let l := get_lbl prev in
  let ps := get_phis b in
. *)