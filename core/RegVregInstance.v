From Stdlib Require Import PeanoNat.
From Stdlib Require Import ListSet.
From Ssara.Core Require Import RegClass.

Definition vreg : Set := nat.

Instance reg_vreg_instance : RegClass := {|
  reg := vreg;
  reg_eqb := Nat.eqb;
  reg_eq_dec := Nat.eq_dec;
|}.

(* Set of virtual registers *)
Definition vregs_union := set_union reg_eq_dec.
Definition vregs_diff := set_diff reg_eq_dec.
Definition vregs_add := set_add reg_eq_dec.
Definition vregs_remove := set_remove reg_eq_dec.
Definition vregs_mem := set_mem reg_eq_dec.