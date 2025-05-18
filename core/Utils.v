From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Vm.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.

(* Set of registers *)
Definition reg_eq_dec : forall r r' : reg, {r = r'} + {r <> r'} := Nat.eq_dec.
Definition regs_union := set_union reg_eq_dec.
Definition regs_diff := set_diff reg_eq_dec.
Definition regs_add := set_add reg_eq_dec.
Definition regs_remove := set_remove reg_eq_dec.
Definition regs_mem := set_mem reg_eq_dec.

(* Set of labels *)
Definition l_eq_dec : forall r r' : reg, {r = r'} + {r <> r'} := Nat.eq_dec.
Definition ls_union := set_union l_eq_dec.
Definition ls_diff := set_diff l_eq_dec.
Definition ls_add := set_add l_eq_dec.

(* Convert option to list *)
Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.