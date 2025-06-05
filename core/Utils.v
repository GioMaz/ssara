From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import Vm.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.
From Stdlib Require Import Lists.List.

From Ssara.Core Require Import RegVregInstance.
Existing Instance reg_vreg_instance.

(* Set of virtual registers *)
Definition vreg_eq_dec : forall r r' : reg, {r = r'} + {r <> r'} := reg_eq_dec.
Definition vregs_union := set_union reg_eq_dec.
Definition vregs_diff := set_diff reg_eq_dec.
Definition vregs_add := set_add reg_eq_dec.
Definition vregs_remove := set_remove reg_eq_dec.
Definition vregs_mem := set_mem reg_eq_dec.

(* Convert option to list *)
Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.

(* Convert list option to list *)
Fixpoint list_option_to_list {A : Type} (l : list (option A)) : list A :=
  match l with
  | nil => nil
  | x :: xs =>
    match x with
    | Some y => y :: (list_option_to_list xs)
    | None => (list_option_to_list xs)
    end
  end
.