From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import Vm.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.
From Stdlib Require Import Lists.List.

From Ssara.Core Require Import RegVregInstance.
Existing Instance reg_vreg_instance.

(* Convert option to list *)
Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.