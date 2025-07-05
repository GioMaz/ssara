From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import RegSet.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Dict.
From Ssara.Core Require Import Utils.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.

From Ssara.Core Require Import RegVregInstance.
Existing Instance reg_vreg_instance.

(* Check whether regs are neighbors of r *)
Definition are_neighbors (g : ig) (r : reg) (regs : list reg) : bool :=
  regs_mem r (dict_keys g) &&
  conjunction (fun r' => (r =? r') || regs_mem r' (dict_map g r)) regs
.

(* Check whether the neighbors of r are a clique *)
Definition is_simplicial (g : ig) (r : reg) : bool :=
  let regs := dict_map g r in
  regs_mem r (dict_keys g) &&
  conjunction (fun r' => are_neighbors g r' regs) regs
.

Definition find_next (g : ig) : option reg :=
  find (is_simplicial g) (dict_keys g)
. 

Lemma find_next_in :
  forall (g : ig) (n : reg), find_next g = Some n -> In n (dict_keys g)
.
Proof.
  intros g n. unfold find_next. apply find_some.
Qed.

From Stdlib Require Import FunInd.
From Stdlib Require Import Recdef.

Function eliminate (g : ig) {measure dict_size g} : list vreg :=
  match find_next g with
  | Some next =>
    let g := ig_remove_node g next in
    let peo := eliminate g in
    next :: peo
  | None => nil
  end
.
Proof.
  intros g n H.
  apply find_next_in in H.
  apply ig_size_decrease.
  assumption.
Qed.
