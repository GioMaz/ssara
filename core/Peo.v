From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import RegSet.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Dict.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.

From Ssara.Core Require Import RegVregInstance.
Existing Instance reg_vreg_instance.

(* Check whether regs are neighbors of r *)
Definition are_neighbors (r : reg) (regs : list reg) (g : ig) : bool :=
  regs_mem r (dict_keys g) &&
  fold_left
    (fun b r' =>
      b &&
      ((r =? r') ||
        regs_mem r' (ig_map g r)))
    regs
    true
.

Definition is_simplicial (r : reg) (g : ig) : bool :=
  let regs := ig_map g r in
  regs_mem r (dict_keys g) &&
  fold_left (* Check whether the neighbor set of r is a clique *)
    (fun b r =>
      b &&
      are_neighbors r regs g
    )
    regs
    true
.

Fixpoint find_next_aux (regs : list reg) (g : ig) : option reg :=
  match regs with
  | nil => None
  | r :: rs =>
    if is_simplicial r g then Some r else find_next_aux rs g
  end
.

Definition find_next (g : ig) : option reg :=
  find_next_aux (dict_keys g) g
. 

Lemma find_next_mem :
  forall (g : ig) (n : reg), find_next g = Some n -> In n (dict_keys g)
.
Proof.
  intros g n H. unfold find_next in H. generalize dependent n.
  induction (dict_keys g) as [|r rs IH].
  - intros n'. simpl. congruence.
  - intros n'. simpl.
    destruct (is_simplicial r g).
    + intros H. injection H. intro H0. left. assumption.
    + intros H. apply IH in H. right. assumption.
Qed.

From Stdlib Require Import FunInd.
From Stdlib Require Import Recdef.

Function eliminate (g : ig) {measure dict_size g} : ig * list vreg :=
  match find_next g with
  | Some next =>
    let g' := ig_remove_node g next in
    let (g'', peo) := eliminate g' in
    (g'', next :: peo)
  | None => (g, nil)
  end
.
Proof.
  intros g n H.
  apply find_next_mem in H.
  apply dict_size_decrease.
  assumption.
Qed.