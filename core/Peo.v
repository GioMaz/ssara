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
Definition are_neighbors (r : reg) (regs : list reg) (ig : InterfGraph.dict) : bool :=
  regs_mem r (InterfGraph.keys ig) &&
  fold_left
    (fun b r' =>
      b &&
      ((r =? r') ||
        regs_mem r' (InterfGraph.get ig r)))
    regs
    true
.

Definition is_simplicial (r : reg) (ig : InterfGraph.dict) : bool :=
  let regs := InterfGraph.get ig r in
  regs_mem r (InterfGraph.keys ig) &&
  fold_left (* Check whether the neighbor set of r is a clique *)
    (fun b r =>
      b &&
      are_neighbors r regs ig
    )
    regs
    true
.

Fixpoint find_next_aux (regs : list reg) (ig : InterfGraph.dict) : option reg :=
  match regs with
  | nil => None
  | r :: rs =>
    if is_simplicial r ig then Some r else find_next_aux rs ig
  end
.

Definition find_next (ig : InterfGraph.dict) : option reg :=
  find_next_aux (InterfGraph.keys ig) ig
. 

Lemma find_next_mem :
  forall (ig : InterfGraph.dict) (n : reg),
    find_next ig = Some n -> In n (InterfGraph.keys ig)
.
Proof.
  intros g n H. unfold find_next in H. generalize dependent n.
  induction (InterfGraph.keys g) as [|r rs IH].
  - intros n'. simpl. congruence.
  - intros n'. simpl.
    destruct (is_simplicial r g).
    + intros H. injection H. intro H0. left. assumption.
    + intros H. apply IH in H. right. assumption.
Qed.

From Stdlib Require Import FunInd.
From Stdlib Require Import Recdef.

Function eliminate (ig : InterfGraph.dict) {measure InterfGraph.size ig} : list vreg :=
  match find_next ig with
  | Some next =>
    let g' := ig_remove_node ig next in
    let peo := eliminate g' in
    next :: peo
  | None => nil
  end
.
Proof.
  intros g n H.
  apply find_next_mem in H.
  apply dict_size_decrease.
  assumption.
Qed.