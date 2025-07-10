From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Dict.
From Ssara.Core Require Import Utils.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.

From Ssara.Core Require Import IRVregModule.
Import IRVreg.

(* Check whether regs are neighbors of r *)
Definition are_neighborsb (g : InterfGraph.dict) (r : reg) (regs : list reg) : bool :=
  regs_mem r (InterfGraph.keys g) &&
  conjunction (fun r' => (r =? r') || regs_mem r' (InterfGraph.get g r)) regs
.

(* Check whether the neighbors of r are a clique *)
Definition is_simplicialb (g : InterfGraph.dict) (r : reg) : bool :=
  let nbors := InterfGraph.get g r in
  regs_mem r (InterfGraph.keys g) &&
  conjunction (fun r' => are_neighborsb g r' nbors) nbors
.

Definition find_next (g : InterfGraph.dict) : option reg :=
  find (is_simplicialb g) (InterfGraph.keys g)
.

Lemma find_next_in :
  forall (g : InterfGraph.dict) (n : reg), find_next g = Some n -> In n (InterfGraph.keys g)
.
Proof.
  intros g n. unfold find_next. apply find_some.
Qed.

From Stdlib Require Import FunInd.
From Stdlib Require Import Recdef.

Function eliminate (g : InterfGraph.dict) {measure InterfGraph.size g} : list reg :=
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

(*
  Proof of correctness of the algorithm that is, the result of the eliminate
  function is actually a PEO.
  We start by defining a lemma proving the correctness of a single iteration of
  the eliminate function, that is proving that `find_next` actually returns a
  simplicial node.
*)
Lemma find_next_simplicial :
  forall (g : InterfGraph.dict) (r : reg),
    find_next g = Some r -> is_simplicialb g r = true
.
Proof.
  intros g r. unfold find_next. apply find_some.
Qed.

(* Now we define a predicate for the simplicial property *)
Definition is_simplicial (g : InterfGraph.dict) (r : reg) : Prop :=
  let nbors := InterfGraph.get g r in
  forall (n n': reg),
    In n (InterfGraph.keys g) /\ In n' (InterfGraph.keys g) ->
    In n (InterfGraph.get g n') /\ In n' (InterfGraph.get g n)
.

(*
  And the we prove that the `is_simplicialb` function satisfies the
  `is_simplicial` predicate.
*)
(*Lemma is_simplicialb_is_simplicial :
  forall (g : InterfGraph.dict) (r : reg),
    is_simplicialb g r = true -> is_simplicial g r
.
Proof.
  intros g r. unfold is_simplicialb.*)

(* Fixpoint split_by (rs : list reg) (r : reg) : list reg :=
  match rs with
  | nil => nil
  | x :: xs => if r =? x then xs else split_by xs r
  end
.

Theorem eliminate_result_is_peo :
  forall (g : InterfGraph.dict) (r : reg),
    let peo := eliminate g in
    let after := split_by (InterfGraph.keys g) r
    In r peo -> after
.

Definition is_simplicial (g : InterfGraph.dict) (r : reg) : Prop :=
  let nbors := InterfGraph.get g r in
  forall (n n': reg),
    In n nbors /\ In n' nbors
.

Lemma is_simplicialb_is_simplicial :
  forall (g : InterfGraph.dict) (r : reg),
    is_simplicialb g r = true -> is_simplicial g r
.
Proof.
Admitted. *)
