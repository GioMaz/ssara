From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Dict.
From Ssara.Core Require Import Utils.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
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

Fixpoint eliminate_fuel (g : InterfGraph.dict) (fuel : nat) : list reg :=
  match fuel with
  | O => nil
  | S fuel' =>
    match find_next g with
    | Some next =>
      let g := ig_remove_node g next in
      let peo := eliminate_fuel g fuel' in
      next :: peo
    | None => nil
    end
  end
.

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
  function is actually a PEO. To prove that we should follow the following
  steps:
  1) At each step of the eliminate function we eliminate a simplicial node;
  2) Each element of the PEO has all of its neighbors to the left of it;
  3) At each step of the coloring function we insert a node where every neighbor
  node is already inserted;
  4) At each step of the coloring function the color we choose is not already
  used by the node's neighbors;
*)

Fixpoint split_by (r : reg) (rs : list reg) : list reg :=
  match rs with
  | nil => nil
  | x :: xs => if r =? x then xs else split_by r xs
  end
.

(* 3 *)
(* Lemma peo_neighbors :
  forall (g : InterfGraph.dict) (r : reg),
  let peo := eliminate g in regs_inter (split_by r peo)
. *)

(*
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

(*
  Now we define a predicate for the simplicial relation, we define a node being
  simplicial if:
  - It has no neighbors
  - It is built by a simplicial node r to which we add a neighbor r' that also
    has an edge with every other neighbor of r
*)
Inductive is_simplicial (r : reg) : InterfGraph.dict -> Prop :=
  | SimplicialIsolated (g : InterfGraph.dict):
    InterfGraph.get g r = nil -> is_simplicial r g
  | SimplicialAddNeighbor (g : InterfGraph.dict) :
    is_simplicial r g -> forall r', let nbors := InterfGraph.get g r in
    is_simplicial r (ig_insert_edges g r' (r :: nbors))
.

(*
  Graph:
  0
*)
Goal is_simplicial 10 (ig_insert_node InterfGraph.empty 10).
  apply SimplicialIsolated. simpl. reflexivity.
Qed.

(*
  Graph:
     0
   / | \
  1--2--3
   \---/
*)

Definition example_ig_1 : InterfGraph.dict :=
  (ig_insert_edges
    (ig_insert_edges
      (ig_insert_edges
        (ig_insert_edges InterfGraph.empty 0 []) 1 [0]) 2 [0; 1]) 3 [0; 1; 2])
.

Goal is_simplicial 0 example_ig_1.
  unfold example_ig_1.
  apply SimplicialAddNeighbor.
  apply SimplicialAddNeighbor.
  apply SimplicialAddNeighbor.
  apply SimplicialIsolated.
  simpl. reflexivity.
Qed.

(*
  Graph:
  0 1 2
*)
Definition example_ig_2 : InterfGraph.dict :=
  (ig_insert_node (ig_insert_node (ig_insert_node InterfGraph.empty 2) 1) 0)
.
Goal is_simplicial 2 example_ig_2.
  unfold example_ig_2.
  apply SimplicialIsolated. simpl. reflexivity.
Qed.

From Stdlib Require Import ListSet.

(* Lemma is_simplicialb_is_simplicial :
  forall g r, is_simplicialb g r = true -> is_simplicial r g
.
Proof.
  intros g r. unfold is_simplicialb. induction (InterfGraph.get g r) eqn:E.
  - intros H. apply andb_prop in H. destruct H as [H _]. unfold regs_mem in H.
    apply set_mem_correct1 in H.
  -  *)

Definition a := 2.

(* Definition is_simplicial (g : InterfGraph.dict) (r : reg) : Prop :=
  let nbors := InterfGraph.get g r in
  forall (n n': reg),
    In n (InterfGraph.keys g) /\ In n' (InterfGraph.keys g) ->
    In n (InterfGraph.get g n') /\ In n' (InterfGraph.get g n)
. *)

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