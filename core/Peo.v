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

Definition is_cliqueb (g : InterfGraph.dict) (regs : list reg) : bool :=
  conjunction (fun r => are_neighborsb g r regs) regs
.

(* Check whether the neighbors of r are a clique *)
Definition is_simplicialb (g : InterfGraph.dict) (r : reg) : bool :=
  let nbors := InterfGraph.get g r in
  regs_mem r (InterfGraph.keys g) &&
  is_cliqueb g nbors
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
  2) At each step of the eliminate function all of the neighbors of the eliminated node are already eliminated;
  3) At each step of the coloring function we insert a node where every neighbor
  node is already inserted;
  4) At each step of the coloring function the color we choose is not already
  used by the node's neighbors;
*)

(*
  We start by defining a lemma proving the correctness of a single iteration of
  the eliminate function, that is proving that `find_next` actually returns a
  simplicial node.
*)

(*
  Now we define a predicate for the simplicial relation, we define a node being
  simplicial if:
  - It has no neighbors
  - It is built by a simplicial node r to which we add a neighbor r' that also
    has an edge with every other neighbor of r
*)
(* Inductive is_simplicial (r : reg) : InterfGraph.dict -> Prop :=
  | SimplicialIsolated (g : InterfGraph.dict):
    InterfGraph.get g r = nil -> is_simplicial r g
  | SimplicialAddNeighbor (g : InterfGraph.dict) :
    is_simplicial r g -> forall r', let nbors := InterfGraph.get g r in
    is_simplicial r (ig_insert_edges g r' (r :: nbors))
. *)
Inductive is_simplicial (r : reg) : InterfGraph.dict -> Prop :=
  | SimplicialAddSingleton (g : InterfGraph.dict):
    ~(In r (InterfGraph.keys g)) -> is_simplicial r (ig_insert_node g r)
  | SimplicialAddNode (g : InterfGraph.dict):
    is_simplicial r g -> forall r', r <> r' ->
    is_simplicial r (ig_insert_node g r')
  | SimplicialAddEdge (g : InterfGraph.dict) :
    is_simplicial r g -> forall r' r'', r <> r' -> r <> r'' ->
    is_simplicial r (ig_insert_edge g r' r'')
  | SimplicialAddNeighbor (g : InterfGraph.dict) :
    is_simplicial r g -> forall a, let nbors := InterfGraph.get g r in
    is_simplicial r (ig_insert_edges g a (r :: nbors))
.

(* (*
  Graph:
  0
*)
Goal is_simplicial 0 (ig_insert_node InterfGraph.empty 0).
  apply SimplicialAddNode. apply SimplicialEmpty. reflexivity.
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
  apply SimplicialAddNode.
  apply SimplicialEmpty.
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
  apply SimplicialAddNode.
  apply SimplicialAddNode.
  apply SimplicialAddNode.
  apply SimplicialEmpty. reflexivity.
Qed.
*)

From Stdlib Require Import ListSet.

Lemma invert_keys : forall g a E,
  a :: E = InterfGraph.keys g ->
  exists g', (
    (ig_insert_node g' a = g) \/
    (exists r', In r' (InterfGraph.keys g') /\ ig_insert_edge g' a r' = g)
  ) /\ InterfGraph.keys g = a :: (InterfGraph.keys g') /\ ~(In a (InterfGraph.keys g'))
.
Proof.
Admitted.

From Stdlib Require Import Sorting.Permutation.

(*
  Given a predicate on a list of Xs state that every pair of lists of Xs such
  that they are permutations also satisfy that predicate
*)
Definition perm_invariant {X : Type} (P : list X -> Prop) : Prop :=
  forall xs ys, Permutation xs ys -> P xs <-> P ys
.

(*
  Prove that `is_cliqueb` is permutation invariant, that is for every two lists
  that are permutations `is_cliqueb xs = true` iff `is_cliqueb ys = true`
*)
Lemma is_cliqueb_perm_inveriant : forall g,
  perm_invariant (fun regs => is_cliqueb g regs = true)
.
Proof.
Admitted.

Lemma ig_insert_node_singleton :
  forall g r, ~(In r (InterfGraph.keys g)) -> InterfGraph.get (ig_insert_node g r) r = [].
Proof.
Admitted.

Lemma ig_insert_edge_singleton :
  forall g u v, ~(In v (InterfGraph.keys g)) -> InterfGraph.get (ig_insert_edge g u v) v = [u].
Proof.
Admitted.

Lemma ig_insert_node_regs_mem :
  forall g r, regs_mem r (InterfGraph.keys (ig_insert_node g r)) = true
.
Proof.
Admitted.

Lemma ig_insert_node_is_cliqueb :
  forall g r a, ~(In a (InterfGraph.keys g)) -> r <> a ->
  is_cliqueb (ig_insert_node g a) (InterfGraph.get g r) = true ->
  is_cliqueb g (InterfGraph.get g r) = true
.
Proof.
Admitted.

Lemma ig_insert_node_permutation :
  forall g r a, ~(In a (InterfGraph.keys g)) -> r <> a ->
  Permutation (InterfGraph.get (ig_insert_node g a) r) (InterfGraph.get g r)
.
Proof.
Admitted.

Lemma ig_insert_edge_ig_insert_edges :
  forall g u v, ig_insert_edges g u [v] = ig_insert_edge g v u
.
Proof.
Admitted.

Lemma ig_insert_node_edge_ig_insert_edge :
  forall g u v, ~(In u (InterfGraph.keys g)) -> ig_insert_edge (ig_insert_node g u) u v = ig_insert_edge g u v
.
Proof.
Admitted.

Goal is_simplicial 0 (ig_insert_edge InterfGraph.empty 0 1).
Proof.
  rewrite <- ig_insert_node_edge_ig_insert_edge. rewrite <- ig_insert_edge_ig_insert_edges. apply SimplicialAddNeighbor.
  apply SimplicialAddSingleton. cbn. tauto. cbn. tauto.
Qed.

Lemma is_simplicialb_is_simplicial :
  forall g r, is_simplicialb g r = true -> is_simplicial r g
.
Proof.
  intros g. remember (InterfGraph.keys g) as E.  (* Induction on the size of the graph *)
  revert g HeqE. induction E.
  - intros g E. unfold is_simplicialb. rewrite <- E. discriminate.
  - intros g H r. assert (H' := H). apply invert_keys in H. destruct H as [g' [[Hsing | [r' [Hin Hedge]]] [H2 H3]]].
    + specialize (IHE g'). rewrite H2 in H'.
      inversion H'. specialize (IHE H0 r). intros H.
      unfold is_simplicialb in H. apply andb_prop in H as [Ha Hb]. rewrite <- Hsing.
      rewrite H2 in Ha. cbn in Ha. destruct (reg_eq_dec r a) eqn:X.
      * subst. now apply SimplicialAddSingleton.
      * apply SimplicialAddNode; trivial. apply IHE. unfold is_simplicialb. apply andb_true_intro. split. apply Ha. rewrite <- Hsing in Hb.
        pose proof (is_cliqueb_perm_inveriant (ig_insert_node g' a)). unfold perm_invariant in H.

        (* ys is (InterfGraph.get g' r) since a is a singleton so it cannot be part of the neighborhood of r *)
        specialize (H (InterfGraph.get (ig_insert_node g' a) r) (InterfGraph.get g' r)). apply H in Hb. clear H.
        eapply ig_insert_node_is_cliqueb; eauto.
        apply ig_insert_node_permutation; eauto.
    + specialize (IHE g'). rewrite H2 in H'. inversion H'. specialize (IHE H0). intros H.
      unfold is_simplicialb in H. apply andb_prop in H as [Ha Hb]. rewrite <- Hedge.
      rewrite H2 in Ha. cbn in Ha. destruct (reg_eq_dec r a) eqn:X.
      * subst. assert (H3' := H3). assert (H3'' := H3). rewrite <- ig_insert_node_edge_ig_insert_edge.
        apply ig_insert_edge_singleton with (u := r') in H3. rewrite <- ig_insert_edge_ig_insert_edges.
        apply ig_insert_node_singleton in H3'. rewrite <- H3'. eapply SimplicialAddNeighbor.
        apply SimplicialAddSingleton. assumption. assumption.
      *
Admitted.

Lemma find_next_simplicial :
  forall (g : InterfGraph.dict) (r : reg),
    find_next g = Some r -> is_simplicial r g
.
Proof.
  intros g r. unfold find_next. intros H. apply is_simplicialb_is_simplicial.
  apply find_some in H. destruct H as [H1 H2]. assumption.
Qed.

(* Lemma is_simplicial_peo_correct :
  forall (g : InterfGraph.dict),  *)

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
