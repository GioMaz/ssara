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
  2) At each step of the eliminate function the node we just eliminated has a neighbor set that is a clique, that means that we can color it in polynomial time
  3) At each step of the coloring function we insert a node where every neighbor node is already inserted;
  4) At each step of the coloring function the color we choose is not already used by the node's neighbors;
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

From Stdlib Require Import Sorting.Permutation.

(*
  Given a predicate on a list of Xs state that every pair of lists of Xs such
  that they are permutations also satisfy that predicate
*)
Definition perm_invariant {X : Type} (P : list X -> Prop) : Prop :=
  forall xs ys, Permutation xs ys -> P xs <-> P ys
.

Definition ig_perm_invariant (P : InterfGraph.dict -> Prop) : Prop :=
  forall g g',
    Permutation (InterfGraph.keys g) (InterfGraph.keys g') ->
    (forall r, Permutation (InterfGraph.get g r) (InterfGraph.get g' r)) ->
    P g <-> P g'
.

Lemma is_simplicial_perm_inveriant : forall r,
  ig_perm_invariant (fun g => is_simplicial r g)
.
Proof.
Admitted.

(*
  Prove that `is_cliqueb` is permutation invariant, that is for every two lists
  that are permutations `is_cliqueb xs = true` iff `is_cliqueb ys = true`
*)
Lemma is_cliqueb_perm_inveriant : forall g,
  perm_invariant (fun regs => is_cliqueb g regs = true)
.
Proof.
Admitted.

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

Lemma invert_keys : forall g a V',
  a :: V' = InterfGraph.keys g -> exists g',
    (ig_insert_node g' a = g \/ exists r', (In r' (InterfGraph.keys g')) /\ ig_insert_edge g' a r' = g)
    /\ InterfGraph.keys g = a :: (InterfGraph.keys g')
    /\ ~(In a (InterfGraph.keys g'))
    (* /\ (forall b, a <> b -> Permutation (InterfGraph.get g b) (InterfGraph.get g' b)) *)
.
Proof.
  intros g a V' Hkeys. destruct (InterfGraph.keys g) as [| x xs] eqn:Ekeys.
  - discriminate.
  - injection Hkeys as Eax EV'xs. subst.
Admitted.

Lemma nbors_is_cliqueb_ig_insert_node :
  forall g r a, r <> a ->
    is_cliqueb (ig_insert_node g a) (InterfGraph.get g r) = true ->
    is_cliqueb g (InterfGraph.get g r) = true
.
Proof.
Admitted.

Lemma nbors_is_cliqueb_ig_insert_edge :
  forall g r a b, r <> a -> r <> b ->
    is_cliqueb (ig_insert_edge g a b) (InterfGraph.get g r) = true ->
    is_cliqueb g (InterfGraph.get g r) = true
.
Proof.
Admitted.

(*
  TODO: add property of well formed graphs s.t. (V = {}, E = {{1,2}}) is not
  well formed
*)

(* Inductive well_formed : InterfGraph.dict -> Prop :=
  | WellFormedEmpty : well_formed InterfGraph.empty
  | WellFormedNode : forall g r, well_formed g -> well_formed (ig_insert_node g r)
  | WellFormedEdge : forall g r r', well_formed g -> well_formed (ig_insert_edge g r r')
. *)

Definition well_formed (g : InterfGraph.dict) : Prop :=
  (forall r r', ~ In r (InterfGraph.keys g) -> ~ In r (InterfGraph.get g r')) /\
  (forall r r', In r' (InterfGraph.get g r) <-> In r (InterfGraph.get g r')) /\
  (NoDup (InterfGraph.keys g)) /\
  (forall r, NoDup (InterfGraph.get g r)) /\
  (forall r, ~ In r (InterfGraph.keys g) -> InterfGraph.get g r = [])
.

Lemma ig_insert_node_singleton :
  forall g r, well_formed g -> ~(In r (InterfGraph.keys g)) -> InterfGraph.get (ig_insert_node g r) r = [].
Proof.
  intros g r [_ [_ [_ [_ WFnbors]]]]. remember (InterfGraph.keys g) as V eqn:EV. destruct V as [| a V'].
  - intros  _. cbn.
    destruct InterfGraph.key_eq_dec as [Err | NErr]; try contradiction; clear Err.
    pose proof in_nil as Hinnil. specialize (Hinnil InterfGraph.key r).
    specialize (WFnbors r Hinnil). assumption.
  - intros NInraV'. assert (EV' := EV). apply invert_keys in EV. destruct EV as [g' [_ [Hkeys Hin]]].
    assert (NInraV'' := NInraV'). cbn in NInraV'. apply Decidable.not_or in NInraV' as [NEra NInrV'].
    cbn.
    destruct InterfGraph.key_eq_dec as [Err | NErr]; try contradiction; clear Err.
    rewrite Hkeys in EV'. injection EV' as EkeysV'. specialize (WFnbors r NInraV'').
    assumption.
Qed.

Lemma ig_insert_edge_singleton :
  forall g u v, well_formed g -> ~(In v (InterfGraph.keys g)) -> InterfGraph.get (ig_insert_edge g u v) v = [u].
Proof.
  intros g. remember (InterfGraph.keys g) as V eqn:EV. destruct V as [| a V'].
  - intros u v [_ [_ [_ [_ WFnbors]]]] _.
Admitted.

Lemma ig_insert_node_permutation :
  forall g r a, ~(In a (InterfGraph.keys g)) -> r <> a ->
  Permutation (InterfGraph.get (ig_insert_node g a) r) (InterfGraph.get g r)
.
Proof.
Admitted.

Lemma ig_insert_node_double :
  forall g u, ig_insert_node (ig_insert_node g u) u = ig_insert_node g u
.
Proof.
Admitted.

Lemma ig_insert_node_in :
  forall g u, In u (InterfGraph.keys g) -> ig_insert_node g u = g
.
Proof.
  intros g u H. unfold ig_insert_node, InterfGraph.update.
  apply set_add_intro1 with (Aeq_dec := InterfGraph.key_eq_dec) (b := u) in H.
Admitted.

Lemma ig_insert_edge_node_ig_insert_edge :
  forall g u v, ig_insert_node (ig_insert_edge g u v) u = ig_insert_edge g u v
.
Proof.
  intros g u v.
Admitted.

Lemma ig_insert_edges_ig_insert_edge :
  forall g u v, u <> v -> ig_insert_edges g u [v] = ig_insert_edge g u v
.
Proof.
  intros g u v H. unfold ig_insert_edges. assert (H' := H). apply Nat.eqb_neq in H'. rewrite H'. clear H'.
  rewrite ig_insert_edge_node_ig_insert_edge. reflexivity.
Qed.

Lemma ig_insert_node_edge_ig_insert_edge :
  forall g u v, ig_insert_edge (ig_insert_node g u) u v = ig_insert_edge g u v
.
Proof.
Admitted.

Axiom ig_insert_edge_comm :
  forall g u v, ig_insert_edge g u v = ig_insert_edge g v u
.

Lemma invert_isolated : forall g r, InterfGraph.get g r = [] ->
  exists g',
    ~(In r (InterfGraph.keys g')) /\ (ig_insert_node g' r) = g
.
Proof.
Admitted.

Lemma invert_loop : forall g r, InterfGraph.get g r = [r] ->
  exists g',
    ~(In r (InterfGraph.keys g')) /\ (ig_insert_edge g' r r) = g
.
Proof.
Admitted.

(* TODO: this depends on the implementation *)
Lemma ig_insert_edge_nbors :
  forall g u v, InterfGraph.get (ig_insert_edge g u v) u = v :: (InterfGraph.get g u)
.
Proof.
Admitted.

Lemma ig_get_in :
  forall g u v, In v (InterfGraph.get g u) -> In v (InterfGraph.keys g)
.
Proof.
Admitted.

Lemma fold_left_false :
  forall {X : Type} (l : list X) (f : X -> bool), fold_left (fun b x => b && f x) l false = false
.
Proof.
  intros X l f. induction l.
  - cbn. reflexivity.
  - simpl. assumption.
Qed.

Lemma ig_get_nodup_invariant :
  forall g u, NoDup (InterfGraph.get g u)
.
Proof.
Admitted.

Lemma nodup_neq :
  forall (A : Type) (x y : A) (ys: list A),
    NoDup (x :: y :: ys) -> x <> y
.
Proof.
  intros A x y ys H. inversion H as [| x' l HNIn HNDup HExx'].
  unfold not in HNIn.
  intros Heq. subst.
  apply HNIn. left. reflexivity.
Qed.

Lemma ig_insert_edges_double :
  forall g u v, ig_insert_edges g u [v] = ig_insert_edges g u [v; v]
.
Proof.
Admitted.

Lemma ig_insert_edge_isolated_nbors :
  forall g a b c, a <> b -> a <> c -> InterfGraph.get (ig_insert_edge g b c) a = InterfGraph.get g a
.
Proof.
Admitted.

Lemma is_simplicialb_is_simplicial :
  forall g r, is_simplicialb g r = true -> is_simplicial r g
.
Proof.
  intros g. remember (InterfGraph.keys g) as V eqn:EV. revert g EV. induction V as [| a]. (* Induction on the size of the graph *)
  - intros g V. unfold is_simplicialb. rewrite <- V. discriminate.
  - intros g H r. assert (H' := H). apply invert_keys in H. destruct H as [g' [[Hsing | Hedge] [Hkeys Hin]]].
    * specialize (IHV g'). rewrite Hkeys in H'.
      injection H' as H'. specialize (IHV H' r). intros H.
      unfold is_simplicialb in H. apply andb_prop in H as [Ha Hb]. rewrite <- Hsing.
      rewrite Hkeys in Ha. cbn in Ha. destruct (reg_eq_dec r a).
      + subst. now apply SimplicialAddSingleton.
      + apply SimplicialAddNode; trivial. apply IHV. unfold is_simplicialb. apply andb_true_intro. split. apply Ha. rewrite <- Hsing in Hb.
        pose proof (is_cliqueb_perm_inveriant (ig_insert_node g' a)). unfold perm_invariant in H.

        (* `ys` is `(InterfGraph.get g' r)` since `a` is a singleton and so it cannot be part of the neighborhood of `r` *)
        specialize (H (InterfGraph.get (ig_insert_node g' a) r) (InterfGraph.get g' r)). apply H in Hb. clear H.
        eapply nbors_is_cliqueb_ig_insert_node; eauto.
        apply ig_insert_node_permutation; eauto.
    * specialize (IHV g'). rewrite Hkeys in H'. injection H' as H'. specialize (IHV H'). intros H. assert (Hsimpb := H).
      unfold is_simplicialb in H.
      apply andb_prop in H as [Ha Hb]. assert (Hedge' := Hedge). destruct Hedge' as [r' [Hinedge' Hedge']].
      rewrite <- Hedge'. rewrite Hkeys in Ha. cbn in Ha. destruct (reg_eq_dec r a) as [Era | NEra].

      (* First we take into consideration the case where a = r, we are adding a new isolated edge a = r --- r' *)
      + subst. assert (Hin' := Hin). assert (Hin'' := Hin). rewrite <- ig_insert_node_edge_ig_insert_edge.
        apply ig_insert_edge_singleton with (u := r') in Hin. rewrite <- ig_insert_edge_comm.
        rewrite <- ig_insert_edges_ig_insert_edge. apply ig_insert_node_singleton in Hin'. rewrite <- Hin'.
        eapply SimplicialAddNeighbor. now apply SimplicialAddSingleton.
        admit. admit. admit.

(*
  Then we take into consideration the case where a <> r, we are connecting the new node a to an already existing node r'
  We analyze the following cases for r':

  1) a --- (r = r') --- ?

    1.1) a --- (r = r')                         (r still simplicial)

    1.2) a --- (r = r') --- nbors (clique)

      1.2.1) a --- (r = r') --- nbors (clique)  (r not simplicial anymore)
                     \-/

      1.2.2) a --- (r = r') --- nbors (clique)  (r not simplicial anymore)

  2) a     r --- nbors (clique)                 (r still simplicial)
      \---------/

  3) a     r --- nbors (clique)     r'          (r still simplicial)
      \----------------------------/

*)

      (* + destruct (reg_eq_dec r r').
        (* 1 *)
        -- destruct (InterfGraph.get g' r) as [| x xs] eqn:nbors.

          (* 1.1 *)
          ** subst. rewrite <- ig_insert_edges_ig_insert_edge. rewrite <- nbors. apply SimplicialAddNeighbor.
            apply invert_isolated in nbors. destruct nbors as [g'' [nborsIn nborsEq]]. rewrite <- nborsEq.
            apply SimplicialAddSingleton. assumption. symmetry. assumption.

          (* 1.2 *)
          ** subst. destruct (reg_eq_dec a x) as [Eax | NEax].
            ++ rewrite <- Eax in nbors. assert (In a (InterfGraph.get g' r')). rewrite nbors. apply in_eq.
              apply ig_get_in in H. contradiction.
            ++ destruct (reg_eq_dec x r') as [Exr' | NExr'] eqn:EDxr'.
              --- rewrite ig_insert_edge_comm in Hb. rewrite ig_insert_edge_nbors in Hb. rewrite nbors in Hb. assert (Hin' := Hin).
                apply ig_insert_edge_singleton with (u := r') in Hin. cbn in Hb.

                (*
                  Now the contradiction in `Hb` should be that `a` is not connected to `xs`,
                  but if `xs = []` we cannot derive the contradiction, in that case in fact
                  we have a --- (r' = x) which is simplicial
                *)
                destruct xs as [| y ys].
                *** subst. cbn in Hb. rewrite <- ig_insert_edges_ig_insert_edge by now auto. rewrite ig_insert_edges_double. rewrite <- nbors.
                  apply SimplicialAddNeighbor. apply invert_loop in nbors. destruct nbors as [g'' [Hinr'g'' Hr'r']]. assert (Hinr'g''' := Hinr'g'').
                  rewrite <- Hr'r'. rewrite <- ig_insert_node_edge_ig_insert_edge by now assumption. rewrite <- ig_insert_edges_ig_insert_edge by now admit.
                  apply ig_insert_node_singleton in Hinr'g''. rewrite <- Hinr'g''. apply SimplicialAddNeighbor. apply SimplicialAddSingleton.
                  assumption. admit.

                *** remember (are_neighborsb (ig_insert_edge g' r' a) a (a :: x :: y :: ys)) as Contr.
                assert
                  (fold_left (fun (b : bool) (x0 : reg) => b && are_neighborsb (ig_insert_edge g' r' a) x0 (a :: x :: y :: ys)) (y :: ys)
                    (Contr && are_neighborsb (ig_insert_edge g' r' a) x (a :: x :: y :: ys)) = true) as Hb'
                by now rewrite HeqContr. clear Hb.
                unfold are_neighborsb in HeqContr. cbn in HeqContr.
                remember (((a =? y) || regs_mem y (InterfGraph.get (ig_insert_edge g' r' a) a))) as Contr'.
                pose proof in_elt as Iny. specialize (Iny reg y [x] ys). change ([x] ++ y :: ys) with (x :: y :: ys) in Iny. rewrite <- nbors in Iny. apply ig_get_in in Iny.
                assert (a <> y) as NEay. intros Eay. rewrite <- Eay in Iny. contradiction. apply Nat.eqb_neq in NEay. rewrite NEay in HeqContr'.
                cbn in HeqContr'. admit.
                (* rewrite Hin in HeqContr'. cbn in HeqContr'. rewrite <- Exr' in HeqContr'.
                pose proof (ig_get_nodup_invariant) as ND. specialize (ND g' r'). rewrite nbors in ND. apply nodup_neq in ND. apply Nat.eqb_neq in ND.
                destruct (reg_eq_dec y x) as [Eyx | NEyx]. rewrite Eyx in ND. rewrite Nat.eqb_refl in ND. discriminate.
                rewrite HeqContr' in HeqContr. rewrite andb_false_r in HeqContr. rewrite fold_left_false in HeqContr. rewrite andb_false_r in HeqContr.
                rewrite HeqContr in Hb'. rewrite andb_false_l in Hb'. rewrite fold_left_false in Hb'. discriminate. *)

              (*
                We prove by contradiction that if we add a neighbor `a` to an `r` such that `a` is not in the graph
                and `r` is simplicial and has neighbors, then `r` is no longer simplicial
              *)
              --- rewrite ig_insert_edge_comm in Hb. rewrite ig_insert_edge_nbors in Hb. rewrite nbors in Hb. assert (Hin' := Hin).
                apply ig_insert_edge_singleton with (u := r') in Hin. cbn in Hb.
                remember (are_neighborsb (ig_insert_edge g' r' a) a (a :: x :: xs)) as Contr.
                assert
                  (fold_left (fun (b : bool) (x0 : reg) => b && are_neighborsb (ig_insert_edge g' r' a) x0 (a :: x :: xs)) xs
                    (Contr && are_neighborsb (ig_insert_edge g' r' a) x (a :: x :: xs)) = true) as Hb'
                by now rewrite HeqContr. clear Hb.
                unfold are_neighborsb in HeqContr. cbn in HeqContr.
                remember ((a =? x) || regs_mem x (InterfGraph.get (ig_insert_edge g' r' a) a)) as Contr'.
                rewrite Hin in HeqContr'. apply Nat.eqb_neq in NEax. rewrite NEax in HeqContr'. cbn in HeqContr'. rewrite EDxr' in HeqContr'.
                rewrite HeqContr' in HeqContr. rewrite andb_false_r in HeqContr. rewrite fold_left_false in HeqContr. rewrite andb_false_r in HeqContr.
                rewrite HeqContr in Hb'. cbn in Hb'. rewrite fold_left_false in Hb'. discriminate.

        (* 2 - 3 *)
        -- subst. eapply SimplicialAddEdge; eauto. rewrite ig_insert_edge_isolated_nbors in Hb by now assumption.
          apply nbors_is_cliqueb_ig_insert_edge in Hb; eauto. unfold is_simplicialb in IHV. specialize (IHV r).
          rewrite Ha in IHV. rewrite Hb in IHV. cbn in IHV. specialize (IHV eq_refl). assumption. *)
Admitted.

Lemma find_next_simplicial :
  forall (g : InterfGraph.dict) (r : reg),
    find_next g = Some r -> is_simplicial r g
.
Proof.
  intros g r. unfold find_next. intros H. apply is_simplicialb_is_simplicial.
  apply find_some in H. destruct H as [H1 H2]. assumption.
Qed.

Inductive is_clique : InterfGraph.dict -> list reg -> Prop :=
  | CliqueEmpty : forall g, is_clique g []
  | CliqueAddNode : forall g r rs, is_clique g rs ->
    is_clique (ig_insert_edges g r rs) (r :: rs)
.

Lemma is_simplicial_nbors_is_clique :
  forall g r, is_simplicial r g -> is_clique g (InterfGraph.get g r)
.
Proof.
Admitted.

(* Inductive is_peo : InterfGraph.dict -> list reg -> Prop :=
  | PeoEmpty : is_peo InterfGraph.empty []
  | PeoAddEdge : forall g' r rs,
    is_peo g' rs ->
    (exists g, InterfGraph.keys g = r :: (InterfGraph.keys g') /\ is_simplicial r g)
    is_peo g (r :: rs)
.

Lemma eliminate_is_peo : *)