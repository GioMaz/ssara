From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Dict.
From Ssara.Core Require Import Utils.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ListSet.
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
  forall (g : InterfGraph.dict) (n : reg),
    find_next g = Some n -> In n (InterfGraph.keys g)
.
Proof.
  intros g n. unfold find_next. apply find_some.
Qed.

From Stdlib Require Import FunInd.
From Stdlib Require Import Recdef.

Definition eliminate_step (g : InterfGraph.dict) : option (reg * InterfGraph.dict):=
  match find_next g with
  | Some next =>
    Some (next, ig_remove_node g next)
  | None => None
  end
.

(*
  Precondition: g is chordal
  Postcondition:
  Correctness: after this function:
  - reg is simplicial for g
  - InterfGraph.dict is chordal
  Or
  InterfGraph.dict is empty
*)

Function eliminate (g : InterfGraph.dict) {measure InterfGraph.size g} : list reg :=
  match eliminate_step g with
  | Some (next, g') => next :: (eliminate g')
  | None => nil
  end
.
Proof.
  intros g result next g' Hp Helim.
  unfold eliminate_step in Helim.
  destruct find_next eqn:E.
  - inversion Helim. subst.
    apply ig_size_decrease. apply find_next_in in E. assumption.
  - discriminate.
Qed.

Fixpoint eliminate_fuel (g : InterfGraph.dict) (fuel : nat) : list reg :=
  match fuel with
  | O => nil
  | S fuel' =>
    match eliminate_step g with
    | Some (next, g') => next :: (eliminate_fuel g' fuel')
    | None => nil
    end
  end
.

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

Lemma set_add_elim {A : Type} :
  forall Aeq_dec (a b : A) l,
    ~ In b (set_add Aeq_dec a l) -> ~ set_In b l /\ a <> b
.
Proof.
  intros Aeq_dec a b l Hnotin.
  induction l as [| x xs IH].
  - split.
    intros HIn. cbn in HIn. contradiction.
    intros HEab. cbn in Hnotin. tauto.
  - split.
    * cbn in *. intros HIn.
      destruct HIn as [Hb_eq | Hb_in_tail].
      + destruct (Aeq_dec a x).
        cbn in Hnotin. apply Hnotin. left. assumption.
        cbn in Hnotin. apply Hnotin. left. assumption.
      + destruct (Aeq_dec a x).
        cbn in Hnotin. apply Hnotin. right. exact Hb_in_tail.
        cbn in Hnotin. apply Decidable.not_or in Hnotin as [Hnotin1 Hnotin2].
        specialize (IH Hnotin2) as [IH1 IH2]. contradiction.
    * cbn in *. destruct (Aeq_dec a x) as [Eax | NEax].
      + cbn in Hnotin. apply Decidable.not_or in Hnotin.
        rewrite <- Eax in Hnotin. tauto.
      + cbn in Hnotin. apply Decidable.not_or in Hnotin as [Hnotin1 Hnotin2].
        specialize (IH Hnotin2) as [_ H]. assumption.
Qed.

Definition well_formed (g : InterfGraph.dict) : Prop :=
  (forall r r', ~ In r (InterfGraph.keys g) -> ~ In r (InterfGraph.get g r')) /\
  (forall r r', In r' (InterfGraph.get g r) -> In r (InterfGraph.get g r')) /\
  (NoDup (InterfGraph.keys g)) /\
  (forall r, NoDup (InterfGraph.get g r)) /\
  (forall r, ~ In r (InterfGraph.keys g) -> InterfGraph.get g r = []) /\
  (forall r, ~ In r (InterfGraph.get g r))
.

Lemma empty_wf :
  well_formed InterfGraph.empty
.
Proof.
  unfold well_formed. repeat (split; auto).
  - cbn. apply NoDup_nil.
  - intros r. cbn.
    unfold InterfGraph.default, InterfGraphParams.default.
    apply NoDup_nil.
Qed.

Lemma ig_insert_node_not_in :
  forall g u v, well_formed g ->
    ~ In v (InterfGraph.keys (ig_insert_node g u)) ->
    ~ In v (InterfGraph.keys g) /\ u <> v
.
Proof.
  intros g u v WF H.
  unfold InterfGraph.keys, ig_insert_node, InterfGraph.update in H.
  cbn in H. apply set_add_elim in H. assumption.
Qed.

Lemma ig_insert_node_get :
  forall g u v,
    InterfGraph.get g u = InterfGraph.get (ig_insert_node g v) u
.
Proof.
  intros g u v. cbn.
  destruct (InterfGraph.key_eq_dec) as [Euv | NEuv]. rewrite Euv. reflexivity.
  reflexivity.
Qed.

Lemma ig_insert_node_in :
  forall g u, In u (InterfGraph.keys (ig_insert_node g u))
.
Proof.
  intros g u. cbn. apply set_add_intro2. reflexivity.
Qed.

Lemma ig_insert_node_wf :
  forall g u, well_formed g -> well_formed (ig_insert_node g u)
.
Proof.
  intros g u WFg. unfold well_formed. repeat split.
  - intros r r' H.
    destruct (WFg) as [WFg1 [_ [_ [_ WFg2]]]].
    pose proof ig_insert_node_not_in as H1.
    specialize (H1 g u r WFg H) as [H1 H2].
    specialize (WFg1 r r' H1).
    cbn. destruct (InterfGraph.key_eq_dec u r') as [Eur' | NEur'].
    * rewrite Eur'. assumption.
    * assumption.
  - intros r r' H.
    destruct (WFg) as [_ [WFg1 _]].
    specialize (WFg1 r r').
    rewrite <- ig_insert_node_get in H.
    rewrite <- ig_insert_node_get.
    apply WFg1. assumption.
  - destruct (WFg) as [_ [_ [WFg1 _]]].
    cbn. apply set_add_nodup. assumption.
  - intros r.
    destruct (WFg) as [_ [_ [_ [WFg1 _]]]].
    specialize (WFg1 r).
    rewrite <- ig_insert_node_get.
    assumption.
  - intros r H.
    destruct (WFg) as [_ [_ [_ [_ [WFg1 _]]]]].
    specialize (WFg1 r).
    cbn. destruct InterfGraph.key_eq_dec as [Eur | NEur].
    subst. pose proof (ig_insert_node_in g r) as Contr. contradiction.
    cbn in H. apply ig_insert_node_not_in in H as [H _]; try assumption.
    specialize (WFg1 H). assumption.
  - intros r.
    destruct (WFg) as [_ [_ [_ [_ [_ WFg1]]]]].
    specialize (WFg1 r).
    cbn. destruct InterfGraph.key_eq_dec as [Eur | NEur].
    rewrite Eur. assumption.
    assumption.
Qed.

Lemma ig_remove_node_wf :
  forall g u, well_formed g -> well_formed (ig_remove_node g u)
.
Proof.
Admitted.

Lemma ig_insert_edge_ig_insert_node :
  forall g u,
    ig_insert_edge g u u = g
.
Proof.
  intros g u.
  unfold ig_insert_edge, ig_update_edge.
  destruct (reg_eq_dec u u).
  reflexivity.
  contradiction.
Qed.

Lemma ig_insert_edge_wf :
  forall g u v, well_formed g -> well_formed (ig_insert_edge g u v)
.
Proof.
  intros g u v WF. unfold well_formed. repeat split.
  - intros r r' H.
    destruct WF as [WF _].
    specialize (WF r r').
    destruct (reg_eq_dec u v) as [Euv | NEuv].
    * subst.
      rewrite ig_insert_edge_ig_insert_node in H.
      rewrite ig_insert_edge_ig_insert_node.
      specialize (WF H).
      assumption.
    * unfold ig_insert_edge, ig_update_edge in H.
      destruct (reg_eq_dec u v) as [Contr | _]. contradiction.
      cbn in H.
      apply set_add_elim in H as [H NEvr].
      apply set_add_elim in H as [H NEur].
      specialize (WF H).
      unfold ig_insert_edge, ig_update_edge.
      destruct (reg_eq_dec u v) as [Contr | _]. contradiction.
      cbn.
      unfold InterfGraph.key_eq_dec, InterfGraphParams.key_eq_dec.
      destruct (reg_eq_dec v r') as [Evr' | NEvr'].
      + destruct (reg_eq_dec u v) as [Contr | _]. contradiction.
        subst.
        intros Hin.
        apply set_add_elim2 in Hin.
        contradiction.
        symmetry; assumption.
      + destruct (reg_eq_dec u r') as [Eur' | NEur'].
        subst.
        intros Hin.
        apply set_add_elim2 in Hin.
        contradiction.
        symmetry; assumption.
        assumption.
  - intros r r' H.
Admitted.

Lemma ig_insert_edges_wf :
  forall g u vs, well_formed g -> well_formed (ig_insert_edges g u vs)
.
Proof.
Admitted.

Inductive is_simplicial (r : reg) : InterfGraph.dict -> Prop :=
  | SimplicialAddSingleton (g : InterfGraph.dict):
    well_formed g ->
    ~ In r (InterfGraph.keys g) ->
    is_simplicial r (ig_insert_node g r)
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

Lemma is_simplicial_wf :
  forall g r,
    is_simplicial r g -> well_formed g
.
Proof.
  intros g r H.
  induction H.
  apply ig_insert_node_wf; assumption.
  apply ig_insert_node_wf; assumption.
  apply ig_insert_edge_wf; assumption.
  apply ig_insert_edges_wf; assumption.
Qed.

Lemma is_simplicial_nbors :
  forall g u v w,
    is_simplicial u g ->
    In v (InterfGraph.get g u) ->
    In w (InterfGraph.get g v) ->
    In u (InterfGraph.get g w)
.
Proof.
Admitted.

From Stdlib Require Import Sorting.Permutation.

Definition ig_eq (g : InterfGraph.dict) (g' : InterfGraph.dict) : Prop :=
  Permutation (InterfGraph.keys g) (InterfGraph.keys g') /\
  forall r, Permutation (InterfGraph.get g r) (InterfGraph.get g' r)
.

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

Lemma invert_keys : forall g a V',
  a :: V' = InterfGraph.keys g -> exists g',
    (ig_insert_node g' a = g \/ exists r', (In r' (InterfGraph.keys g')) /\ ig_insert_edge g' a r' = g)
    /\ InterfGraph.keys g = a :: (InterfGraph.keys g')
    /\ ~ In a (InterfGraph.keys g')
    /\ ig_remove_node g a = g'
    (* /\ (forall b, a <> b -> Permutation (InterfGraph.get g b) (InterfGraph.get g' b)) *)
.
Proof.
Admitted.

Lemma ig_insert_node_singleton :
  forall g r,
    well_formed g ->
    ~ In r (InterfGraph.keys g) ->
    InterfGraph.get (ig_insert_node g r) r = [].
Proof.
  intros g r [_ [_ [_ [_ [WFnbors _]]]]].
  remember (InterfGraph.keys g) as V eqn:EV. destruct V as [| a V'].
  - intros  _. cbn.
    destruct InterfGraph.key_eq_dec as [Err | NErr]; try contradiction;
    clear Err.
    pose proof in_nil as Hinnil.
    specialize (Hinnil InterfGraph.key r).
    specialize (WFnbors r Hinnil). assumption.
  - intros NInraV'. assert (EV' := EV). apply invert_keys in EV.
    destruct EV as [g' [_ [Hkeys Hin]]].
    assert (NInraV'' := NInraV'). cbn in NInraV'.
    apply Decidable.not_or in NInraV' as [NEra NInrV']. cbn.
    destruct InterfGraph.key_eq_dec as [Err | NErr]; try contradiction;
    clear Err.
    rewrite Hkeys in EV'. injection EV' as EkeysV'.
    specialize (WFnbors r NInraV'').
    assumption.
Qed.

Lemma ig_insert_edge_not_in :
  forall g u v,
    well_formed g ->
    ~ In v (InterfGraph.keys g) ->
    InterfGraph.get (ig_insert_edge g u v) v = [u].
Proof.
  intros g. remember (InterfGraph.keys g) as V eqn:EV. destruct V as [| a V'].
  - intros u v [_ [_ [_ [_ WFnbors]]]] _.
Admitted.

Lemma ig_insert_node_permutation :
  forall g r a, ~ In a (InterfGraph.keys g) -> r <> a ->
  Permutation (InterfGraph.get (ig_insert_node g a) r) (InterfGraph.get g r)
.
Proof.
Admitted.

Lemma ig_insert_node_intro :
  forall g u v,
    In u (InterfGraph.keys g) ->
    In u (InterfGraph.keys (ig_insert_node g v))
.
Proof.
  intros g u v H.
  cbn. apply set_add_intro1. assumption.
Qed.

Lemma map_unchanged :
  forall {A B : Type} (f : A -> B) (a a' : A)
    (Aeq_dec : forall x y : A, {x = y} + {x <> y}),
    (fun x => if Aeq_dec a x then f a else f x) a' = f a'
.
Proof.
  intros A B f a a' Aeq_dec.
  cbn. destruct (Aeq_dec a a') as [Eaa' | NEaa'].
  - rewrite Eaa'. reflexivity.
  - reflexivity.
Qed.

From Stdlib Require Import Logic.FunctionalExtensionality.

Lemma map_unchanged_eq :
  forall {A B : Type} (f : A -> B) (a : A)
    (Aeq_dec : forall x y : A, {x = y} + {x <> y}),
    (fun x => if Aeq_dec a x then f a else f x) = f
.
Proof.
  intros A B f a Aeq_dec.
  apply functional_extensionality.
  intros x.
  apply map_unchanged.
Qed.

Lemma set_add_already_in :
  forall {A : Type} (u : A) (s : set A)
    (Aeq_dec : forall x y : A, {x = y} + {x <> y}),
      In u s -> set_add Aeq_dec u s = s
.
Proof.
  intros A u s Aeq_dec H.
  induction s.
  - contradiction.
  - destruct (Aeq_dec u a) as [Eua | NEua].
    * cbn. rewrite Eua. destruct Aeq_dec. reflexivity. contradiction.
    * apply in_inv in H as [H1 | H2]. symmetry in H1. contradiction.
      specialize (IHs H2).
      cbn. destruct Aeq_dec. contradiction. f_equal. assumption.
Qed.

Lemma application_remove:
  forall {A B : Type} (f : A -> B),
    (fun x => f x) = f
.
Proof.
  intros A B f. apply functional_extensionality.
  intros x. reflexivity.
Qed.

Lemma ig_insert_node_already_in :
  forall g u,
    In u (InterfGraph.keys g) ->
    ig_insert_node g u = g
.
Proof.
  intros g u H. assert (H' := H).
  apply ig_insert_node_intro with (v := u) in H'.
  unfold ig_insert_node, InterfGraph.update.
  rewrite map_unchanged_eq.
  apply set_add_already_in with (Aeq_dec := InterfGraph.key_eq_dec) in H.
  rewrite H.
  unfold InterfGraph.keys, InterfGraph.get.
  rewrite application_remove with (f := snd g).
  rewrite surjective_pairing. reflexivity.
Qed.

Lemma ig_insert_edge_already_in :
  forall g u v,
    In u (InterfGraph.get g v) ->
    In v (InterfGraph.get g u) ->
    ig_insert_edge g u v = g
.
Proof.
Admitted.

Lemma set_add_in :
  forall {A : Type} Aeq_dec (a : A) (s : set A),
    In a (set_add Aeq_dec a s)
.
Proof.
  intros A a s Aeq_dec. apply set_add_intro2. reflexivity.
Qed.

Lemma ig_insert_edge_in :
  forall g u v,
    u <> v -> In u (InterfGraph.keys (ig_insert_edge g u v))
.
Proof.
  intros g u v H. cbn.
  remember (set_add InterfGraph.key_eq_dec u (InterfGraph.keys g)) as g' eqn:Eg'.
  pose proof (set_add_in InterfGraph.key_eq_dec u (InterfGraph.keys g)) as H'.
  unfold InterfGraph.keys, ig_insert_edge, ig_update_edge.
  destruct (reg_eq_dec u v). contradiction.
  apply set_add_intro1. assumption.
Qed.

Lemma ig_insert_edge_node_ig_insert_edge :
  forall g u v, u <> v -> ig_insert_node (ig_insert_edge g u v) u = ig_insert_edge g u v
.
Proof.
  intros g u v H.
  apply ig_insert_node_already_in.
  apply ig_insert_edge_in.
  assumption.
Qed.

Lemma ig_insert_edges_ig_insert_edge :
  forall g u v, u <> v -> ig_insert_edges g u [v] = ig_insert_edge g u v
.
Proof.
  intros g u v H.
  unfold ig_insert_edges.
  apply ig_insert_edge_node_ig_insert_edge.
  assumption.
Qed.

Lemma ig_insert_node_edge_ig_insert_edge :
  forall g u v,
    ig_insert_edge (ig_insert_node g u) u v = ig_insert_edge g u v
.
Proof.
  intros g u v.
Admitted.

Axiom ig_insert_edge_comm :
  forall g u v, ig_insert_edge g u v = ig_insert_edge g v u
.

Lemma ig_remove_node_not_in :
  forall g u,
    well_formed g -> ~ In u (InterfGraph.keys (ig_remove_node g u))
.
Proof.
  intros g u WF.
  destruct WF as [_ [_ [WF _]]]. unfold not. intros H.
  apply set_remove_2 with (Aeq_dec := reg_eq_dec) (a := u) (b := u) in WF.
  contradiction. assumption.
Qed.

Lemma ig_remove_node_ig_insert_node_not_in :
  forall g u,
    InterfGraph.get g u = [] ->
    ig_insert_node (ig_remove_node g u) u = g
.
Proof.
Admitted.

Lemma invert_isolated :
  forall g r,
    well_formed g ->
    InterfGraph.get g r = [] ->
    exists g', ~ In r (InterfGraph.keys g') /\ (ig_insert_node g' r) = g
.
Proof.
  intros g r WF H.
  remember (ig_remove_node g r) as g'.
  exists g'. split.
  rewrite Heqg'. apply ig_remove_node_not_in. assumption.
  rewrite Heqg'. rewrite ig_remove_node_ig_insert_node_not_in.
  reflexivity.
  assumption.
Qed.

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
  forall {A : Type} (x y : A) (ys: list A),
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

Lemma ig_not_in_nbors :
  forall g u, ~ In u (InterfGraph.keys g) -> InterfGraph.get g u = []
.
Proof.
Admitted.

Lemma in_not_in_neq :
  forall {A : Type} (l : list A) (a b : A), In a l -> ~ In b l -> a <> b
.
Proof.
  intros A l a b H1 H2 Heq.
  rewrite <- Heq in H2.
  contradiction.
Qed.

Lemma is_simplicialb_is_simplicial :
  forall g r,
    well_formed g ->
    is_simplicialb g r = true ->
    is_simplicial r g
.
Proof.
  intros g.
  remember (InterfGraph.keys g) as V eqn:EV. revert g EV.
  induction V as [| a]. (* Induction on the size of the graph *)
  - intros g V. unfold is_simplicialb. rewrite <- V. discriminate.
  - intros g H r WF.
    assert (H' := H).
    apply invert_keys in H. destruct H as [g' [[Hsing | Hedge] [Hkeys [Hin Hrem]]]].
    * specialize (IHV g'). rewrite Hkeys in H'.
      injection H' as H'. specialize (IHV H' r).
      intros H.
      unfold is_simplicialb in H. apply andb_prop in H as [Ha Hb].
      rewrite <- Hsing.
      rewrite Hkeys in Ha. cbn in Ha. destruct (reg_eq_dec r a).
      + subst. apply SimplicialAddSingleton; try assumption.
        admit.
      + apply SimplicialAddNode; try assumption.
        apply IHV.
        rewrite <- Hrem. now apply ig_remove_node_wf.
        unfold is_simplicialb. apply andb_true_intro. split.
        apply Ha.
        rewrite <- Hsing in Hb.
        pose proof (is_cliqueb_perm_inveriant (ig_insert_node g' a)).
        unfold perm_invariant in H.

        (*
          `ys` is `(InterfGraph.get g' r)` since `a` is a singleton so it
          cannot be part of the neighborhood of `r`
        *)
        specialize (H (InterfGraph.get (ig_insert_node g' a) r) (InterfGraph.get g' r)).
        apply H in Hb. clear H.
        eapply nbors_is_cliqueb_ig_insert_node; eauto.
        apply ig_insert_node_permutation; eauto.

    * specialize (IHV g'). rewrite Hkeys in H'.
      injection H' as H'. specialize (IHV H').
      intros H.
      assert (Hsimpb := H).
      unfold is_simplicialb in H. apply andb_prop in H as [Ha Hb].
      assert (Hedge' := Hedge). destruct Hedge' as [r' [Hinedge' Hedge']].
      rewrite <- Hedge'.
      rewrite Hkeys in Ha. cbn in Ha.
      destruct (reg_eq_dec r a) as [Era | NEra].

      (*
        We take into consideration the case where a = r,
        we are adding a new isolated edge a = r --- r'
      *)
      + subst.
        assert (Hin' := Hin). assert (Hin'' := Hin).
        rewrite <- ig_insert_node_edge_ig_insert_edge.
        apply ig_insert_edge_not_in with (u := r') in Hin;
        try now apply ig_remove_node_wf.
        rewrite <- ig_insert_edge_comm.
        rewrite <- ig_insert_edges_ig_insert_edge.
        apply ig_insert_node_singleton in Hin';
        try now apply ig_remove_node_wf.
        rewrite <- Hin'.
        eapply SimplicialAddNeighbor.
        apply SimplicialAddSingleton; try assumption.
        admit.
        now apply in_not_in_neq with (b := a) in Hinedge'.

      (*
        Now we take into consideration the case where a <> r,
        we are connecting the new node a to an already existing node r'.
      *)
      + destruct (reg_eq_dec r r') as [Err' | NErr'].
        (*
          Case 1:
          a --- (r = r') --- nbors (clique)
        *)
        -- destruct (InterfGraph.get g' r) as [| x xs] eqn:nbors.
          (*
            Case 1.1: (r still simplicial)
            a --- (r = r')
          *)
          ** subst. remember (ig_remove_node g a) as g'.
            rewrite <- ig_insert_edges_ig_insert_edge; try (symmetry; assumption).
            rewrite <- nbors.
            apply SimplicialAddNeighbor.
            apply invert_isolated in nbors.
            destruct nbors as [g'' [nborsIn nborsEq]].
            rewrite <- nborsEq. apply SimplicialAddSingleton; try assumption.
            admit.
            rewrite Heqg'. apply ig_remove_node_wf. assumption.

          (*
            Case 1.2: (r is not simplicial anymore)
            a --- (r = r') --- nbors (clique)
          *)
          ** subst r'.
            destruct (reg_eq_dec a x) as [Eax | NEax].
            rewrite <- Eax in nbors.
            assert (In a (InterfGraph.get g' r)).
            rewrite nbors. apply in_eq.
            apply ig_get_in in H. contradiction.
            destruct (reg_eq_dec x r) as [Exr' | NExr'].

            (*
              Case 1.2.1: (r is not simplicial anymore)
              a --- (r = r') --- nbors (clique)
                     \-/
            *)
            ++ rewrite <- Hedge' in Hb.
              rewrite ig_insert_edge_comm in Hb.
              rewrite ig_insert_edge_nbors in Hb.
              rewrite nbors in Hb. assert (Hin' := Hin).
              apply ig_insert_edge_not_in with (u := r) in Hin;
              try now apply ig_remove_node_wf.
              cbn in Hb.
              destruct xs as [| y ys].

              (*
                Now the contradiction in `Hb` should be that `a` is not connected to `xs`,
                but if `xs = []` we cannot derive the contradiction, in that case in fact
                we have a --- (r' = x) which is simplicial, but the problem this time is
                the fact that since `x = r = r'` there is a self-loop, which is not allowed
                by well-formedness, we can then still derive a contradiction
              *)
              --- subst.
                assert (well_formed (ig_remove_node g a)) as HWF.
                apply ig_remove_node_wf. assumption.
                destruct HWF as [_ [_ [_ [_ [_ HWF]]]]].
                specialize (HWF r).
                rewrite nbors in HWF.
                cbn in HWF.
                apply Decidable.not_or in HWF.
                destruct HWF as [HWF _].
                contradiction.

              (*
                We prove by contradiction that if we add a neighbor `a` to an `r`
                such that `a` is not in the graph and `r` is simplicial and has neighbors,
                then `r` is no longer simplicial
              *)
              --- remember (are_neighborsb (ig_insert_edge g' r a) a (a :: x :: y :: ys)) as Contr.
                assert
                  (fold_left (fun (b : bool) (x0 : reg) => b && are_neighborsb (ig_insert_edge g' r a) x0 (a :: x :: y :: ys)) (y :: ys)
                    (Contr && are_neighborsb (ig_insert_edge g' r a) x (a :: x :: y :: ys)) = true) as Hb'
                by now rewrite HeqContr. clear Hb.
                unfold are_neighborsb in HeqContr. cbn in HeqContr.
                remember (((a =? y) || regs_mem y (InterfGraph.get (ig_insert_edge g' r a) a))) as Contr'.
                pose proof in_elt as Iny.
                specialize (Iny reg y [r] ys).
                change ([r] ++ y :: ys) with (r :: y :: ys) in Iny.
                assert (In y (InterfGraph.get g' r)).
                rewrite nbors. rewrite Exr'. assumption.
                apply ig_get_in in H.
                assert (a <> y) as NEay.
                intros Eay. rewrite <- Eay in H. contradiction.
                apply Nat.eqb_neq in NEay.
                rewrite NEay in HeqContr'.
                rewrite orb_false_l in HeqContr'.
                apply ig_insert_edge_not_in with (u := r) in Hin'.
                rewrite Hin' in HeqContr'.
                cbn in HeqContr'.
                destruct (reg_eq_dec y r). subst x y.
                apply ig_remove_node_wf with (u := a) in WF.
                rewrite Hrem in WF. destruct WF as [_ [_ [_ [WF _]]]].
                specialize (WF r). rewrite nbors in WF. apply nodup_neq in WF.
                contradiction.
                rewrite HeqContr' in HeqContr.
                rewrite andb_false_r in HeqContr.
                rewrite fold_left_false in HeqContr.
                rewrite andb_false_r in HeqContr.
                rewrite HeqContr in Hb'.
                rewrite andb_false_l in Hb'.
                rewrite fold_left_false in Hb'. discriminate.
                rewrite <- Hrem. apply ig_remove_node_wf. assumption.

              --- rewrite <- Hrem.
                apply ig_remove_node_wf.
                assumption.

          (*
            Case 1.2.2: (r not simplicial anymore)
            a --- (r = r') --- nbors (clique)
          *)
          (*
            We prove by contradiction that if we add a neighbor `a` to an `r`
            such that `a` is not in the graph and `r` is simplicial and has neighbors,
            then `r` is no longer simplicial
          *)
          ++ rewrite <- Hedge' in Hb.
            rewrite ig_insert_edge_comm in Hb.
            rewrite ig_insert_edge_nbors in Hb.
            rewrite nbors in Hb. assert (Hin' := Hin).
            apply ig_insert_edge_not_in with (u := r) in Hin;
            try (rewrite <- Hrem; apply ig_remove_node_wf; assumption).
            cbn in Hb.
            remember (are_neighborsb (ig_insert_edge g' r a) a (a :: x :: xs)) as Contr.
            assert
              (fold_left (fun (b : bool) (x0 : reg) => b && are_neighborsb (ig_insert_edge g' r a) x0 (a :: x :: xs)) xs
                (Contr && are_neighborsb (ig_insert_edge g' r a) x (a :: x :: xs)) = true) as Hb'
            by now rewrite HeqContr. clear Hb.
            unfold are_neighborsb in HeqContr. cbn in HeqContr.
            remember ((a =? x) || regs_mem x (InterfGraph.get (ig_insert_edge g' r a) a)) as Contr'.
            apply Nat.eqb_neq in NEax.
            rewrite NEax in HeqContr'.
            rewrite orb_false_l in HeqContr'.
            apply ig_insert_edge_not_in with (u := r) in Hin';
            try (rewrite <- Hrem; apply ig_remove_node_wf; assumption).
            rewrite Hin' in HeqContr'.
            cbn in HeqContr'.
            destruct (reg_eq_dec x r). subst x. contradiction.
            rewrite HeqContr' in HeqContr.
            rewrite andb_false_r in HeqContr.
            rewrite fold_left_false in HeqContr.
            rewrite andb_false_r in HeqContr.
            rewrite HeqContr in Hb'.
            rewrite fold_left_false in Hb'. discriminate.

        (*
          Case 2 and 3: (r is still simplicial)
          a     r --- nbors (clique)
           \---------/
          a     r --- nbors (clique)     r'
           \----------------------------/
        *)
        -- eapply SimplicialAddEdge; eauto.
          rewrite <- Hedge' in Hb.
          rewrite ig_insert_edge_isolated_nbors in Hb by now assumption.
          apply nbors_is_cliqueb_ig_insert_edge in Hb; eauto.
          unfold is_simplicialb in IHV.
          assert (well_formed g') as WF'.
          rewrite <- Hrem. apply ig_remove_node_wf. assumption.
          specialize (IHV r WF').
          rewrite Ha, Hb in IHV. cbn in IHV.
          specialize (IHV eq_refl). assumption.
Admitted.

Lemma find_next_simplicial :
  forall (g : InterfGraph.dict) (r : reg),
    well_formed g ->
    find_next g = Some r ->
    is_simplicial r g
.
Proof.
  intros g r H H'. unfold find_next in H'.
  apply is_simplicialb_is_simplicial. assumption.
  apply find_some in H'. destruct H' as [H1 H2]. assumption.
Qed.

Inductive is_chordal : InterfGraph.dict -> Prop :=
  | ChordalEmpty : is_chordal InterfGraph.empty
  | ChordalStep : forall g,
    (*
      Here well-formedness is not an assumption because the existance of a
      simplicial node already implies well-fromedness
    *)
    (exists r, is_simplicial r g /\ is_chordal (ig_remove_node g r)) ->
    is_chordal g
.

Lemma ig_insert_node_ig_remove_node_not_in :
  forall g u,
    ~ In u (InterfGraph.keys g) ->
    ig_remove_node (ig_insert_node g u) u = g
.
Proof.
Admitted.

Lemma ig_insert_node_ig_remove_node_comm :
  forall g u v,
    u <> v ->
    ig_remove_node (ig_insert_node g u) v =
    ig_insert_node (ig_remove_node g v) u
.
Proof.
Admitted.

Lemma set_remove_not_in :
  forall {A : Type} Aeq_dec (s : set A) (a b : A) ,
    a <> b -> ~ In a s -> ~ In a (set_remove Aeq_dec b s)
.
Proof.
Admitted.

Lemma ig_remove_node_not_in_2 :
  forall g u,
    ~ In u (InterfGraph.keys g) ->
    ig_remove_node g u = g
.
Proof.
Admitted.

Lemma is_simplicial_ig_insert_node :
  forall g u v,
    u <> v ->
    is_simplicial u (ig_insert_node g v) -> is_simplicial u g
.
Proof.
Admitted.

Lemma is_simplicial_ig_remove_node :
  forall g u v,
    u <> v ->
    is_simplicial u g -> is_simplicial u (ig_remove_node g v)
.
Proof.
Admitted.

From Stdlib Require Import Program.Equality.

Lemma is_chordal_inversion :
  forall g u,
    is_chordal g -> is_chordal (ig_insert_node g u)
.
Proof.
Admitted.

Lemma is_chordal_ig_insert_node :
  forall g u,
    well_formed g ->
    is_chordal (ig_insert_node g u) <-> is_chordal g
.
Proof.
  intros g u WF.
  split.
  - intros H.
    destruct (in_dec InterfGraph.key_eq_dec u (InterfGraph.keys g)) as [Inug | NInug].
    apply ig_insert_node_already_in in Inug.
    rewrite Inug in H.
    assumption.
    inversion H as [| g' Hc Egg'].
    * assert (In u (set_add InterfGraph.key_eq_dec u (InterfGraph.keys g))) as Contr.
      apply set_add_in. rewrite <- H0 in Contr. contradiction.
    * destruct Hc as [r [H1 H2]].
      destruct (InterfGraph.key_eq_dec u r) as [Eur | NEur]; subst.

      (* Trivial with u = r *)
      apply ig_insert_node_ig_remove_node_not_in in NInug.
      rewrite NInug in H2. assumption.

      (*
        Non-trivial with u <> r:
        I have to prove that u is also simplicial and that, if I remove it,
        I get another chordal graph.
      *)
      assert (Hin := NInug).
      apply SimplicialAddSingleton in NInug; try assumption.
      apply ChordalStep.
      exists r. split.
      apply is_simplicial_ig_insert_node with (v := u); try (symmetry; assumption).
      assumption.
      inversion H2 as [| g'' Hc' Egg'].
      (* Contradiction *) admit.
      destruct Hc' as [r' [H1' H2']].
      apply ChordalStep.
      exists r'.
      destruct (InterfGraph.key_eq_dec u r'); subst; split.
      + admit.
      + admit.
      + admit.
      + admit.











Admitted.

Lemma is_simplicial_ig_insert_edge :
  forall g u v,
    u <> v ->
    ~ In u (InterfGraph.keys g) ->
    is_simplicial u (ig_insert_edge g u v)
.
Proof.
Admitted.

Inductive even : nat -> Prop :=
| E0 : even 0
| E2: forall n, even n -> even (S (S n)).

Inductive property : nat -> Prop :=
| P0 : property 0
| PS : forall n, property n -> property (S n).

Goal forall n, even n -> property n.
  intros n H.
  induction H.
  - apply P0.
  - apply PS. apply PS. assumption.
Qed.

Lemma is_chordal_ig_remove_node :
  forall g u,
    is_simplicial u g ->
    is_chordal g ->
    is_chordal (ig_remove_node g u)
.
Proof.
  intros g u Hs Hc.
  induction Hs.
  - dependent induction Hc.
    * assert (In u (set_add InterfGraph.key_eq_dec u (InterfGraph.keys g))) as Contr.
      apply set_add_in. rewrite <- x in Contr. contradiction.
    * destruct H1 as [r [Hs Hc]].
      destruct (reg_eq_dec u r) as [Eur | NEur].
      subst; assumption.

      (*
        r simplicial  chordal
              r
              |\
            u | X      u   X
              |/          /
              X          X
        _____________________?
               chordal
                  r
                  |\
                  | X
                  |/
                  X
      *)
      apply ChordalStep.
      assert (Hin := H0).
      apply ig_insert_node_ig_remove_node_not_in in Hin.
      rewrite Hin. exists r. split.
      apply is_simplicial_ig_insert_node with (v := u);
      apply not_eq_sym in NEur; assumption.
      rewrite ig_insert_node_ig_remove_node_comm in Hc; try assumption.
      assert (~ In u (InterfGraph.keys (ig_remove_node g r))).
      cbn.
      apply set_remove_not_in; assumption.
      apply is_chordal_ig_insert_node in Hc. assumption.
      apply ig_remove_node_wf; assumption.

    (*
      u simplicial  chordal
                       r'
          u---X      u---X
           \ /        \ /
            X          X
      _____________________?
             chordal
                r'
                  X
                 /
                X
    *)
  - apply is_chordal_ig_insert_node in Hc.
    specialize (IHHs Hc).
    rewrite ig_insert_node_ig_remove_node_comm; try (symmetry; assumption).
    apply is_chordal_ig_insert_node.
    apply ig_remove_node_wf, is_simplicial_wf with (r := u); assumption.
    assumption.
    apply is_simplicial_wf with (r := u); assumption.

    (*
      u simplicial  chordal
                     r'--r''
          u---X      u---X
           \ /        \ /
            X          X
      _____________________?
             chordal
              r'--r''
                  X
                 /
                X
      In particular, for the second assumption we have the following cases:
      chordal
      (which implies the conclusion if u is already removed)
       u---r'
        \ /
         r''
      chordal
      (which implies the conclusion if u is already removed and then we
      remove r'')
       u---r'--r''
        \ /
         X
      chordal
      (which implies the conclusion if u is already removed and then we
      remove r')
       u---r''-r'
        \ /
         X
      chordal
      (which implies the conclusion if u is already removed and then we
      remove r' and r'')
       r'--r''
       u---X
        \ /
         X

    *)
  - destruct
      (in_dec InterfGraph.key_eq_dec r' (InterfGraph.get g u)) as [Inrn' | NInrn'],
      (in_dec InterfGraph.key_eq_dec r'' (InterfGraph.get g u)) as [Inrn'' | NInrn''].
    * assert (ig_insert_edge g r' r'' = g) as Hg.
      admit.
      rewrite Hg.
      rewrite Hg in Hc.
      specialize (IHHs Hc). assumption.
    * assert (WF := Hs); apply is_simplicial_wf in WF.
      destruct (in_dec InterfGraph.key_eq_dec r'' (InterfGraph.keys g)) as [Inrk | NInrk].
      apply ig_insert_edge_not_in with (u := r') (v := r'') in WF; try assumption.




      (* assert (is_simplicial u (ig_remove_node g r)).
      rewrite ig_insert_node_ig_remove_node_comm in H2; try assumption.
      admit. *)


  (* intros g.
  remember (InterfGraph.keys g) as V eqn:EV. revert g EV.
  induction V as [| a].
  - intros g Hn r WF Hc.
    unfold ig_remove_node.
    rewrite <- Hn. cbn.
    destruct WF as [_ [_ [_ [_ [WF _]]]]].
    assert (forall x, InterfGraph.get g x = []) as FE.
    intros x. specialize (WF x). rewrite <- Hn in WF.
    pose proof in_nil. specialize (H reg x).
    specialize (WF H). assumption.
    apply functional_extensionality in FE.
    unfold InterfGraph.get in FE.
    rewrite application_remove with (f := snd g) in FE.
    rewrite FE.
    apply ChordalEmpty.
  - intros g H r WF Hc.
    assert (H' := H).
    apply invert_keys in H.
    destruct H as [g' [[Hsing | Hedge] [Hkeys [Hin Hrem]]]].
    * specialize (IHV g').
      rewrite Hkeys in H'. injection H' as H'.
      specialize (IHV H' r).
      apply ig_remove_node_wf with (u := a) in WF. rewrite Hrem in WF.
      specialize (IHV WF). *)
Admitted.

Lemma ig_insert_node_chordal :
  forall g u,
    is_chordal (ig_insert_node g u) ->
    ~ In u (InterfGraph.keys g) ->
    is_chordal g
.
Proof.
Admitted.

Lemma ig_insert_node_ig_remove_node :
  forall g g' u,
    ig_insert_node g' u = g ->
    ig_remove_node g u = g'
.
Proof.
Admitted.

Lemma ig_remove_node_simplicial :
  forall g u v,
    u <> v ->
    is_simplicial u g ->
    is_simplicial u (ig_remove_node g v)
.
Proof.
Admitted.

Lemma is_simplicial_is_simplicialb :
  forall g r,
    well_formed g ->
    is_simplicial r g ->
    is_simplicialb g r = true
.
Proof.
Admitted.

Lemma ig_insert_node_in_in :
  forall g u v,
    In u (InterfGraph.keys g) ->
    In u (InterfGraph.keys (ig_insert_node g v))
.
Proof.
  intros g u v H1. cbn.
  apply set_add_intro1 with (Aeq_dec := reg_eq_dec) (b := v) in H1.
  assumption.
Qed.

Lemma ig_insert_edge_in_in :
  forall g u v w,
    In u (InterfGraph.keys g) ->
    In u (InterfGraph.keys (ig_insert_edge g v w))
.
Proof.
  intros g u v w H.
  unfold InterfGraph.keys, ig_insert_edge, ig_update_edge.
  destruct (reg_eq_dec v w).
  - unfold InterfGraph.keys in H. assumption.
  - cbn.
    apply set_add_intro1.
    apply set_add_intro1.
    assumption.
Qed.

Lemma ig_insert_edges_in_in :
  forall g u v vs,
    In u (InterfGraph.keys g) ->
    In u (InterfGraph.keys (ig_insert_edges g v vs))
.
Proof.
Admitted.

Lemma is_simplicial_in :
  forall g r,
    is_simplicial r g -> In r (InterfGraph.keys g)
.
Proof.
  intros g r H. induction H.
  apply ig_insert_node_in.
  apply ig_insert_node_in_in. assumption.
  apply ig_insert_edge_in_in. assumption.
  apply ig_insert_edges_in_in. assumption.
Qed.

Theorem eliminate_step_invariant :
  forall g,
    well_formed g ->
    is_chordal g ->
    match eliminate_step g with
    | Some (_, g') => is_chordal g'
    | None => g = InterfGraph.empty
    end
.
Proof.
  intros g WF Hch.
  assert (Hch' := Hch).
  induction Hch as [| g H].
  - now cbn.
  - unfold eliminate_step.
    destruct (find_next g) eqn:Efn.
    * apply find_next_simplicial in Efn; try assumption.
      apply is_chordal_ig_remove_node; try assumption.
    * destruct H as [r [H1 H2]].
      unfold find_next in Efn.
      apply find_none with (x := r) in Efn.
      apply is_simplicial_is_simplicialb in H1; try assumption.
      rewrite H1 in Efn. discriminate.
      apply is_simplicial_in. assumption.
Qed.

Inductive is_clique : InterfGraph.dict -> list reg -> Prop :=
  | CliqueEmpty : forall g, is_clique g []
  | CliqueAddNode : forall g r rs, is_clique g rs ->
    is_clique (ig_insert_edges g r rs) (r :: rs)
.

(* Inductive is_peo : InterfGraph.dict -> list reg -> Prop :=
  | PeoEmpty : is_peo InterfGraph.empty []
  | PeoAddEdge : forall g' r rs,
    is_peo g' rs ->
    (exists g, InterfGraph.keys g = r :: (InterfGraph.keys g') /\ is_simplicial r g)
    is_peo g (r :: rs)
.

Lemma eliminate_is_peo : *)