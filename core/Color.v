From Ssara.Core Require Import LivenessInfo.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Peo.
From Ssara.Core Require Import Dict.
From Ssara.Core Require Import Utils.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ListSet.
Import ListNotations.
From Ssara.Core Require Import IR.
From Stdlib Require Import Bool.

From Ssara.Core Require Import IRVregModule.
From Ssara.Core Require Import IRPregModule.

Module ColoringParams <: DICT_PARAMS.
  Definition key := IRVreg.reg.
  Definition value := IRPreg.reg.
  Definition default : value := UNASSIGNED.
  Definition key_eq_dec := Nat.eq_dec.
End ColoringParams.
Module Coloring := MakeDict ColoringParams.

(*
  The coloring is performed this way:
  - Get a perfect elimination order (ordering that eliminates simplicial nodes first)
  - For each node in the peo reinsert it into the graph and color it differently wrt its neighbors
*)
Definition preg_compl (colors : list IRPreg.reg) : option IRPreg.reg :=
  hd_error (IRPreg.regs_diff preg_allowed colors)
.

Lemma hd_error_in :
  forall {A : Type} (l : set A) (a : A),
    hd_error l = Some a -> In a l
.
Proof.
  intros A l a H.
  destruct l as [| x xs].
  - discriminate.
  - cbn in H. injection H as H. rewrite H. cbn. left. reflexivity.
Qed.

Lemma preg_compl_not_forbidden :
  forall colors p,
    preg_compl colors = Some p ->
    ~ In p preg_forbidden
.
Proof.
  intros colors p H.
  unfold preg_compl in H.
  apply preg_allowed_in .
  apply hd_error_in in H.
  apply set_diff_elim1 in H.
  assumption.
Qed.

Definition get_color (v : IRVreg.reg) (g : InterfGraph.dict) (c : Coloring.dict) : option IRPreg.reg :=
  let nbors := InterfGraph.get g v in
  let used := map (Coloring.get c) nbors in
  preg_compl used
.

Lemma get_color_not_forbidden :
  forall v g c p,
    get_color v g c = Some p ->
    ~ In p preg_forbidden
.
Proof.
  intros v g c.
  apply preg_compl_not_forbidden.
Qed.

(*
  The None constructor is returned if there aren't enough physical registers
  for the coloring to happen, this may happen if we don't perform spilling
  before the coloring.
*)
Fixpoint get_coloring_aux (peo : list IRVreg.reg) (g : InterfGraph.dict) (c : Coloring.dict) : option Coloring.dict :=
  match peo with
  | nil => Some c
  | v :: peo =>
    match get_color v g c with
    | Some p => get_coloring_aux peo g (Coloring.update c v p)
    | None => None
    end
  end
.

Definition get_coloring (peo : list IRVreg.reg) (g : InterfGraph.dict) : option Coloring.dict :=
  get_coloring_aux (rev peo) g Coloring.empty
.

(*
  Converting the intermediate representation into one using physical registers
  instead.
*)

Definition color_phi (c : Coloring.dict) (p : IRVreg.phi) : IRPreg.phi :=
  match p with
  | IRVreg.Phi v vs =>
    IRPreg.Phi
    (Coloring.get c v)
    (map (fun '(v, l) => (Coloring.get c v, l)) vs)
  end
.

Definition color_val (c : Coloring.dict) (v : IRVreg.val) : IRPreg.val :=
  match v with
  | IRVreg.Imm x => IRPreg.Imm x
  | IRVreg.Reg v => IRPreg.Reg (Coloring.get c v)
  | IRVreg.Ptr p => IRPreg.Ptr p
  end
.

Definition color_expr (c : Coloring.dict) (e : IRVreg.expr) : IRPreg.expr :=
  match e with
  | IRVreg.Val v => IRPreg.Val (color_val c v)
  | IRVreg.Load v => IRPreg.Load (color_val c v)
  | IRVreg.Add v v' => IRPreg.Add (Coloring.get c v) (color_val c v')
  | IRVreg.Sub v v' => IRPreg.Sub (Coloring.get c v) (color_val c v')
  | IRVreg.Mul v v' => IRPreg.Mul (Coloring.get c v) (color_val c v')
  | IRVreg.Div v v' => IRPreg.Div (Coloring.get c v) (color_val c v')
  end
.

Definition color_inst (c : Coloring.dict) (i : IRVreg.inst) : IRPreg.inst :=
  match i with
  | IRVreg.Def v e =>
    IRPreg.Def
    (Coloring.get c v)
    (color_expr c e)
  | IRVreg.Store r r' =>
    IRPreg.Store
    (Coloring.get c r)
    (Coloring.get c r')
  end
.

CoFixpoint color_program (c : Coloring.dict) (p : IRVreg.program) : IRPreg.program :=
  match p with
  | IRVreg.Block l ps is j =>
    IRPreg.Block
    l
    (map (color_phi c) ps)
    (map (color_inst c) is)
    (match j with
    | IRVreg.CondJump c' r v b1 b2 =>
      IRPreg.CondJump c'
      (Coloring.get c r)
      (color_val c v)
      (color_program c b1)
      (color_program c b2)
    | IRVreg.Jump b => IRPreg.Jump (color_program c b)
    | IRVreg.Ret r => IRPreg.Ret (Coloring.get c r)
    end)
  end
.

Import IRVreg.

Module Example1.
  Definition example_block_4 : block :=
    Block (Normal 4) [
    ] [
      r(7) <- r(5) + r(6)
    ] (
      ret r(7)
    )
  .

  Definition example_block_3 : block :=
    Block (Normal 3) [
    ] [
      r(5) <- r(3) + i(1);
      r(6) <- r(4) + i(1)
    ] (
      Jump example_block_4
    )
  .

  Definition example_block_2 : block :=
    Block (Normal 2) [
      r(3) <- phi [(1, Normal 1)];
      r(4) <- phi [(2, Normal 1)]
    ] [
    ] (
      Jump example_block_3
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [
    ] [
      r(1) <- i(34);
      r(2) <- i(35)
    ] (
      Jump example_block_2
    )
  .

  (* Definition ig :=
    let (pi, _) := analyze_program example_block_1 10 in
    InterfGraph.get_ig pi
  .
  Compute InterfGraph.listify ig.

  Definition peo := eliminate_fuel ig 10.
  Compute peo.

  Definition c := get_coloring peo ig.
  Compute
    match c with
    | Some c => Coloring.listify c
    | None => nil
    end
  . *)
End Example1.

Module Example2.
  Definition example_block_2 : block :=
    Block (Normal 2) [
      r(3) <- phi [(0, Normal 1)]
    ] [
      r(4) <- r(3)
    ] (
      ret r(4)
    )
  .

  Definition example_block_3 : block :=
    Block (Normal 3) [
      r(5) <- phi [(1, Normal 1)]
    ] [
      r(6) <- r(5)
    ] (
      ret r(6)
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [
    ] [
      r(0) <- i(34);
      r(1) <- i(35)
    ] (
      if r(0) < r(1) then example_block_2 else example_block_3
    )
  .
End Example2.

(* Example 3 *)
Module Example3.
  Definition example_block_3 : block :=
    Block (Normal 3) [
    ] [
    ] (
      ret r(5)
    )
  .

  CoFixpoint example_block_2 : block :=
    Block (Normal 2) [
      r(2) <- phi [(0, Normal 1); (4, Normal 2)];   (* Iterator *)
      r(3) <- phi [(1, Normal 1); (5, Normal 2)]    (* Accumulator *)
    ] [
      r(4) <- r(2) - i(1);
      r(5) <- r(3) * r(4)
    ] (
      if r(4) <= i(1) then example_block_3 else example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [
    ] [
      r(0) <- i(5);   (* Iterator *)
      r(1) <- r(0)    (* Accumulator *)
    ] (
      Jump example_block_2
    )
  .
End Example3.

(* Example 4 *)
Module Example4.
  Definition example_block_3 : block :=
    Block (Normal 3) [
    ] [
    ] (
      ret r(3)
    )
  .

  CoFixpoint example_block_2 : block :=
    Block (Normal 2) [
      r(2) <- phi [(0, Normal 1); (3, Normal 2)]
    ] [
      r(3) <- r(2) + i(3)
    ] (
      if r(3) < r(1) then example_block_2 else example_block_3
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [
    ] [
      r(0) <- i(0);
      r(1) <- i(20)
    ] (
      Jump example_block_2
    )
  .
End Example4.

(* Example 5 *)
Module Example5.
  Definition example_block_3 : block :=
    Block (Normal 3) [
    ] [
    ] (
      ret r(6)
    )
  .

  CoFixpoint example_block_2 : block :=
    Block (Normal 2) [
      r(3) <- phi [(0, Normal 1); (4, Normal 2)];
      r(4) <- phi [(1, Normal 1); (6, Normal 2)];
      r(5) <- phi [(2, Normal 1); (7, Normal 2)]
    ] [
      r(6) <- r(4) + r(3);  (* New first block *)
      r(7) <- r(5) - i(1)   (* New iterator *)
    ] (
      if r(7) = i(1) then example_block_3 else example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [
    ] [
      r(0) <- i(0);  (* Second block *)
      r(1) <- i(1);  (* First block *)
      r(2) <- i(12)  (* Iterator*)
    ] (
      Jump example_block_2
    )
  .
End Example5.

(* Example 6 *)
Module Example6.
  Definition example_block_4 : block :=
    Block (Normal 4) [] [] (ret r(11)).

  Definition example_block_5 : block :=
    Block (Normal 5) [] [] (ret r(11)).

  Definition example_block_3 : block :=
    Block (Normal 3) [
      r(6) <- phi [(0, Normal 1); (3, Normal 2)];
      r(7) <- phi [(1, Normal 1); (4, Normal 2)];
      r(8) <- phi [(2, Normal 1); (5, Normal 2)]
    ] [
      r(9) <- r(6) + r(7);
      r(10) <- r(9) + r(8);
      r(11) <- r(10) * i(3)
    ] (
      if r(11) <= i(100) then example_block_4 else example_block_5
    )
  .

  Definition example_block_2 : block :=
    Block (Normal 2) [] [
      r(3) <- i(3);
      r(4) <- i(4);
      r(5) <- i(5)
    ] (
      jump example_block_3
      (* ret r(5) *)
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [] [
      r(0) <- i(1);
      r(1) <- i(2);
      r(2) <- i(3)
    ] (
      jump example_block_3
      (* ret r(2) *)
    )
  .

  Definition example_block_999 : block :=
    Block (Normal 999) [
    ] [
      r(999) <- i(0)
    ] (
      if r(999) < i(1000) then example_block_1 else example_block_2
    )
  .

  Definition pi := let (pi, _) := analyze_program example_block_999 100 in pi.
  Definition ig := get_ig pi.
  Definition peo := eliminate_fuel ig 100.
  Definition coloring := get_coloring peo ig.
  Definition irpreg_program :=
    match coloring with
    | Some coloring => Some (IRPreg.visit_program (color_program coloring example_block_1) 3)
    | None => None
    end
  .
  Compute irpreg_program.
End Example6.

(* Example 7 *)
Module Example7.
  Definition example_block_4 : block :=
    Block (Normal 4) [] [] (ret r(11)).

  Definition example_block_5 : block :=
    Block (Normal 5) [] [] (ret r(11)).

  Definition example_block_3 : block :=
    Block (Normal 3) [
      r(4) <- phi [(0, Normal 1); (2, Normal 2)];
      r(5) <- phi [(1, Normal 1); (3, Normal 2)]
    ] [
      r(6) <- r(4) * r(5);
      r(7) <- r(6) + i(1)
    ] (
      if r(7) <= i(100) then example_block_4 else example_block_5
    )
  .

  Definition example_block_2 : block :=
    Block (Normal 2) [] [
      r(2) <- i(2);
      r(3) <- i(3)
    ] (
      jump example_block_3
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [] [
      r(0) <- i(0);
      r(1) <- i(1)
    ] (
      jump example_block_3
    )
  .

  Definition example_block_999 : block :=
    Block (Normal 999) [
    ] [
      r(999) <- i(0)
    ] (
      if r(999) < i(1000) then example_block_1 else example_block_2
    )
  .

  Definition pi := let (pi, _) := analyze_program example_block_999 100 in pi.
  Definition ig := get_ig pi.
  Definition peo := eliminate_fuel ig 100.
  Definition coloring := get_coloring peo ig.
  Definition irpreg_program :=
    match coloring with
    | Some coloring => Some (IRPreg.visit_program (color_program coloring example_block_1) 3)
    | None => None
    end
  .
  Compute irpreg_program.
End Example7.

(* Example 8 *)
Module Example8.
  Definition example_block_3 : block :=
    Block (Normal 3) [
      r(4) <- phi [(2, Normal 1); (3, Normal 2)]
    ] [
      store r(0) r(1)
    ] (
      ret r(4)
    ).

  Definition example_block_2 : block :=
    Block (Normal 2) [] [
      r(3) <- r(0) + i(2)
    ] (
      jump example_block_3
    ).

  Definition example_block_1 : block :=
    Block (Normal 1) [] [
      r(2) <- r(0) + i(1)
    ] (
      jump example_block_3
    ).

  Definition example_block_0 : block :=
    Block (Normal 0) [] [
      r(0) <- i(5);
      r(1) <- i(10)
    ] (
      if r(0) < r(1) then example_block_1 else example_block_2
    ).

  Definition pi := let (pi, _) := analyze_program example_block_0 100 in pi.
  Definition ig := get_ig pi.
  Compute InterfGraph.listify ig.
  Definition peo := eliminate_fuel ig 100.
  Definition coloring := get_coloring peo ig.
  Definition irpreg_program :=
    match coloring with
    | Some coloring => Some (IRPreg.visit_program (color_program coloring example_block_1) 3)
    | None => None
    end
  .
  Compute irpreg_program.
End Example8.

(* Module Example8.
  Definition example_ig :=
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge
    (ig_insert_edge InterfGraph.empty
    1 2) 1 3) 7 2) 7 5) 8 5) 8 6) 2 3) 2 5) 6 4) 6 5) 3 4) 3 5) 4 5)
  .
  Definition peo := eliminate_fuel example_ig 100.
  Compute peo.
  Definition c := get_coloring peo example_ig.
  Compute
    match c with
    | Some c => Coloring.listify c
    | None => nil
    end
  .
End Example8. *)