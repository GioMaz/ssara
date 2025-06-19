From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import RegSet.
From Ssara.Core Require Import LivenessInfo.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Peo.
From Ssara.Core Require Import Dict.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Ssara.Core Require Import Syntax.
From Stdlib Require Import Bool.
From Ssara.Core Require Import RegVregInstance.
From Ssara.Core Require Import RegPregInstance.

Module ColoringParams <: DICT_PARAMS.
  Definition key : Set := vreg.
  Definition value : Type := preg.
  Definition default : value := tmp.
  Definition key_eq_dec := Nat.eq_dec.
End ColoringParams.
Module Coloring := MakeDict(ColoringParams).

(*
  The coloring is performed this way:
  - Get a perfect elimination order (ordering that eliminates simplicial nodes first)
  - For each node in the peo reinsert it into the graph and color it differently wrt its neighbors
*)
Definition preg_compl (colors : list preg) : option preg :=
  match @regs_diff reg_preg_instance preg_all_minus_tmp colors with
  | nil => None
  | c :: _ => Some c
  end
.

(*
  By definition of PEO the `nbors` list contains all the neighbors of `v`
*)
Definition color_vreg (v : vreg) (c : Coloring.dict) (ig : InterfGraph.dict) : option preg :=
  let nbors := InterfGraph.get ig v in
  let used := map (Coloring.get c) nbors in
  preg_compl used
.

(*
  The None constructor is returned if there aren't enough physical registers
  for the coloring to happen, this may happen if we don't perform spilling
  before the coloring.
*)
Definition get_coloring (peo : list vreg) (ig : InterfGraph.dict) : option Coloring.dict :=
  let fix get_coloring_aux (peo : list vreg) (c : Coloring.dict) (ig : InterfGraph.dict) : option Coloring.dict :=
    match peo with
    | nil => Some c
    | v :: peo' =>
      match color_vreg v c ig with
      | Some p =>
        let c' := Coloring.update c v p in
        get_coloring_aux peo' c' ig
      | None => None
      end
    end
  in
  get_coloring_aux peo Coloring.empty ig
.

(*
  Definition of a parallel IR using physical registers instead
*)

Definition vphi : Type := @phi reg_vreg_instance.
Definition pphi : Type := @phi reg_preg_instance.

Definition color_phi (c : Coloring.dict) (p : vphi) : pphi :=
  match p with
  | Phi v vs =>
    @Phi reg_preg_instance
    (Coloring.get c v)
    (map (fun '(v, l) => (Coloring.get c v, l)) vs)
  end
.

Definition vval : Type := @val reg_vreg_instance.
Definition pval : Type := @val reg_preg_instance.

Definition color_val (c : Coloring.dict) (v : vval) : pval :=
  match v with
  | Imm x => Imm x
  | Reg v => @Reg reg_preg_instance (Coloring.get c v)
  | Ptr p => Ptr p
  end
.

Definition vexpr : Type := @expr reg_vreg_instance.
Definition pexpr : Type := @expr reg_preg_instance.

Definition color_expr (c : Coloring.dict) (e : vexpr) : pexpr :=
  match e with
  | Val v => Val (color_val c v)
  | Neg v => Neg (color_val c v)
  | Load v => Load (color_val c v)
  | Add v v' => @Add reg_preg_instance (Coloring.get c v) (color_val c v')
  | Sub v v' => @Sub reg_preg_instance (Coloring.get c v) (color_val c v')
  | Mul v v' => @Mul reg_preg_instance (Coloring.get c v) (color_val c v')
  | Div v v' => @Div reg_preg_instance (Coloring.get c v) (color_val c v')
  end
.

Definition vinst : Type := @inst reg_vreg_instance.
Definition pinst : Type := @inst reg_preg_instance.

Definition color_inst (c : Coloring.dict) (i : vinst) : pinst :=
  match i with
  | Def v e =>
    @Def reg_preg_instance
    (Coloring.get c v)
    (color_expr c e)
  | Store v v' =>
    @Store reg_preg_instance
    (color_val c v)
    (Coloring.get c v')
  end
.

Definition vjinst : Type := @jinst reg_vreg_instance.
Definition pjinst : Type := @jinst reg_preg_instance.
Definition vprogram : Type := @program reg_vreg_instance.
Definition pprogram : Type := @program reg_preg_instance.

CoFixpoint color_program (c : Coloring.dict) (p : vprogram) : pprogram :=
  match p with
  | Block l ps is j =>
    @Block reg_preg_instance
    l
    (map (color_phi c) ps)
    (map (color_inst c) is)
    (match j with
    | CondJump c' r v b1 b2 =>
      @CondJump reg_preg_instance c'
      (Coloring.get c r)
      (color_val c v)
      (color_program c b1)
      (color_program c b2)
    | Jump b => @Jump reg_preg_instance (color_program c b)
    | Halt => Halt
    end)
  end
.

Existing Instance reg_vreg_instance.

Module Example1.
  CoFixpoint example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(1, 1); (5, 4)];
      r(4) <- phi [(2, 1); (6, 4)]
    ] [
    ] (
      Jump example_block_3
    )
  with example_block_3 : block :=
    Block 3 [
    ] [
      r(5) <- r(3) + (Imm 1);
      r(6) <- r(4) + (Imm 1)
    ] (
      Jump example_block_4
    )
  with example_block_4 : block :=
    Block 4 [
    ] [
    ] (
      Jump example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(1) <- (Imm 34);
      r(2) <- (Imm 35)
    ] (
      Jump example_block_2
    )
  .

  Definition fuel : nat := 20.

  (* Get liveness information *)
  Definition pi : ProgramInfo.dict := fst (analyze_program example_block_1 fuel).
  Compute ProgramInfo.list pi.

  (* Get interference graph *)
  Definition ig : InterfGraph.dict := get_ig pi.
  Compute InterfGraph.list ig.

  (* Get perfect elimination ordering *)
  (* Definition peo : list vreg := eliminate g.
  Compute peo.

  (* Get coloring *)
  Definition c := get_coloring peo g.

  (* Color program *)
  Compute
    let p :=
      match c with
      | Some c' => color_program c' example_block_1
      | None => @Block reg_preg_instance O nil nil Halt
      end
    in
    visit_program p fuel
  . *)
End Example1.

Module Example2.
  Definition example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(0, 1)]
    ] [
      store (Ptr 0) r(3)
    ] (
      Halt
    )
  .

  Definition example_block_3 : block :=
    Block 3 [
      r(4) <- phi [(1, 1)]
    ] [
      store (Ptr 0) r(4)
    ] (
      Halt
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(0) <- (Imm 34);
      r(1) <- (Imm 35)
    ] (
      if r(0) < (Reg 1) then example_block_2 else example_block_3
    )
  .

  Definition fuel : nat := 20.

  (* Get liveness information *)
  Definition pi : ProgramInfo.dict := fst (analyze_program example_block_1 fuel).
  Compute ProgramInfo.list pi.

  (* Get interference graph *)
  Definition ig : InterfGraph.dict := get_ig pi.
  Compute InterfGraph.list ig.

  (* Get perfect elimination ordering *)
  (* Definition peo : list vreg := let (g', peo) := eliminate g fuel in peo.
  Compute peo.

  (* Get coloring *)
  Definition c := get_coloring peo g.
  Compute
    match c with
    | Some c' => dict_list c'
    | None => nil
    end
  .

  (* Color program *)
  Compute
    let p :=
      match c with
      | Some c' => color_program c' example_block_1
      | None => @Block reg_preg_instance O nil nil Halt
      end
    in
    visit_program p fuel
  . *)
End Example2.