From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import RegSet.
From Ssara.Core Require Import LivenessInfo.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Peo.
From Ssara.Core Require Import Dict.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Ssara.Core Require Import IR.
From Stdlib Require Import Bool.
From Ssara.Core Require Import RegVregInstance.
From Ssara.Core Require Import RegPregInstance.

Instance dict_coloring_instance : DictClass := {|
  key := vreg;
  value := preg;
  default := tmp;
  key_eq_dec := Nat.eq_dec;
|}.
Definition coloring := dict.

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
Definition color_vreg (v : vreg) (c : coloring) (g : ig) : option preg :=
  let nbors := dict_map g v in
  let used := map (dict_map c) nbors in
  preg_compl used
.

(*
  The None constructor is returned if there aren't enough physical registers
  for the coloring to happen, this may happen if we don't perform spilling
  before the coloring.
*)
Definition get_coloring (peo : list vreg) (g : ig) : option coloring :=
  let fix get_coloring_aux (peo : list vreg) (c : coloring) (g : ig) : option coloring :=
    match peo with
    | nil => Some c
    | v :: peo =>
      match color_vreg v c g with
      | Some p =>
        let c := dict_update c v p in
        get_coloring_aux peo c g
      | None => None
      end
    end
  in
  get_coloring_aux peo dict_empty g
.

(*
  Converting the intermediate representation into one using physical registers
  instead.
*)

Definition vphi : Type := @phi reg_vreg_instance.
Definition pphi : Type := @phi reg_preg_instance.

Definition color_phi (c : coloring) (p : vphi) : pphi :=
  match p with
  | Phi v vs =>
    @Phi reg_preg_instance
    (dict_map c v)
    (map (fun '(v, l) => (dict_map c v, l)) vs)
  end
.

Definition vval : Type := @val reg_vreg_instance.
Definition pval : Type := @val reg_preg_instance.

Definition color_val (c : coloring) (v : vval) : pval :=
  match v with
  | Imm x => Imm x
  | Reg v => @Reg reg_preg_instance (dict_map c v)
  | Ptr p => Ptr p
  end
.

Definition vexpr : Type := @expr reg_vreg_instance.
Definition pexpr : Type := @expr reg_preg_instance.

Definition color_expr (c : coloring) (e : vexpr) : pexpr :=
  match e with
  | Val v => Val (color_val c v)
  | Neg v => Neg (color_val c v)
  | Load v => Load (color_val c v)
  | Add v v' => @Add reg_preg_instance (dict_map c v) (color_val c v')
  | Sub v v' => @Sub reg_preg_instance (dict_map c v) (color_val c v')
  | Mul v v' => @Mul reg_preg_instance (dict_map c v) (color_val c v')
  | Div v v' => @Div reg_preg_instance (dict_map c v) (color_val c v')
  end
.

Definition vinst : Type := @inst reg_vreg_instance.
Definition pinst : Type := @inst reg_preg_instance.

Definition color_inst (c : coloring) (i : vinst) : pinst :=
  match i with
  | Def v e =>
    @Def reg_preg_instance
    (dict_map c v)
    (color_expr c e)
  | Store v v' =>
    @Store reg_preg_instance
    (color_val c v)
    (dict_map c v')
  end
.

Definition vjinst : Type := @jinst reg_vreg_instance.
Definition pjinst : Type := @jinst reg_preg_instance.
Definition vprogram : Type := @program reg_vreg_instance.
Definition pprogram : Type := @program reg_preg_instance.

CoFixpoint color_program (c : coloring) (p : vprogram) : pprogram :=
  match p with
  | Block l ps is j =>
    @Block reg_preg_instance
    l
    (map (color_phi c) ps)
    (map (color_inst c) is)
    (match j with
    | CondJump c' r v b1 b2 =>
      @CondJump reg_preg_instance c'
      (dict_map c r)
      (color_val c v)
      (color_program c b1)
      (color_program c b2)
    | Jump b => @Jump reg_preg_instance (color_program c b)
    | Halt => Halt
    end)
  end
.

(* Existing Instance reg_vreg_instance.

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
  Definition pi : programinfo := fst (analyze_program example_block_1 fuel).
  Compute dict_list pi.

  (* Get interference graph *)
  Definition g : ig := get_ig pi.
  Compute dict_list g.

  (* Get perfect elimination ordering *)
  (* Definition peo : list vreg := let (g', peo) := eliminate g in peo.
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
  Definition pi : programinfo := fst (analyze_program example_block_1 fuel).
  Compute dict_list pi.

  (* Get interference graph *)
  Definition g : ig := get_ig pi.
  Compute dict_list g.

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
End Example2. *)