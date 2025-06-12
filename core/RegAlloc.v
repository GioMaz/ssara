From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import RegSet.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Dict.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Ssara.Core Require Import Syntax.
From Stdlib Require Import Bool.
From Ssara.Core Require Import RegPregInstance.
From Ssara.Core Require Import RegVregInstance.

(* Check whether regs are neighbors of r *)
Definition are_neighbors (r : reg) (regs : list reg) (g : ig) : bool :=
  regs_mem r (dict_keys g) &&
  fold_left
    (fun b r' =>
      b &&
      ((r =? r') ||
        regs_mem r' (dict_map g r)))
    regs
    true
.

Definition is_simplicial (r : reg) (g : ig) : bool :=
  let regs := dict_map g r in
  regs_mem r (dict_keys g) &&
  fold_left (* Check whether the neighbor set of r is a clique *)
    (fun b r =>
      b &&
      are_neighbors r regs g
    )
    regs
    true
.

Definition find_next (g : ig) : option reg :=
  let fix find_next_aux (regs : list reg) : option reg :=
    match regs with
    | nil => None
    | r :: rs =>
      if is_simplicial r g then Some r else find_next_aux rs
    end
  in
  find_next_aux (dict_keys g)
.

Fixpoint eliminate (g : ig) (fuel : nat) : ig * list reg :=
  match fuel with
  | O => (g, nil)
  | S fuel' =>
    match find_next g with
    | Some next =>
      let g' := ig_remove_node g next in
      let (g'', peo) := eliminate g' fuel' in
      (g'', next :: peo)
    | None => (g, nil)
    end
  end
.

Instance dict_coloring_instance : DictClass := {|
  key := vreg;
  value := preg;
  default := RAX;
  key_eq_dec := Nat.eq_dec;
|}.
Definition coloring := dict.

(*
  The coloring is performed this way:
  - Get a perfect elimination order (ordering that eliminates simplicial nodes first)
  - For each node in the peo reinsert it into the graph and color it differently wrt its neighbor
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
Definition color (peo : list vreg) (g : ig) : option coloring :=
  let fix color_aux (peo : list vreg) (c : coloring) (g : ig) : option coloring :=
    match peo with
    | nil => Some c
    | v :: peo' =>
      match color_vreg v c g with
      | Some p =>
        let c' := dict_update c v p in
        color_aux peo' c' g
      | None => None
      end
    end
  in
  color_aux peo dict_empty g
.

(*
  Definition of a parallel IR using physical registers instead
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
  | CmpLt v v' => @CmpLt reg_preg_instance (dict_map c v) (color_val c v')
  | CmpLe v v' => @CmpLe reg_preg_instance (dict_map c v) (color_val c v')
  | CmpGt v v' => @CmpGt reg_preg_instance (dict_map c v) (color_val c v')
  | CmpGe v v' => @CmpGe reg_preg_instance (dict_map c v) (color_val c v')
  | CmpEq v v' => @CmpEq reg_preg_instance (dict_map c v) (color_val c v')
  | CmpNe v v' => @CmpNe reg_preg_instance (dict_map c v) (color_val c v')
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
Definition vblock : Type := @block reg_vreg_instance.
Definition pblock : Type := @block reg_preg_instance.

CoFixpoint color_block (c : coloring) (b : vblock) : pblock :=
  match b with
  | Block l ps is j =>
    @Block reg_preg_instance
    l
    (map (color_phi c) ps)
    (map (color_inst c) is)
    (match j with
    | Jnz v b1 b2 => @Jnz reg_preg_instance (dict_map c v) (color_block c b1) (color_block c b2)
    | Jmp b => @Jmp reg_preg_instance (color_block c b)
    | Halt => Halt
    end)
  end
.

Fixpoint visit_pblock (b : pblock) (fuel : nat) : pblock :=
  match b, fuel with
  | _, O => block_empty
  | Block l ps is j, S fuel' =>
    Block l ps is
    match j with
    | Jnz p b1 b2 => Jnz p (visit_pblock b1 fuel') (visit_pblock b2 fuel')
    | Jmp b => Jmp (visit_pblock b fuel')
    | Halt => Halt
    end
  end
.

Module Example1.
  CoFixpoint example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(1, 1); (5, 4)];
      r(4) <- phi [(2, 1); (6, 4)]
    ] [
    ] (
      Jmp example_block_3
    )
  with example_block_3 : block :=
    Block 3 [
    ] [
      r(5) <- r(3) + (Imm 1);
      r(6) <- r(4) + (Imm 1)
    ] (
      Jmp example_block_4
    )
  with example_block_4 : block :=
    Block 4 [
    ] [
    ] (
      Jmp example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(1) <- (Imm 34);
      r(2) <- (Imm 35)
    ] (
      Jmp example_block_2
    )
  .

  Definition fuel : nat := 20.

  (* Get interference graph *)
  Definition g : ig := get_ig example_block_1 fuel.
  Compute dict_list g.

  (* Get perfect elimination ordering *)
  Definition eliminate_result : (ig * list vreg) := eliminate g fuel.
  Compute
    let (g' , peo) := eliminate_result in
    peo
  .

  (* Get coloring *)
  Definition c := let (g', peo) := eliminate_result in color peo g.
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
      | Some c' => color_block c' example_block_1
      | None => @Block reg_preg_instance O nil nil Halt
      end
    in
    visit_pblock p fuel
  .
End Example1.