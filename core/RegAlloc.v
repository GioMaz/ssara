From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import Utils.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Dict.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Ssara.Core Require Import Syntax.
From Stdlib Require Import Bool.
From Stdlib Require Import ListSet.

(* Check whether regs are neighbors of r *)
Definition neighborsb (r : reg) (regs : list reg) (g : ig) : bool :=
  vregs_mem r (dict_keys g) &&
  fold_left
    (fun b r' =>
      b &&
      ((r =? r') ||
        vregs_mem r' (dict_map g r)))
    regs
    true
.

Definition simplicialb (r : reg) (g : ig) : bool :=
  let regs := dict_map g r in
  vregs_mem r (dict_keys g) &&
  fold_left (* Check whether the neighbor set of r is a clique *)
    (fun b r =>
      b &&
      neighborsb r regs g
    )
    regs
    true
.

Definition find_next (g : ig) : option reg :=
  let fix find_next_aux (regs : list reg) : option reg :=
    match regs with
    | nil => None
    | r :: rs =>
      if simplicialb r g then Some r else find_next_aux rs
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

From Ssara.Core Require Import RegPregInstance.
From Ssara.Core Require Import RegVregInstance.

Instance dict_coloring_instance : DictClass := {|
  key := vreg;
  value := preg;
  default := RAX;
  key_eq_dec := Nat.eq_dec;
|}.
Definition coloring := dict.

(*
  The partial_coloring is performed this way:
  - Get a perfect elimination order (ordering that eliminates simplicial nodes first)
  - For each node in the peo reinsert it into the graph and color it differently wrt its neighbor
*)
Definition color_diff (colors : list preg) : option preg :=
  match set_diff preg_eq_dec preg_all colors with
  | nil => None
  | c :: _ => Some c
  end
.

(*
  By definition of peo the `nbors` list contains all the neighbors of `v`
*)
Definition color_vreg (v : vreg) (deleted : list vreg) (c : coloring) (g : ig) : option preg :=
  let nbors := dict_map g v in
  let colors := map (dict_map c) nbors in
  color_diff colors
.

Definition color (peo : list vreg) (g : ig) : option coloring :=
  let fix color_aux (peo : list vreg) (deleted : list vreg) (c : coloring) (g : ig) : option coloring :=
    match peo with
    | nil => Some c
    | v :: peo' =>
      match color_vreg v deleted c g with
      | Some p =>
        let c' := dict_update c v p in
        color_aux peo' (v :: deleted) c' g
      | None => None
      end
    end
  in
  color_aux peo nil dict_empty g
.

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
  | Val v => @Val reg_preg_instance (color_val c v)
  | Neg v => @Neg reg_preg_instance (color_val c v)
  | Load v => @Load reg_preg_instance (color_val c v)
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
  | _, O => Block O nil nil Halt
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

  Definition fuel : nat := 10.

  Compute
    let g := get_ig example_block_1 fuel in
    dict_list g
  .

  Compute
    let g := get_ig example_block_1 fuel in
    let (g' , peo) := eliminate g fuel in
    peo
  .

  Compute
    let g := get_ig example_block_1 fuel in
    let (g' , peo) := eliminate g fuel in
    let c := color peo g in
    let p :=
      match c with
      | Some c' => color_block c' example_block_1
      | None => @Block reg_preg_instance O nil nil Halt
      end
    in
    visit_pblock p fuel
  .
End Example1.

(*
TODO:
- Generic map data type V
- Register allocation
- Maybe visualize the interference graph in OCaml
*)