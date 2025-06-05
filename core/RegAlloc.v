From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import Utils.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Dict.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
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
  default := NOREG;
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

(* Definition vphi := phi reg_vreg_instance.
Definition pphi := phi reg_preg_instance.

Definition color_phi (p : phi) (c : coloring) :=
  match p with
  | Phi v vs => Phi (dict_map c v) (fold_left (dict_map c) vs)
  end
.

Definition color_program (p : program) (c : coloring) : program :=

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
    dict_list c
  .
End Example1.

(*
TODO:
- Generic map data type V
- Register allocation
- Maybe visualize the interference graph in OCaml
*) *)