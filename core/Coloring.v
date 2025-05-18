From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Utils.
From Ssara.Core Require Import Interference.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
Import ListNotations.
From Stdlib Require Import Bool.

(* Check whether r has regs neighbors *)
Definition neighbors (r : reg) (regs : list reg) (g : ig) : bool :=
  regs_mem r (ig_dom g) &&
  fold_left
    (fun b r' =>
      b && (
        (r =? r') ||
        regs_mem r' (ig_map g r)
      )
    )
    regs
    true
.

Definition simplicial (r : reg) (g : ig) : bool :=
  let regs := ig_map g r in
  regs_mem r (ig_dom g) &&
  fold_left (* Check whether the neighbor set of r is a clique *)
    (fun b r =>
      b &&
      neighbors r regs g
    )
    regs
    true
.

Definition find_next (g : ig) : option reg :=
  let fix find_next_aux (regs : list reg) : option reg :=
    match regs with
    | nil => None
    | r :: rs =>
      if simplicial r g then Some r else find_next_aux rs
    end
  in
  find_next_aux (ig_dom g)
.

Fixpoint eliminate (g : ig) (fuel : nat) : ig * list reg :=
  match fuel with
  | O => (g, nil)
  | S fuel' =>
    match find_next g with
    | Some next =>
      let g' := ig_remove_node g next in
      let (g'', regs) := eliminate g' fuel' in
      (g'', next :: regs)
    | None => (g, nil)
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
    map (fun r => (r, ig_map g r)) (ig_dom g)
  .

  Compute
    let g := get_ig example_block_1 fuel in
    let (g' , l) := eliminate g fuel in
    (list_of_ig g', l)
  .
End Example1.