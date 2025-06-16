From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import RegSet.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Dict.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.

From Ssara.Core Require Import RegVregInstance.
Existing Instance reg_vreg_instance.

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

(*
  We need to use `vreg` instead of `reg` for the OCaml extraction
*)
Fixpoint eliminate (g : ig) (fuel : nat) : ig * list vreg :=
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