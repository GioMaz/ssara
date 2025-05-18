From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Utils.
From Ssara.Core Require Import LivenessInfo.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.
Import ListNotations.

(* Interference graph definition as a map from a register to its adjacence set *)
Definition ig : Type := set reg * (reg -> set reg).
Definition ig_empty : ig := (nil, fun _ => nil).
Definition ig_update (g : ig) (k : reg) (v : set reg) : ig :=
  let (regs, nbors) := g in
  (regs_add k regs, fun r => if r =? k then v else nbors r)
.
Definition ig_nbors (g : ig) (k : reg) : set reg :=
  let (_, nbors) := g in nbors k
.
Definition ig_v (g : ig) : set reg :=
  let (v, _) := g in v
.

Definition ig_update_edge (f : reg -> set reg -> set reg) (r : reg) (r' : reg) (g : ig) : ig :=
  let regs  := ig_nbors g r in
  let g'    := ig_update g r (f r' regs) in
  let regs' := ig_nbors g' r' in
  ig_update g' r' (f r regs')
.

Definition ig_remove_edge := ig_update_edge regs_remove.
Definition ig_insert_edge := ig_update_edge regs_add.

Definition ig_remove_node (g : ig) (r : reg) : ig :=
  let (v, nbors) := fold_left
    (fun g_acc r' =>
      ig_remove_edge r r' g_acc)
    (ig_v g)
    g
  in
  (regs_remove r v, nbors)
.

Definition ig_insert_edges (g : ig) (r : reg) (regs : list reg) : ig :=
  fold_left
    (fun g_acc r' => if r =? r' then g else ig_insert_edge r r' g)
    regs
    g
.

Definition ig_insert_clique (g : ig) (regs : list reg) : ig :=
  fold_left
    (fun g_acc r => (ig_insert_edges g_acc r regs))
    regs
    g
.

Definition ig_insert_instinfo (g : ig) (ii : instinfo) : ig :=
  match ii with
  | InstInfo live_in live_out =>
    ig_insert_clique (ig_insert_clique g live_in) live_out 
  end
.

Definition ig_insert_instinfos (g : ig) (iis: list instinfo) : ig :=
  fold_left (fun g' ii => ig_insert_instinfo g' ii) iis g
.

Definition get_ig_programinfo (pi : programinfo) : ig :=
  let (ls, nbors) := pi in
  fold_left
    (fun g l =>
      match nbors l with
      | Some (BlockInfo iis) => ig_insert_instinfos g iis
      | None => g
      end
    )
    ls
    ig_empty
.

Definition get_ig (p : program) (fuel : nat) : ig :=
  let (pi, _) := analyze_program p fuel in
  get_ig_programinfo pi
.

Axiom get_ig_fixpoint : program -> ig.

(*
  +-----------+
  | r1 <- ... |
  | r2 <- ... |
  +-----------+
        |
        |     +-----------+
        |     |           |
  +-----------------+     |
  | r3 <- Φ(r1, r5) |     |
  | r4 <- Φ(r2, r6) |     |
  +-----------------+     |
         |                |
  +--------------+        |
  | r5 <- r3 + 1 |        |
  | r6 <- r4 + 1 |        |
  +--------------+        |
         |                |
         +----------------+
*)

Module Example3.
  CoFixpoint example_block_3 : block :=
    Block 3 [
    ] [
      r(5) <- r(3) + (Imm 1);
      r(6) <- r(4) + (Imm 1)
    ] (
      Jmp example_block_2
    )
  with example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(1, 1); (5, 3)];
      r(4) <- phi [(2, 1); (6, 3)]
    ] [
    ] (
      Jmp example_block_3
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

  Definition fuel : nat := 4.

  Compute
    let g := get_ig example_block_1 fuel in
    map (fun r => (r, ig_nbors g r)) (ig_v g)
  .
End Example3.

Module Example4.
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

  Definition fuel : nat := 4.

  Compute
    let g := get_ig example_block_1 fuel in
    map (fun r => (r, ig_nbors g r)) (ig_v g)
  .
End Example4.