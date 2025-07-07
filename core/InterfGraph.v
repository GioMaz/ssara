From Ssara.Core Require Import IR.
From Ssara.Core Require Import LivenessInfo.
From Ssara.Core Require Import Dict.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.
Import ListNotations.

From Ssara.Core Require Import IRVregModule.
Import IRVreg.

Module InterfGraphParams <: DICT_PARAMS.
  Definition key := reg.
  Definition value := set reg.
  Definition default : value := nil.
  Definition key_eq_dec := Nat.eq_dec.
End InterfGraphParams.

Module InterfGraph := MakeDict InterfGraphParams.

Definition ig_update_edge (f : reg -> set reg -> set reg) (g : InterfGraph.dict) (r : reg) (r' : reg) : InterfGraph.dict :=
  let regs  := InterfGraph.get g r in
  let g    := InterfGraph.update g r (f r' regs) in
  let regs := InterfGraph.get g r' in
  InterfGraph.update g r' (f r regs)
.
Definition ig_remove_edge := ig_update_edge regs_remove.
Definition ig_insert_edge := ig_update_edge regs_add.

Definition ig_insert_node (g : InterfGraph.dict) (r : reg) : InterfGraph.dict :=
  InterfGraph.update g r (InterfGraph.get g r)
.

Definition ig_remove_node (g : InterfGraph.dict) (r : reg) : InterfGraph.dict :=
  (regs_remove r (InterfGraph.keys g),
    snd (fold_left (fun g_acc r' => ig_remove_edge g_acc r r') (InterfGraph.keys g) g))
.

Lemma regs_size_decrease :
  forall (r : reg) (rs : list reg), In r rs -> length (regs_remove r rs) < length rs
.
Proof.
  intros r rs H. generalize dependent r.
  induction rs as [|hd rs IH].  (* Induction over the size of the list *)
  - contradiction.
  - simpl. intros r H. destruct H. (* Case analysis on (regs_remove r (hd :: rs)) *)
    + rewrite H. destruct Nat.eq_dec. auto. contradiction.
    + destruct Nat.eq_dec.
      * auto.
      * simpl. apply Arith_base.lt_n_S_stt. apply IH. assumption.
Qed.

Lemma ig_size_decrease :
  forall (g : InterfGraph.dict) (n : reg), In n (InterfGraph.keys g) -> InterfGraph.size (ig_remove_node g n) < InterfGraph.size g
.
Proof.
  intros g n H.
  destruct g as [keys map].
  induction keys as [|r rs IH].
  - contradiction.
  - destruct (r :: rs).
    contradiction.
    unfold ig_remove_node. unfold InterfGraph.size. unfold InterfGraph.keys. unfold fst.
    unfold InterfGraph.keys in H. unfold fst in H.
    apply regs_size_decrease. assumption.
Qed.

Fixpoint ig_insert_edges (g : InterfGraph.dict) (r : reg) (regs : list reg) : InterfGraph.dict :=
  match regs with
  | nil => g
  | r' :: tl =>
    if r =? r'
    then ig_insert_edges (ig_insert_node g r) r tl
    else ig_insert_edges (ig_insert_edge g r r') r tl
  end
.

Definition ig_insert_clique (g : InterfGraph.dict) (regs : list reg) : InterfGraph.dict :=
  fold_left
    (fun g_acc r => (ig_insert_edges g_acc r regs))
    regs
    g
.

Definition ig_insert_instinfo (g : InterfGraph.dict) (ii : instinfo) : InterfGraph.dict :=
  match ii with
  | InstInfo live_in live_out =>
    ig_insert_clique (ig_insert_clique g live_in) live_out 
  end
.

Definition ig_insert_instinfos (g : InterfGraph.dict) (iis: list instinfo) : InterfGraph.dict :=
  fold_left ig_insert_instinfo iis g
.

Definition get_ig (pi : ProgramInfo.dict) : InterfGraph.dict :=
  let (ls, nbors) := pi in
  fold_left
    (fun g l =>
      match nbors l with
      | Some (BlockInfo iis) => ig_insert_instinfos g iis
      | None => g
      end
    )
    ls
    InterfGraph.empty
.

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

Module Example1.
  CoFixpoint example_block_3 : block :=
    Block 3 [
    ] [
      r(5) <- r(3) + (Imm 1);
      r(6) <- r(4) + (Imm 1)
    ] (
      Jump example_block_2
    )
  with example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(1, 1); (5, 3)];
      r(4) <- phi [(2, 1); (6, 3)]
    ] [
    ] (
      Jump example_block_3
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

  Definition fuel : nat := 4.

  Compute
    let '(pi, _) := analyze_program example_block_1 fuel in
    let g := get_ig pi in
    InterfGraph.list g
  .
End Example1.

Module Example2.
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

  Definition fuel : nat := 4.

  Compute
    let '(pi, _) := analyze_program example_block_1 fuel in
    let g := get_ig pi in
    InterfGraph.list g
  .
End Example2.

Module Example3.
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

  Definition fuel : nat := 4.

  Compute
    let '(pi, regs) := (analyze_program example_block_1 10) in
    ProgramInfo.list pi
  .

  Compute
    let '(pi, _) := analyze_program example_block_1 fuel in
    let g := get_ig pi in
    InterfGraph.list g
  .
End Example3.