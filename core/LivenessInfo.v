From Ssara.Core Require Import IR.
From Ssara.Core Require Import Utils.
From Ssara.Core Require Import Dict.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.
From Stdlib Require Import Lists.List.
Import ListNotations.

From Ssara.Core Require Import IRVregModule.
Import IRVreg.

(*
  https://en.wikipedia.org/wiki/Live-variable_analysis
  https://pfalcon.github.io/ssabook/latest/book-full.pdf#section.531
*)

(* Definition of metadata types *)
Inductive instinfo : Type :=
  | InstInfo (live_out: set reg) (live_in: set reg)
.

Definition merge_instinfo (ii : instinfo) (ii' : instinfo) : instinfo :=
  match ii, ii' with
  | InstInfo lout lin, InstInfo lout' lin' =>
    InstInfo (regs_union lout lout') (regs_union lin lin')
  end
.

Fixpoint merge_instinfos (iis : list instinfo) (iis' : list instinfo) : list instinfo :=
  match iis, iis' with
  | nil, nil => nil
  | L, nil => L
  | nil, L => L
  | ii :: xs, ii' :: ys => (merge_instinfo ii ii') :: merge_instinfos xs ys
  end
.

Inductive blockinfo : Type :=
  | BlockInfo (iis : list instinfo)
.

Module ProgramInfoParams <: DICT_PARAMS.
  Definition key := lbl.
  Definition value := option blockinfo.
  Definition default : value:= None.
  Definition key_eq_dec := Nat.eq_dec.
End ProgramInfoParams.

Module ProgramInfo := MakeDict ProgramInfoParams.

Definition programinfo_insert (pi : ProgramInfo.dict) (l : lbl) (bi : blockinfo) : ProgramInfo.dict :=
  let bi' := ProgramInfo.get pi l in
  match bi, bi' with
  | BlockInfo iis, None => ProgramInfo.update pi l (Some bi)
  | BlockInfo iis, Some (BlockInfo iis') => ProgramInfo.update pi l (Some (BlockInfo (merge_instinfos iis iis')))
  end
.

Definition programinfo_merge (pi : ProgramInfo.dict) (pi' : ProgramInfo.dict) : ProgramInfo.dict :=
  fold_left
    (fun pi_acc l =>
      match ProgramInfo.get pi l with
      | Some bi => programinfo_insert pi_acc l bi
      | None => pi_acc
      end
    )
    (ProgramInfo.keys pi)
    pi'
.

Definition phi_defs (ps : list phi) : set reg :=
  map phi_reg ps
.

Definition phi_uses (b : block) : set reg :=
  let ps := flat_map get_phis (successors b) in               (* Get all phis from successors *)
  let args := flat_map phi_args ps in                         (* Get all arguments of phis *)
  let pairs := filter (fun '(_, l) => l =? get_lbl b) args in (* Keep only those that come from the current label *)
  map fst pairs                                               (* Get only the registers *)
.

(*
  Liveness analysis of a phi instruction section:
  - live_out[ps]  := U with j ∈ succ[ps] of live_in[j]
  - live_in[ps]   := phi_defs[ps] U live_out[ps]

  Returns the instinfo of all the phi instructions (which by SSA semantics are
  all executed at the same time hence they are considered as a single
  instruction) and live_in[ps].
  Note that the live_in contains phi_defs[ps] because phi instructions are
  actually executed in the predecessor blocks, not in the block where they are
  defined.
*)
Definition analyze_phis (ps : list phi) (final_live_out : set reg) : instinfo * set reg :=
  let live_in := regs_union (phi_defs ps) final_live_out in
  (InstInfo final_live_out live_in, live_in)
.

(*
  Liveness analysis of a regular instruction:
  - live_out[i] := U with j ∈ succ[i] of live_in[j]
  - live_in[i]  := use[i] U (live_out[i] \ def[i])

  Returns the list of instinfos and the live_in of the first instruction.
*)
Fixpoint analyze_insts (is : list inst) (final_live_out : set reg) : list instinfo * set reg :=
  match is with
  | nil => (nil, final_live_out)
  | x :: xs =>
    let use := inst_args x in
    let def := inst_reg x in
    let (is, live_out) := analyze_insts xs final_live_out in
    let live_in := regs_union use (regs_diff live_out def) in (
      (InstInfo live_out live_in) :: is,
      live_in
    )
  end
.

(*
  Liveness analysis of a jump instruction:
  - live_out[i] := U with j ∈ succ[i] of live_in[j]
  - live_in[i]  := use[i] U live_out[i]

  Returns the list of instinfos and the live_in of the instruction.
*)
Definition analyze_jinst (j : jinst) (final_live_out : set reg) : instinfo * set reg :=
  let live_in := regs_union (jinst_args j) final_live_out in
  (InstInfo final_live_out live_in, live_in)
.

(*
  Liveness analysis of a block:
  - live_out[b] := phi_uses[b] U (U with s in succ[b] of (live_in[s] - phi_def[s]))
  - live_in[b]  := live_in[ps]

  Returns the list of instinfos and (live_in[b] - phi_def[s]) which will later
  be used in `analyze_program` to calculate the live_out of the predecessor with
  the first equation defined in this comment.
*)
Definition analyze_block (b : block) (final_live_out : set reg) : list instinfo * set reg :=
  match b with
  | Block l ps is j =>
    let (iis_3, live_in_3) := analyze_jinst j final_live_out in
    let (iis_2, live_in_2) := analyze_insts is live_in_3 in
    let (iis_1, live_in_1) := analyze_phis ps live_in_2 in
    (iis_1 :: iis_2 ++ [iis_3], regs_diff live_in_1 (phi_defs (get_phis b)))
  end
.

(*
  Returns the programinfo with depth `fuel` and live_in[p] which can be used to
  check whether the program uses any uninitialized variable.
*)
Fixpoint analyze_program (p : program) (fuel : nat) : ProgramInfo.dict * set reg :=
  match fuel with
  | O =>
    (* Get last blockinfo *)
    let (iis, live_in) := analyze_block p nil in
    (programinfo_insert ProgramInfo.empty (get_lbl p) (BlockInfo iis), live_in)

  | S fuel' =>
    (* Get successors *)
    let bs := successors p in

    (* Analyze successors *)
    let results := map (fun p => analyze_program p fuel') bs in

    (* Create pi, map containing successors blockinfo and live_out, union of live_in of successors *)
    let (pi, live_out) :=
      fold_left
        (fun '(pi_acc, live_out) '(pi_succ, live_in) =>
          (programinfo_merge pi_acc pi_succ, regs_union live_out live_in))
        results
        (ProgramInfo.empty, nil)
    in

    (* Add phi_uses[b] to live_out *)
    let live_out := regs_union live_out (phi_uses p) in

    (* Analyze current block *)
    let (iis, live_in) := analyze_block p live_out in

    (* Insert data into map *)
    let pi := programinfo_insert pi (get_lbl p) (BlockInfo iis) in

    (pi, regs_diff live_in (phi_defs (get_phis p)))
  end
.

(*
         +---------------+
         | r0 <- 34      |
         | r1 <- 35      |
         | r2 <- r1 < r2 |
         +---------------+
              |    |
         +----+    +-----+
         |               |
  +-------------+  +-------------+
  | r2 <- Φ(r0) |  | r3 <- Φ(r1) |
  +-------------+  +-------------+
*)

From Ssara.Core Require Import IR.

Module Example1.
  Definition example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(0, 1)]
    ] [
      r(4) <- (Ptr 0);
      store r(4) r(3)
    ] (
      ret r(4)
    )
  .

  Definition example_block_3 : block :=
    Block 3 [
      r(5) <- phi [(1, 1)]
    ] [
      r(6) <- (Ptr 0);
      store r(6) r(5)
    ] (
      ret r(6)
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

  Compute
    let '(pi, regs) := (analyze_program example_block_1 10) in
    ProgramInfo.listify pi
  .
End Example1.

(*
        +--------+
        |        |
  +-----------+  |
  | r0 <- 100 |  |
  +-----------+  |
        |        |
  +----------+   |
  | r1 <- r0 |   |
  +----------+   |
        |        |
        +--------+
*)
Module Example2.
  CoFixpoint example_block_1 : block :=
    Block 1 [
    ] [
      r(0) <- (Imm 100)
    ] (
      Jump example_block_2
    )
  with example_block_2 : block :=
    Block 2 [
    ] [
      r(1) <- (Reg 0)
    ] (
      Jump example_block_1
    )
  .

  Compute
    let (pi, _) := analyze_program example_block_1 10 in
    ProgramInfo.listify pi
  .
End Example2.

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
    ProgramInfo.listify pi
  .
End Example3.
