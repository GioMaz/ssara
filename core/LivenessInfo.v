From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Vm.
From Ssara.Core Require Import Utils.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.
Import ListNotations.

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

Definition programinfo : Type := set lbl * (lbl -> option blockinfo).
Definition programinfo_empty : programinfo := (nil, fun _ => None).
Definition programinfo_update (pi : programinfo) (l : lbl) (bi : blockinfo) : programinfo :=
  let (ls, map) := pi in
  (ls_add l ls, fun l' => if l =? l' then Some bi else map l')
.
Definition programinfo_map (pi : programinfo) (l : lbl) : (option blockinfo)  :=
  let (_, map) := pi in map l
.
Definition programinfo_dom (pi : programinfo) : set lbl :=
  let (dom, _) := pi in dom
.

Definition programinfo_insert (pi : programinfo) (l : lbl) (bi : blockinfo) : programinfo :=
  let bi' := programinfo_map pi l in
  match bi, bi' with
  | BlockInfo iis, None => programinfo_update pi l bi
  | BlockInfo iis, Some (BlockInfo iis') => programinfo_update pi l (BlockInfo (merge_instinfos iis iis'))
  end
.

Definition programinfo_merge (pi : programinfo) (pi' : programinfo) : programinfo :=
  let (ls, map) := pi in
  fold_left
    (fun pi_acc l =>
      match map l with
      | Some bi => programinfo_insert pi_acc l bi
      | None => pi_acc
      end
    )
    ls
    pi'
.

Definition phi_defs (ps : list phi) : set reg :=
  map phi_reg ps
.

Definition phi_uses (b : block) : set reg :=
  let ps := flat_map (fun b => get_phis b) (successors b) in  (* Get all phis from successors *)
  let args := flat_map phi_args ps in                         (* Get all arguments of phis *)
  let pairs := filter (fun '(_, l) => l =? get_lbl b) args in (* Keep only those that come from the current label *)
  map (fun '(r, _) => r) pairs                                (* Get only the registers *)
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
    let def := option_to_list (inst_reg x) in
    let (is', live_out) := analyze_insts xs final_live_out in
    let live_in := regs_union use (regs_diff live_out def) in (
      (InstInfo live_out live_in) :: is',
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
  let live_in := regs_union (option_to_list (jinst_args j)) final_live_out in
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
Fixpoint analyze_program (p : program) (fuel : nat) : programinfo * set reg :=
  match fuel with
  | O =>
    (* Get last blockinfo *)
    let (iis, live_in) := analyze_block p nil in
    (programinfo_insert programinfo_empty (get_lbl p) (BlockInfo iis), live_in)

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
        (programinfo_empty, nil)
    in

    (* Add phi_uses[b] to live_out *)
    let live_out' := regs_union live_out (phi_uses p) in

    (* Analyze current block *)
    let (iis, live_in) := analyze_block p live_out' in

    (* Insert data into map *)
    let pi' := programinfo_insert pi (get_lbl p) (BlockInfo iis) in

    (pi', regs_diff live_in (phi_defs (get_phis p)))
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

Module Example1.
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
      r(1) <- (Imm 35);
      r(2) <- r(0) < (Reg 1)
    ] (
      Jnz 2 example_block_2 example_block_3
    )
  .

  Compute
    let '((ls, map), regs) := (analyze_program example_block_1 10) in
    map 3.
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
      Jmp example_block_2
    )
  with example_block_2 : block :=
    Block 2 [
    ] [
      r(1) <- (Reg 0)
    ] (
      Jmp example_block_1
    )
  .

  Compute
    let (pi, _) := analyze_program example_block_1 10 in
    (programinfo_map pi 1, programinfo_map pi 2)
  .
End Example2.

(*
TODO:
- Get the interference graph
- Maybe visualize the interference graph in OCaml
- Start regalloc
*)
