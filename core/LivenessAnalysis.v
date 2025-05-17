From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Vm.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.
Import ListNotations.

(*
  https://en.wikipedia.org/wiki/Live-variable_analysis
  https://pfalcon.github.io/ssabook/latest/book-full.pdf#section.531
*)

(* Definition of utility functions *)
Definition reg_eq_dec : forall r r' : reg, {r = r'} + {r <> r'} := Nat.eq_dec.
Definition regs_union := set_union reg_eq_dec.
Definition regs_diff := set_diff reg_eq_dec.
Definition regs_add := set_add reg_eq_dec.

Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.

(* Definition of metadata types *)
Inductive instinfo : Type :=
  | InstInfo (live_out: set reg) (live_in: set reg)
.

Inductive blockinfo : Type :=
  | BlockInfo (iis : list instinfo) (bis: list blockinfo)
.

Definition programinfo : Type := blockinfo.

Definition phi_defs (ps : list phi) : set reg :=
  map phi_reg ps
.

Definition phi_uses (b : block) : set reg :=
  let ps := flat_map (fun b => get_phis b) (successors b) in  (* Get all phis from successors *)
  let args := flat_map phi_args ps in                         (* Get all arguments of phis *)
  let pairs := filter (fun '(_, l) => l =? get_lbl b) args in (* Keep only those that come from the current label *)
  map (fun '(r, _) => r) pairs                                (* Get only the register *)
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
    (BlockInfo iis nil, live_in)

  | S fuel' =>
    (* Get successors *)
    let bs := successors p in

    (* Analyze successors *)
    let results := map (fun p => analyze_program p fuel') bs in

    (* Create bis, list of successors and live_out, union of live_in of successors *)
    let (bis, live_out) :=
      fold_left
        (fun '(bis, live_in) '(bi, live_out) =>
          (bi :: bis, regs_union live_in live_out))
        results
        (nil, nil)
    in

    (* Add phi_uses[b] to live_out *)
    let live_out' := regs_union live_out (phi_uses p) in

    (* Analyze current block *)
    let (iis, live_in) := analyze_block p live_out' in

    (BlockInfo iis bis, regs_diff live_in (phi_defs (get_phis p)))
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

  Compute analyze_program example_block_1 10.
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

  Compute analyze_program example_block_1 10.
End Example2.

(* Interference graph definition as a map from a register to its adjacence set *)
Definition ig : Type := reg -> set reg.
Definition ig_epity : ig := fun k => nil.
Definition ig_update (g : ig) (k : reg) (v : set reg) : ig :=
  fun r => if r =? k then v else g r
.

Definition ig_insert_edge (r : reg) (r' : reg) (g : ig) : ig :=
  let regs  := g r in
  let g'    := ig_update g r (regs_add r' regs) in
  let regs' := g' r' in
  ig_update g' r' (regs_add r regs')
.

Fixpoint ig_insert_edges (r : reg) (regs : list reg) (g : ig) : ig :=
  match regs with
  | nil => g
  | x :: xs =>
    let g' := ig_insert_edge r x g in
    ig_insert_edges r xs g'
  end
.

Fixpoint ig_insert_regs (regs : list reg) (g : ig) : ig :=
  match regs with
  | nil => g
  | x :: xs =>
    let g' := ig_insert_edges x xs g in
    ig_insert_regs xs g'
  end
.

Definition ig_insert_instinfo (ii : instinfo) (g : ig) : ig :=
  match ii with
  | InstInfo live_in live_out =>
    ig_insert_regs live_out (ig_insert_regs live_in g)
  end
.

Definition ig_insert_instinfos (iis: list instinfo) (g : ig) : ig :=
  fold_left (fun g' ii => ig_insert_instinfo ii g') iis g
.

Fixpoint get_ig_blockinfo (bi : blockinfo) (g : ig) : ig :=
  match bi with
  | BlockInfo iis bis =>
    let g' := ig_insert_instinfos iis g in
    fold_left (fun g bi => get_ig_blockinfo bi g) bis g'
  end
.

Definition get_ig_programinfo (pi : programinfo): ig :=
  get_ig_blockinfo pi ig_epity
.

Definition get_regs_instinfos (iis : list instinfo) : set reg :=
  fold_left
    (fun regs ii =>
      match ii with
      | InstInfo live_out live_in =>
        regs_union regs (regs_union live_out live_in)
      end
    )
    iis
    nil
.

Fixpoint get_regs_programinfo (pi : programinfo) : set reg :=
  match pi with
  | BlockInfo iis bis =>
    let curr_regs := get_regs_instinfos iis in
    let succ_regs :=
      fold_left
        (fun regs bi =>
          regs_union regs (get_regs_programinfo bi)
        )
        bis
        nil
    in
    regs_union curr_regs succ_regs
  end
.

Definition get_ig (p : program) (fuel : nat) : ig * set reg :=
  let (pi, _) := analyze_program p fuel in
  let g := get_ig_programinfo pi in
  let regs := get_regs_programinfo pi in
  (g, regs)
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

  Compute analyze_program example_block_1 fuel.
  Compute
    let (pi, _) := analyze_program example_block_1 fuel in
    let g := get_ig_programinfo pi in
    map (fun r => (r, g r)) [1; 2; 3; 4; 5; 6].
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

  Compute analyze_program example_block_4 fuel.
  Compute
    let (pi, _) := analyze_program example_block_1 fuel in
    let g := get_ig_programinfo pi in
    map (fun r => (r, g r)) (get_regs_programinfo pi)
  .
End Example4.

(*
TODO:
- Get the interference graph
- Maybe visualize the interference graph in OCaml
- Start regalloc
*)