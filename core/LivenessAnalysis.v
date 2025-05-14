From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Vm.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
Import ListNotations.

(*
  https://en.wikipedia.org/wiki/Live-variable_analysis
*)

Inductive metainst : Type :=
  (* | Metainst (use : list reg) (def : list reg) (live_out: list reg) (live_in: list reg) *)
  | Metainst (live_out: list reg) (live_in: list reg)
.

Inductive metablock : Type :=
  | Metablock (mis : list metainst) (mbs: list metablock)
.

Definition metaprogram : Type := metablock.

Definition contains (x : reg) (xs : list reg) : bool :=
  existsb (fun n => Nat.eqb x n) xs
.

Fixpoint regs_union (regs : list reg) (regs' : list reg) : list reg :=
  match regs' with
  | nil => regs
  | x :: xs =>
    if contains x regs then regs_union regs xs else x :: regs_union regs xs
  end
.

Notation "x 'U' y" :=
  (regs_union x y) (at level 50)
.

Fixpoint regs_remove (r : reg) (regs : list reg) : list reg :=
  match regs with
  | nil => regs
  | x :: xs =>
    if Nat.eqb x r then regs_remove r xs else x :: regs_remove r xs
  end
.

Fixpoint regs_minus (regs : list reg) (regs' : list reg) : list reg :=
  match regs' with
  | nil => regs
  | x :: xs => regs_minus (regs_remove x regs) xs
  end
.

Definition regs_insert (r : reg) (regs : list reg) : list reg :=
  if contains r regs then regs else r :: regs
.

(* TODO: look into ensembles, coq-ext-lib, other libraries that implement sets *)

Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.

Definition phi_defs (ps : list phi) : list reg :=
  map phi_reg ps
.

Definition phi_uses (b : block) : list reg :=
  match b with
  | Block ps _ _ => flat_map phi_args ps
  end
.

Fixpoint inst_defs (is : list inst) : list reg :=
  match is with
  | nil => nil
  | x :: xs =>
    match inst_reg x with
    | Some r => r :: inst_defs xs
    | None => inst_defs xs
    end
  end
.

Definition defs (b : block) : list reg :=
  match b with
  | Block ps is _ => phi_defs ps ++ inst_defs is
  end
.

(*
  This generic function is used to get the metadata of a section of
  instructions, it takes in the generic arguments, the list of instructions and
  the final live_out set which is live_out[final] := U in[j] with j ∈ succ[i].

  The function returns the list of instruction metadata and the live_in[start]
  where start is the first instruction of the list.
*)


(*
  Returns the metainst of all the phi instructions (which by SSA semantics are
  all executed at the same time) and the live_out of the predecessor block.
  Liveness analysis of a phi instruction section:
  - live_out[ps]  := U with j ∈ succ[ps] of live_in[j]
  - live_in[ps]   := phi_defs[ps] U live_out[ps]
*)
Definition analyze_phis (ps : list phi) (final_live_out : list reg) : metainst * list reg :=
  let live_in := (phi_defs ps) U final_live_out in
  (Metainst final_live_out live_in, live_in)
.

(*
  Returns the list of metainsts and the live_out of the predecessor instruction.
  Liveness analysis of a regular instruction:
  - live_out[i] := U with j ∈ succ[i] of live_in[j]
  - live_in[i]  := use[i] U (live_out[i] \ def[i])
*)
Fixpoint analyze_insts (is : list inst) (final_live_out : list reg) : list metainst * list reg :=
  match is with
  | nil => (nil, final_live_out)
  | x :: xs =>
    let use := inst_args x in
    let def := option_to_list (inst_reg x) in
    let (is', live_out) := analyze_insts xs final_live_out in
    let live_in := use U (regs_minus live_out def) in (
      (Metainst live_out live_in) :: is',
      live_in
    )
  end
.

(*
  Returns the list of metainsts and the live_out of the predecessor instruction.
  Liveness analysis of a jump instruction:
  - live_out[i] := U with j ∈ succ[i] of live_in[j]
  - live_in[i]  := use[i] U live_out[i]
*)
Definition analyze_jinst (j : jinst) (final_live_out : list reg) : metainst * list reg :=
  let live_in := option_to_list (jinst_args j) U final_live_out in
  (Metainst final_live_out live_in, live_in)
.

(*
  
  - live_out[b] := U with s in succ[b] of ((live_in[s] - phi_def[s]) U phi_uses[s])
  - live_in[b]  := phi_defs[b] U (live_out[b] - defs[b])
*)
Definition analyze_block (b : block) (final_live_out : list reg) : list metainst * list reg :=
  match b with
  | Block ps is j =>
    let (mi_3, live_in_3) := analyze_jinst j final_live_out in
    let (mi_2, live_in_2) := analyze_insts is live_in_3 in
    let (mi_1, live_in_1) := analyze_phis ps live_in_2 in
    (mi_1 :: mi_2 ++ [mi_3], live_in_1)
  end
.

Fixpoint analyze_program (p : program) (fuel : nat) : metaprogram * list reg :=
  match fuel with
  | O =>
    (* Get last metablock *)
    let (mis, live_in) := analyze_block p nil in
    (Metablock mis nil, live_in)

  | S fuel' =>
    (* Get successors *)
    let bs := successors p in

    (* Analyze successors *)
    let results := map (fun p => analyze_program p fuel') bs in

    (* Create mbs, list of successors and live_out, union of live_in of successors *)
    let (mbs, live_out) :=
      fold_left
        (fun '(mbs, live_in) '(mb, live_out) =>
          (mb :: mbs, live_in U live_out))
        results
        (nil, nil) in

    (* Analyze current block *)
    let (mis, live_in) := analyze_block p live_out in

    (Metablock mis mbs, (regs_minus live_in (phi_defs (phis p))) U phi_uses p)
  end
.






















Module Example1.
  Definition ps: list phi := [
      r(0) <- phi [3; 4; 5];
      r(1) <- phi [6; 7; 8];
      r(2) <- phi [9; 10; 11]
    ]
  .

  Compute analyze_phis ps nil.
End Example1.

Module Example2.
  Definition is : list inst := [
      r(8) <- r(0) + (Imm 1);
      r(9) <- r(1) - (Imm 1)
    ]
  .

  Compute analyze_insts is nil.
End Example2.

Module Example3.
  Definition example_block : block := Block [
      r(0) <- phi [1; 2; 3]
    ] [
      r(4) <- r(0) + (Imm 1)
    ] (
      Halt
    )
  .

  Compute analyze_block example_block nil.
End Example3.

Module Example4.
  Definition example_block : block := Block [
      r(0) <- phi [2; 3; 4];
      r(1) <- phi [5; 6; 7]
    ] [
      r(8) <- r(0) + (Imm 1);
      r(9) <- r(1) - (Imm 1)
    ] (
      Halt
    )
  .

  Compute analyze_block example_block nil.
End Example4.
(* 
Fixpoint defines_As {A : Type} (get_reg : A -> option reg) (is : list A) (r : reg) : bool :=
  match is with
  | nil => false
  | x :: xs =>
    match get_reg x with
    | Some r' => (r =? r') || defines_As get_reg xs r
    | None => defines_As get_reg xs r
    end
  end
.

Definition defines (b : block) (r : reg) : bool :=
  match b with
  | Block ps is j =>
    defines_As phi_reg ps r || defines_As inst_reg is r
  end
. *)

Axiom get_fuel : program -> nat.

Definition filter_defined (regs : list reg) (defined : list reg) : list reg :=
  filter (fun r => contains r defined) regs
.

(* Fixpoint postprocess_mp_aux (mp : metaprogram) (defined : list reg) : metaprogram :=
  match mp with
  | Metablock mis mbs =>
    let (mis', defined') := postprocess_mis mis defined in
    fold_left
      (fun '(fmis, fdefined) mp => ) mis' :: (postprocess_mp_aux mbs defined')
  end
. *)

Module Example5.
  Definition example_block_2 : block :=
    Block [
      r(3) <- phi [0]
    ] [
      store (Ptr 0) r(3)
    ] (
      Halt
    )
  .

  Definition example_block_3 : block :=
    Block [
      r(4) <- phi [1]
    ] [
      store (Ptr 0) r(4)
    ] (
      Halt
    )
  .

  Definition example_block_1 : block :=
    Block [
    ] [
      r(0) <- (Imm 34);
      r(1) <- (Imm 35);
      r(2) <- r(0) < (Reg 1)
    ] (
      Jnz 2 example_block_2 example_block_3
    )
  .

  Compute analyze_program example_block_1 10.
End Example5.

Module Example6.
  CoFixpoint example_block_1 : block :=
    Block [
    ] [
      r(0) <- (Imm 100)
    ] (
      Jmp example_block_2
    )
  with example_block_2 : block :=
    Block [
    ] [
      r(1) <- (Reg 0)
    ] (
      Jmp example_block_1
    )
  .

  Compute analyze_program example_block_1 10.
End Example6.

(* Interference graph stored using adjacence lists *)
Definition ig : Type := list (reg * list reg).

(* Fixpoint ig_insert_edge_aux (r : reg) (r' : reg) (g : ig) : ig :=
  match g with
  | nil => [(r, [r'])]
  | (x, xs) as L :: ys =>
    if r =? x then
      (x, regs_insert r' xs) :: ys
    else
    L :: ig_insert_edge_aux r r' ys
  end
. *)

Definition ig_insert_edge (r : reg) (r' : reg) (g : ig) : ig :=
  let fix ig_insert_edge_aux (r : reg) (r' : reg) (g : ig) : ig :=
    match g with
    | nil => [(r, [r'])]
    | (x, xs) as L :: ys =>
      if r =? x then
        (x, regs_insert r' xs) :: ys
      else
      L :: ig_insert_edge_aux r r' ys
    end in
  let g' := ig_insert_edge_aux r r' g in
  ig_insert_edge_aux r' r g'
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

Definition ig_insert_mi (mi : metainst) (g : ig) : ig :=
  match mi with
  | Metainst live_in live_out =>
    let regs := live_in U live_out in
    ig_insert_regs regs g
  end
.

Fixpoint ig_insert_mis (mis: list metainst) (g : ig) : ig :=
  match mis with
  | nil => g
  | x :: xs =>
    let g' := ig_insert_mi x g in
    ig_insert_mis xs g'
  end
.

Fixpoint get_ig_mb (mb : metablock) (g : ig) : ig :=
  match mb with
  | Metablock mis mbs =>
    let g' := ig_insert_mis mis g in
    fold_left (fun g mb => get_ig_mb mb g) mbs g'
  end
.

Definition get_ig_mp (mp : metaprogram): ig :=
  get_ig_mb mp nil.

(*
  +-----------+
  | r1 <- ... |
  | r2 <- ... |
  +-----------+
        |
        |     +-----------+  TODO: handle this specific case where the live_out
        |     |           |  of the first block is {r2, r6, r1, r5}, when
  +-----------------+     |  instead it should be {r2, r1}. This is caused by
  | r3 <- Φ(r1, r5) |     |  live_in of the second block being {r2, r6, r1, r5}
  | r4 <- Φ(r2, r6) |     |
  +-----------------+     |
         |                |
  +--------------+        |
  | r5 <- r3 + 1 |--------+
  | r6 <- r4 + 1 |
  +--------------+
*)

Module Example7.
  CoFixpoint example_block_3 : block :=
    Block [
    ] [
      r(5) <- r(3) + (Imm 1);
      r(6) <- r(4) + (Imm 1)
    ] (
      Jmp example_block_2
    )
  with example_block_2 : block :=
    Block [
      r(3) <- phi [1; 5];
      r(4) <- phi [2; 6]
    ] [
    ] (
      Jmp example_block_3
    )
  .

  Definition example_block_1 : block :=
    Block [
    ] [
      r(1) <- (Imm 34);
      r(2) <- (Imm 35)
    ] (
      Jmp example_block_2
    )
  .

  Definition fuel : nat := 3.

  Compute analyze_program example_block_1 fuel.

End Example7.

(*
TODO:
- Get the interference graph
- Maybe visualize the interference graph in OCaml
- Start regalloc
*)