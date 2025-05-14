From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Vm.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
Import ListNotations.

(*
  https://en.wikipedia.org/wiki/Live-variable_analysis
*)

Inductive metainst : Type :=
  | Metainst (use : list reg) (def : list reg) (live_out: list reg) (live_in: list reg)
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

(*
  This generic function is used to get the metadata of a section of
  instructions, it takes in the generic arguments, the list of instructions and
  the final live_out set which is live_out[final] := U in[j] with j ∈ succ[i].

  The function returns the list of instruction metadata and the live_in[start]
  where start is the first instruction of the list.
*)

Fixpoint analyze_As
  {A : Type}
  (get_use : A -> list reg)
  (get_def : A -> list reg)
  (is : list A)
  (final_live_out : list reg)
  : list metainst * list reg :=
  match is with
  | nil => (nil, final_live_out)
  | x :: xs =>
    let use := get_use x in
    let def := get_def x in
    let (is', live_out) := analyze_As get_use get_def xs final_live_out in
    let live_in := use U (regs_minus live_out def) in (
      (Metainst use def live_out live_in) :: is',
      live_in
    )
  end
.

(*
  Liveness analysis of a phi instruction
  - use[i]      := {}
  - def[i]      := reg[i]
  - live_out[i] := U with j ∈ succ[i] of live_in[j]
  - live_in[i]  := live_out[i] - def[i]
*)
(* Definition analyze_phis_old (ps : list phi) (final_live_out : list reg) : list metainst * list reg :=
  analyze_As phi_args (fun _ => nil) (fun x => option_to_list (phi_reg x)) ps final_live_out
. *)

Definition analyze_phis (ps : list phi) (final_live_out : list reg) : list metainst * list reg :=
  analyze_As (fun _ => nil) (fun x => option_to_list (phi_reg x)) ps final_live_out
.

(*
  Liveness analysis of a normal instruction
  - use[i]      := args[i]
  - def[i]      := reg[i]
  - live_out[i] := U with j ∈ succ[i] of live_in[j]
  - live_in[i]  := use[i] U (live_out[i] - def[i])
*)
Definition analyze_insts (is : list inst) (final_live_out : list reg) : list metainst * list reg :=
  analyze_As inst_args (fun x => option_to_list (inst_reg x)) is final_live_out
.

(*
  Liveness analysis of a jump instruction
  - use[i]      := args[i]
  - def[i]      := {}
  - live_out[i] := U with j ∈ succ[i] live_in[j]
  - live_in[i]  := use[i] U live_out[i]
*)
Definition analyze_jinst (j : jinst) (final_live_out : list reg) : list metainst * list reg :=
  analyze_As (fun x => option_to_list (jinst_args j)) (fun _ => nil) (j :: nil) final_live_out
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

Definition analyze_block (b : block) (final_live_out : list reg) : list metainst * list reg :=
  match b with
  | Block ps is j =>
    let (m_3, live_in_3) := analyze_jinst j final_live_out in
    let (m_2, live_in_2) := analyze_insts is live_in_3 in
    let (m_1, live_in_1) := (analyze_phis ps live_in_2) in
    (m_1 ++ m_2 ++ m_3, live_in_1)
  end
.

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
.

Axiom get_fuel : program -> nat.

(* Fixpoint analyze_program (p : program) (fuel : nat) : metablock * list reg :=
  match fuel with
  | O =>
    let (mis, live_out) := analyze_block p nil in
    (Metablock mis nil, live_out)
  | S fuel' =>
    let (_, _, j) := p in
    match j with
    | Jnz _ b1 b2 =>
      let (metablock1, live_in1) := analyze_program b1 fuel' in
      let (metablock2, live_in2) := analyze_program b2 fuel' in
      let (metainsts, live_out) := analyze_block p (live_in1 U live_in2) in
      (Metablock metainsts [metablock1; metablock2], live_out)
    | Jmp b1 =>
      let (mb1, live_in1) := analyze_program b1 fuel' in
      let (mis, live_out) := analyze_block p live_in1 in
      (Metablock mis [mb1], live_out)
    | Halt =>
      let (mis, live_out) := analyze_block p nil in
      (Metablock mis nil, live_out)
    end
  end
. *)

(*
  Given list of phis and block return the registers that are both in the block
  and used as arguemnts of the phis.
*)
Definition analyze_block_phis (b : block) (ps : list phi) : list reg :=
  let args := flat_map phi_args ps in
  filter (defines b) args
.

(*
  This is a better version of the previous commented function analyze_program
  that gets the successors of a block using the function `successors` in order
  to handle possible future branch instructions in a general way.

  The function takes in a program and the maximum depth and returns the
  metaprogram with the live_in set of the first block which should be the empty
  set for a well formed SSA program.

  With this function we use the assumption that every phi operation uses only
  registers that are defined in the immediate predecessor blocks.
*)
Fixpoint analyze_program_aux (p : program) (fuel : nat) : metaprogram * list reg :=
  match fuel with
  | O =>
    let (mis_i, live_in_i) := analyze_block p nil in
    (Metablock mis_i nil, live_in_i)

  | S fuel' =>
    (* Get successors *)
    let bs := successors p in

    (* Analyze successors *)
    let results := map (fun p => analyze_program_aux p fuel') bs in

    (* Create mbs, list of successors and live_out, union of live_in of successors *)
    let (mbs, live_out) :=
      fold_left
        (fun '(mbs, live_in) '(mb, live_out) =>
          (mb :: mbs, live_in U live_out))
        results
        (nil, nil) in

    (*
      live_out[i] := U with j ∈ succ[i] of (
        live_in[j] U { r | r is an argument of a phi instruction of j}
      )

      +-----------+
      | IMPORTANT |
      +-----------+
      We make the assumption that the phi instructions arguments can only be
      defined in immediate predecessors this makes our representation of an SSA
      program incomplete.
    *)
    let ps := flat_map phis bs in
    let defined := analyze_block_phis p ps in
    let live_out' := live_out U defined in

    (* Analyze current block *)
    let (mis, live_in) := analyze_block p live_out' in

    (* Create current metablock *)
    (Metablock mis mbs, live_in)
  end
.

Definition analyze_program (p : program) (fuel : nat) : metaprogram :=
  let (mp, _) := analyze_program_aux p fuel in mp
.

Definition filter_defined (regs : list reg) (defined : list reg) : list reg :=
  filter (fun r => contains r defined) regs
.

Fixpoint postprocess_mis (mis : list metainst) (defined : list reg) : list metainst * list reg :=
  match mis with
  | nil => (nil, defined)
  | x :: xs =>
    match x with
    | Metainst use def live_in live_out =>
      let curr := Metainst use def (filter_defined live_in defined) (filter_defined live_out defined) in
      let (next, defined') := postprocess_mis xs (def U defined) in
      (curr :: next, defined')
    end
  end
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
    ] (
      Halt
    )
  .

  Definition example_block_3 : block :=
    Block [
      r(4) <- phi [1]
    ] [
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
  | Metainst use def live_in live_out =>
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
  Compute get_ig_mp (analyze_program example_block_1 fuel).

End Example7.

Module Example8.
  Definition example_block_2 : block :=
    Block [
    ] [
      store (Ptr 0) r(0)
    ] (
      Halt
    )
  .

  Definition example_block_1 : block :=
    Block [
    ] [
      r(0) <- (Imm 34)
    ] (
      Jmp example_block_2
    )
  .

  Definition fuel : nat := 10.

  Compute analyze_program_aux example_block_1 fuel.
  Compute get_ig_mp (analyze_program example_block_1 fuel).

End Example8.

(*
TODO:
- Get the interference graph
- Maybe visualize the interference graph in OCaml
- Start regalloc
*)