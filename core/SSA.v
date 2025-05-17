From Ssara.Core Require Import Syntax.
From Stdlib Require Import Lists.List.

(*
  1st property of an SSA program, every instruction is assigned exactly once
*)

Inductive in_program : block -> program -> Prop :=
  | IsProgram : forall b, in_program b b
  | IsSuccessor : forall b b' p, (In b' (successors b)) -> in_program b p -> in_program b' p
.

Fixpoint nth_ok {A : Type} (i : nat) (l : list A) : bool :=
  match i, l with
    | O, x :: _ => true
    | O, nil => false
    | S i', nil => false
    | S i', _ :: t => nth_ok i' t
  end.

Definition single_assignment_sec {A : Type} (get_sec : block -> list A) (get_reg : A -> option reg) (b : block) : Prop :=
  forall (i j : nat),
    match nth_error (get_sec b) i, nth_error (get_sec b) j with
    | Some i1, Some i2 => get_reg i1 = get_reg i2 -> i = j
    | _, _ => True
    end
.

Definition single_assignment_program_phi_inst (b : block) : Prop :=
  forall (i j : nat),
    match nth_error (get_phis b) i, nth_error (get_insts b) j with
    | Some i1, Some i2 => Some (phi_reg i1) <> inst_reg i2
    | _, _ => True
    end
.

Definition single_assignment_block (b : block) : Prop :=
  single_assignment_sec get_phis (fun p => Some (phi_reg p)) b /\
  single_assignment_sec get_insts inst_reg b /\
  single_assignment_program_phi_inst b
.

Definition single_assignment_program (p : program) : Prop :=
  forall (b : block), in_program b p -> single_assignment_block b
.

(*
  We make the assumption that a program in SSA form only allows phi
  instructions that have arguments that are registers defined in the immediate
  predecessors of the current block and there is an argument for each immediate
  predecessor, which is what we enforce with this predicate.
*)
Definition predecessor (b b' : block) : Prop :=
  In b' (successors b)
.

Definition well_formed_phis_block (b : block) : Prop :=
  forall (p : phi) (arg : phi_arg),
    In p (get_phis b) -> In arg (phi_args p) ->
      exists (pred : block),
        predecessor pred b /\
        match arg with
        | (r, l) => get_lbl pred = l
        end
.

Definition well_formed_phis_program (p : program) : Prop :=
  forall (b : block), in_program b p -> well_formed_phis_block b
.

(* (*
  2nd property of an SSA program is strictness, that means that an instruction
  must be used only after its first assignment, to enforce this we must first
  define the dominance relation as the set of couple of instructions (i, i')
  such that for every path from the start to i' there is a definition of i.
  Since there cannot exist two instructions that share the same virtual
  register in our representation we only need to check recursively on the
  predecessors of the basic block where i' is situated for the existance of i.
*)
Fixpoint is_path_of (path : list block) (p : program) : Prop :=
  match path with
  | nil => True
  | x :: nil =>
    in_program x p
  | x :: (y :: ys) as L =>
    in_program  x p
    /\ In y (successors x)
    /\ is_path_of L p
  end
.

(* Definition is_path_from_start (path : list block) (p : program) : Prop :=
  match path, p with
  | b :: _, p => b = b'
  | _, _ => False
  end
. *)

Fixpoint comes_before_in (b b' : block) (path : list block) : Prop :=
  match path with
  | nil => False
  | x :: nil => x = b /\ b = b'
  | x :: xs =>
    (x = b /\ b = b')
    \/ (x = b /\ In b' xs)
    \/ comes_before_in b b' xs
  end
.

Definition dominates_block_block (b b' : block) (p : program) : Prop :=
  forall (path : list block), (
    is_path_of path p /\ b = p /\ hd_error path = Some b /\ last path b = b' -> (
      forall (x : block), In x path -> (
        comes_before_in b b' path
      )
    )
  )
.

Definition dominates_A_A {A : Type} (i : A) (i' : A) (get_sec : block -> list A) (p : program) : Prop :=
  exists (b : block), (in_program b p) /\ exists i1 i2, (
    i1 < i2
    /\ nth_error (get_sec b) i1 = Some i
    /\ nth_error (get_sec b) i2 = Some i'
  )
  \/
  exists (b b' : block), (
    dominates_block_block b b' p
    /\ In i (get_sec b)
    /\ In i' (get_sec b')
  )
.

Definition dominates_A_B {A : Type} {B : Type} (i : A) (i' : B) (get_A_sec : block -> list A) (get_B_sec : block -> list B) (p : program) : Prop :=
  exists (b : block), (
    in_program b p /\ In i (get_A_sec b) /\ In i' (get_B_sec b)
  )
  \/
  exists (b b' : block), (
    dominates_block_block b b' p
    /\ In i (get_A_sec b)
    /\ In i' (get_B_sec b)
  )
.

Definition dominates_A_jinst {A : Type} (i : A) (j : jinst) (get_A_sec : block -> list A) (p : program) : Prop :=
  exists (b : block), (
    in_program b p /\ In i (get_A_sec b) /\ j = (jinsts b)
  )
  \/
  exists (b b' : block), (
    dominates_block_block b b' p
    /\ In i (get_A_sec b)
    /\ j = (jinsts b')
  )
.

(* Strictness: every variable usage is dominated by its assignment *)
Definition strict (p : program) : Prop :=
  forall (b : block), in_program b p -> (
    forall (i' : inst), In i' (insts b) -> (
      forall (r : reg), In r (inst_args i') -> (
        (exists (ph : phi), (phi_reg ph) = r /\ dominates_A_B ph i' phis insts p) \/
        (exists (i : inst), (inst_reg i) = Some r /\ dominates_A_A i i' insts p)
      )
    )
    /\
    match b with
    | Block _ _ j => forall (r : reg), jinst_args j = Some r -> (
        (exists (ph : phi), (phi_reg ph) = r /\ dominates_A_jinst ph j phis p) \/
        (exists (i : inst), (inst_reg i) = Some r /\ dominates_A_jinst i j insts p)
      )
    end
  )
. *)