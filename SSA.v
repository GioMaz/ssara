Require Import Ssara.Syntax.
Require Import Coq.Lists.List. 

(*
  1st property of an SSA program, every instruction is assigned exactly once
*)

Definition single_assignment_program_of {A : Type} (get_sec : block -> list A) (get_reg : A -> option reg) (p : program) : Prop :=
  forall (b b' : block) (i i' : A),
    (In b p) /\ (In i (get_sec b)) /\ (In b' p) /\ (In i' (get_sec b')) -> (
      (get_reg i = get_reg i') -> (
        (b = b')
        /\ exists j, (
          nth_error (get_sec b) j = Some i /\ nth_error (get_sec b') j = Some i'
        )
      )
    )
.

Definition single_assignment_program_phi_inst (pr : program) : Prop :=
  forall (b b' : block) (p : phi) (i : inst),
    (In b pr) /\ (In p (phis b)) /\ (In b' pr) /\ (In i (insts b')) -> (
      (phi_reg p) <> (inst_reg i)
    )
.

Definition single_assignment_program (p : program) : Prop :=
  single_assignment_program_of insts inst_reg p /\
  single_assignment_program_of phis phi_reg p /\
  single_assignment_program_phi_inst p
.

(*
  For every block, for every phi instruction, for every predecessor, there
  exist a variable defined in that predecessor that is contained in the
  argument of the phi instruction and that predecessor doesn't define any other
  variable used which is an argument for that phi.
  This can be done since we know that two variables with the same name do not
  exist (i.e. `single_assignment_program` is valid).
*)
Definition defines (b : block) (r : reg) : Prop :=
  (exists (p : phi), (In p (phis b)) /\ (phi_reg p = Some r)) \/
  (exists (i : inst), (In i (insts b)) /\ (inst_reg i = Some r))
.

Definition well_formed_phis (p : program) : Prop :=
  forall (b : block), (In b p) -> (
    forall (ph : phi), (In ph (phis b)) -> (
      forall (pr : block), (predecessor pr b p) -> (
        exists (r : reg), (
          In r (phi_args ph) /\ defines pr r /\
          ~ exists (r' : reg), (
            In r' (phi_args ph) /\ defines pr r' /\ r <> r'
          )
        )
      )
    )
  )
.

(*
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
    (In x p)
  | x :: (y :: ys) as L =>
    (In x p)
    /\ (In y (successors x))
    /\ (is_path_of L p)
  end
.

Definition is_path_from_start (path : list block) (p : program) : Prop :=
  match path, p with
  | b :: _, b' :: _ => b = b'
  | _, _ => False
  end
.

Fixpoint comes_before_in (b b' : block) (path : list block) : Prop :=
  match path with
  | nil => False
  | x :: nil => (x = b) /\ (b = b')
  | x :: xs =>
    ((x = b) /\ (b = b'))
    \/ ((x = b) /\ (In b' xs))
    \/ (comes_before_in b b' xs)
  end
.

Definition dominates_block_block (b b' : block) (p : program) : Prop :=
  forall (path : list block), (
    is_path_of path p /\ is_path_from_start path p /\ hd_error path = Some b /\ last path b = b' -> (
      forall (x : block), (In x path) -> (
        comes_before_in b b' path
      )
    )
  )
.

Definition dominates_A_A {A : Type} (i : A) (i' : A) (get_sec : block -> list A) (p : program) : Prop :=
  exists (b : block), (In b p) /\ exists i1 i2, (
    (i1 < i2)
    /\ (nth_error (get_sec b) i1 = Some i)
    /\ (nth_error (get_sec b) i2 = Some i')
  )
  \/
  exists (b b' : block), (
    (dominates_block_block b b' p)
    /\ (In i (get_sec b))
    /\ (In i' (get_sec b'))
  )
.

Definition dominates_A_B {A : Type} {B : Type} (i : A) (i' : B) (get_A_sec : block -> list A) (get_B_sec : block -> list B) (p : program) : Prop :=
  exists (b : block), (
    In b p /\ In i (get_A_sec b) /\ In i' (get_B_sec b)
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
    In b p /\ In i (get_A_sec b) /\ j = (jinsts b)
  )
  \/
  exists (b b' : block), (
    (dominates_block_block b b' p)
    /\ (In i (get_A_sec b))
    /\ j = (jinsts b')
  )
.

(* Strictness: every variable usage is dominated by its assignment *)
Definition strict (p : program) : Prop :=
  forall (b : block), (In b p) -> (
    forall (i' : inst), (In i' (insts b)) -> (
      forall (r : reg), (In r (inst_args i')) -> (
        (exists (ph : phi), (phi_reg ph) = Some r /\ dominates_A_B ph i' phis insts p) \/
        (exists (i : inst), (inst_reg i) = Some r /\ dominates_A_A i i' insts p)
      )
    )
    /\
    match b with
    | Block _ _ j => forall (r : reg), jinst_args j = Some r -> (
        (exists (ph : phi), (phi_reg ph) = Some r /\ dominates_A_jinst ph j phis p) \/
        (exists (i : inst), (inst_reg i) = Some r /\ dominates_A_jinst i j insts p)
      )
    end
  )
.

(*

- Generics
- QuickChick
- Interpreter and then extraction

*)