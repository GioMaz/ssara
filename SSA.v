Require Import Top.Syntax.
Require Import Coq.Lists.List. 

(*
  1st property of an SSA program, every instruction is assigned exactly once
*)
Definition single_assignment_program_inst (p : program) : Prop :=
  forall (b b' : block) (i i' : inst),
    (In b p) /\ (In i (insts b)) /\ (In b' p) /\ (In i' (insts b')) -> (
      (inst_reg i = inst_reg i') -> (
        (b = b')
        /\ (exists i1 i2,
          (nth_error (insts b) i1 = Some i) /\
          (nth_error (insts b) i2 = Some i') /\
          (i1 = i2)
        )
      )
    )
.

Definition single_assignment_program_phi (pr : program) : Prop :=
  forall (b b' : block) (p p' : phi),
    (In b pr) /\ (In p (phis b)) /\ (In b' pr) /\ (In p' (phis b')) -> (
      (phi_reg p = phi_reg p') -> (
        (b = b')
        /\ (exists i1 i2,
          (nth_error (phis b) i1 = Some p) /\
          (nth_error (phis b) i2 = Some p') /\
          (i1 = i2)
        )
      )
    )
.

Definition single_assignment_program_phi_inst (pr : program) : Prop :=
  forall (b b' : block) (p : phi) (i : inst),
    (In b pr) /\ (In p (phis b)) /\ (In b' pr) /\ (In i (insts b')) -> (
      ~ exists (r : reg), ((phi_reg p) = r) /\ ((inst_reg i) = Some r)
    )
.

Definition single_assignment_program (p : program) : Prop :=
  single_assignment_program_inst p
  /\ single_assignment_program_phi p
  /\ single_assignment_program_phi_inst p
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
  (exists (p : phi), (In p (phis b)) /\ (phi_reg p = r)) \/
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
  2nd property of an SSA program, an instruction must be used only after its
  first assignment, to enforce this we must first define the dominance
  relation as the set of couple of instructions (i, i') such that for every
  path from the entry to i' we find i. Since there cannot exist two
  instructions that share the same virtual register in our representation we
  only need to check recursively on the predecessors of the basic block where i
  is situated for the existance of i'.
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

Definition dominates_block (b b' : block) (p : program) : Prop :=
  forall (path : list block), (
    (is_path_of path p) /\ (hd_error path) = Some b /\ (last path b) = b' -> (
      forall (x : block), (In x path) -> (
        comes_before_in b b' path
      )
    )
  )
.

Definition dominates_inst_inst (i i' : inst) (p : program) : Prop :=
  exists (b : block), (In b p) /\ exists i1 i2, (
    (i1 < i2)
    /\ (nth_error (insts b) i1 = Some i)
    /\ (nth_error (insts b) i2 = Some i')
  )
  \/
  exists (b b' : block), (
    (dominates_block b b' p)
    /\ (In i (insts b))
    /\ (In i' (insts b'))
  )
.

Definition dominates_phi_inst (ph : phi) (i : inst) (p : program) : Prop :=
  exists (b : block), (
    (In b p) /\ (In ph (phis b)) /\ (In i (insts b))
  )
  \/
  exists (b b' : block), (
    (dominates_block b b' p)
    /\ (In ph (phis b))
    /\ (In i (insts b'))
  )
.

(* UNUSED FOR NOW *)
(*
Definition dominates_inst_phi (i : inst) (ph : phi) (p : program) : Prop :=
  exists (b b' : block), (
    (dominates_block b b' p)
    /\ (In i (insts b))
    /\ (In ph (phis b'))
  )
.

Definition dominates_phi (ph ph' : phi) (p : program) : Prop :=
  exists (b b' : block), (
    (dominates_block b b' p)
    /\ (In ph (phis b))
    /\ (In ph' (phis b'))
  )
.
*)

Definition dominates_phi_jinst (ph : phi) (j : jinst) (p : program) : Prop :=
  exists (b : block), (
    (In b p) /\ (In ph (phis b)) /\ j = (jinsts b)
  )
  \/
  exists (b b' : block), (
    (dominates_block b b' p)
    /\ (In ph (phis b))
    /\ j = (jinsts b')
  )
.

Definition dominates_inst_jinst (i : inst) (j : jinst) (p : program) : Prop :=
  exists (b : block), (
    (In b p) /\ (In i (insts b)) /\ j = (jinsts b)
  )
  \/
  exists (b b' : block), (
    (dominates_block b b' p)
    /\ (In i (insts b))
    /\ j = (jinsts b')
  )
.

Definition assignment_dominates_usage (p : program) : Prop :=
  forall (b : block), (In b p) -> (
    forall (i : inst), (In i (insts b)) -> (
      forall (r : reg), (In r (inst_args i)) -> (
        (exists (ph : phi), (phi_reg ph) = r /\ dominates_phi_inst ph i p) \/
        (exists (i' : inst), (inst_reg i') = Some r /\ dominates_inst_inst i' i p)
      )
    )
    /\
    match b with
    | Block _ _ j => forall (r : reg), jinst_args j = Some r -> (
        (exists (ph : phi), (phi_reg ph) = r /\ dominates_phi_jinst ph j p) \/
        (exists (i : inst), (inst_reg i) = Some r /\ dominates_inst_jinst i j p)
      )
    end
  )
.
