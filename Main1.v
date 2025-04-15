Require Import ZArith.
Require Import Coq.Lists.List.

Definition reg := nat.
Definition ptr := nat.
Definition lbl := nat.

(*
  This represents a value that can either be an immediate number `x` or the
  value contained in the register `r`
*)
Inductive val : Type :=
  | Imm (x : Z)
  | Reg (r : reg)
  | Ptr (p : ptr)
.

Definition eq_val (v1 v2 : val) : bool :=
  match v1, v2 with
  | Imm x1, Imm x2 => Z.eqb x1 x2
  | Reg x1, Reg x2 => Nat.eqb x1 x2
  | Ptr x1, Ptr x2 => Nat.eqb x1 x2
  | _, _ => false
  end
.

(*
  The first operator of a binary expression is a `reg` because we assume that
  an expression cannot have two constant arguments as the result can be
  calculated in a previous stage of the compilation.
  We avoided differentiating between unary, binary and n-ary expressions to
  avoid having to deal with unnecessary nesting of data types.
*)
Inductive expr : Type :=
  | Val : val -> expr
  | Neg : val -> expr
  | Load : val -> expr
  | Add : reg -> val -> expr
  | Sub : reg -> val -> expr
  | Mul : reg -> val -> expr
  | Div : reg -> val -> expr
  | CmpLt : reg -> val -> expr
  | CmpLe : reg -> val -> expr
  | CmpGt : reg -> val -> expr
  | CmpGe : reg -> val -> expr
  | CmpEq : reg -> val -> expr
  | CmpNe : reg -> val -> expr
.

Definition eq_expr (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Val x1, Val x2 => eq_val x1 x2
  | Neg x1, Neg x2 => eq_val x1 x2
  | Load x1, Load x2 => eq_val x1 x2
  | Add x1 y1, Add x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | Sub x1 y1, Sub x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | Mul x1 y1, Mul x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | Div x1 y1, Div x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | CmpLt x1 y1, CmpLt x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | CmpLe x1 y1, CmpLe x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | CmpGt x1 y1, CmpGt x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | CmpGe x1 y1, CmpGe x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | CmpEq x1 y1, CmpEq x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | CmpNe x1 y1, CmpNe x2 y2 => (Nat.eqb x1 x2) && (eq_val y1 y2)
  | _, _ => false
  end
.

(*
  The `phi`, `inst` and `jinst` instructions are separated to avoid having to
  deal with illegal basic blocks
*)
Inductive phi : Type :=
  | Phi (r : reg) (rs: list reg)
.

Notation "'r(' x ) <- 'phi' y" :=
  (Phi x y) (at level 50).

Definition phi_reg (p : phi) : reg :=
  match p with
  | Phi r _ => r
  end
.

Definition phi_args (p : phi) : list reg :=
  match p with
  | Phi _ rs => rs
  end
.

Fixpoint eq_list_reg (r1 r2 : list reg) : bool :=
  match r1, r2 with
  | nil, nil => true
  | x :: xs, y :: ys => (Nat.eqb x y) && eq_list_reg xs ys
  | _, _ => false
  end
.

Definition eq_phi (p1 p2 : phi) : bool :=
  match (p1, p2) with
  | (Phi r1 rs1, Phi r2 rs2) => (Nat.eqb r1 r2) && (eq_list_reg rs1 rs2)
  end
.

Fixpoint eq_list_phi (p1 p2 : list phi) : bool :=
  match p1, p2 with
  | nil, nil => true
  | x :: xs, y :: ys => (eq_phi x y) && (eq_list_phi xs ys)
  | _, _ => false
  end
.

Inductive inst : Type :=
  | Def (r : reg) (e : expr)
  | Store (v : val) (r : reg)
.

Notation "'r(' x ) <- 'load' y" :=
  (Def x (Load y)) (at level 50).
Notation "'r(' x ) <- y" :=
  (Def x (Val y)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) + z" :=
  (Def x (Add y z)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) - z" :=
  (Def x (Sub y z)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) * z" :=
  (Def x (Mul y z)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) / z" :=
  (Def x (Div y z)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) < z" :=
  (Def x (CmpLt y z)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) <= z" :=
  (Def x (CmpLe y z)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) > z" :=
  (Def x (CmpGt y z)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) >= z" :=
  (Def x (CmpGe y z)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) == z" :=
  (Def x (CmpEq y z)) (at level 50).
Notation "'r(' x ) <- 'r(' y ) != z" :=
  (Def x (CmpNe y z)) (at level 50).
Notation "'store' x 'r(' y )" :=
  (Store x y) (at level 50).

Definition inst_reg (i : inst) : option reg :=
  match i with
  | Def x _ => Some x
  | Store _ _ => None
  end
.

Definition inst_args (i : inst) : list reg :=
  match i with
  | Def x y =>
    match y with
    | Val (Reg r) => r :: nil
    | Neg (Reg r) => r :: nil
    | Load (Reg r) => r :: nil
    | Add r1 (Reg r2) => r1 :: r2 :: nil
    | Sub r1 (Reg r2) => r1 :: r2 :: nil
    | Mul r1 (Reg r2) => r1 :: r2 :: nil
    | Div r1 (Reg r2) => r1 :: r2 :: nil
    | CmpLt r1 (Reg r2) => r1 :: r2 :: nil
    | CmpLe r1 (Reg r2) => r1 :: r2 :: nil 
    | CmpGt r1 (Reg r2) => r1 :: r2 :: nil 
    | CmpGe r1 (Reg r2) => r1 :: r2 :: nil 
    | CmpEq r1 (Reg r2) => r1 :: r2 :: nil 
    | CmpNe r1 (Reg r2) => r1 :: r2 :: nil 
    | _ => nil
    end
  | Store (Reg r1) r2 => r1 :: r2 :: nil
  | _ => nil
  end
.

Definition eq_inst (i1 i2 : inst) : bool :=
  match i1, i2 with
  | Def i1 e1, Def i2 e2 => (Nat.eqb i1 i2) && (eq_expr e1 e2)
  | Store x1 y1, Store x2 y2 => (eq_val x1 x2) && (Nat.eqb y1 y2)
  | _, _ => false
  end
.

Fixpoint eq_list_inst (i1 i2 : list inst) : bool :=
  match i1, i2 with
  | nil, nil => true
  | x :: xs, y :: ys => (eq_inst x y) && (eq_list_inst xs ys)
  | _, _ => false
  end
.

Inductive block : Type :=
  | Block (p : list phi) (i : list inst) (j : jinst)
with jinst : Type :=
  | Jnz (r : reg) (b1 : block) (b2 : block)
  | Jmp (b : block)
  | Halt
.

(*
Definition eq_jinst (j1 j2 : inst) : bool :=
  match j1, j2 with
  | Jnz r b1 b2, Jnz r' b1' b2' => (Nat.eqb r r') && (eq_block b1 b1') && (eq_block b2 b2')
  | Jmp b, Jmp b' => eq_block b b'
  | Halt, Halt => true
  | _, _ => false
  end
.
*)

Definition eq_block (b1 : block) (b2 : block) : bool :=
  match (b1, b2) with
  | (Block p1 i1 j1, Block p2 i2 j2) =>
    (eq_list_phi p1 p2) && (eq_list_inst i1 i2)
  end
.

(*

### Problems:

- `eq_block` does not check for the equality of the jump instruction `jinst`


*)

Definition program : Type := list block
.

(*

### Problems:

- Allows reassigning the same register (TODO: define some propositions that enforce this)
- Allows using unassigned registers (TODO: define some propositions that enforce this)

- Allows duplicate labels (solved by defining block recursivey)
- Allows jumping to unexistent labels (solved by defining block recursivey)

We assume that all labels have a known destination
(there is no linking phase, or the linking already happened)
so we don't need to differentiate between internal jumps (known basic blocks)
and external jumps (unknown basic blocks that will be linked later)

*)

Definition example_block_2 : block :=
  Block (
    nil
  ) (
    nil
  ) (
    Halt
  )
.

Definition example_block_1 : block :=
  Block (
    r(0) <- phi (1 :: 2 :: nil) ::
    r(1) <- phi (1 :: 2 :: nil) ::
    nil
  ) (
    (r(2) <- (Imm 34)) ::
    (r(3) <- r(2) * (Imm 2)) ::
    (r(4) <- r(3) + (Imm 1)) ::
    (store (Ptr 0) r(4)) ::
    (r(5) <- load (Ptr 0)) ::
    (r(6) <- r(4) < (Imm 420)) ::
    nil
  ) (
    Jnz 6 example_block_2 example_block_2
  )
.

Definition program_1 := example_block_1 :: example_block_2 :: nil.

Require Extraction.
Extraction Language OCaml.
Extraction "program.ml" program.

Definition successors (b : block) : list block :=
  let (_, _, j) := b in
  match j with
  | Jnz _ b1 b2 => b1 :: b2 :: nil
  | Jmp b => b :: nil
  | Halt => nil
  end
.

Definition predecessor (b : block) (b' : block) : bool :=
  let (_, _, j) := b in
  match j with
  | Jnz _ b1 b2 => (eq_block b1 b') || (eq_block b2 b')
  | Jmp b1 => eq_block b1 b'
  | Halt => false
  end
.

Fixpoint predecessors (b : block) (p : program) : list block :=
  match p with
  | nil => nil
  | b' :: bs => if predecessor b' b then b :: (predecessors b bs) else (predecessors b bs)
  end
.

Definition dominates_phi (p1 p2 : phi) (ps : list phi) : Prop :=
  exists i j, nth_error ps i = Some p1 /\ nth_error ps j = Some p2 /\ i < j
.

Definition dominates_inst (i1 i2 : inst) (is : list inst) : Prop :=
  exists i j, nth_error is i = Some i1 /\ nth_error is j = Some i2 /\ i < j
.

Definition phi_uses_only_assigned (ps : list phi) : Prop :=
  forall (p : phi), (In p ps) -> (
    forall (r : reg), In r (phi_args p) -> (
      exists (dr : phi), (In dr ps) /\ dominates_phi dr p ps
    )
  )
.

Definition inst_uses_only_assigned (is : list inst) : Prop :=
  forall (i : inst), (In i is) -> (
    forall (r : reg), In r (inst_args i) -> (
      exists (dr : inst), (In dr is) /\ dominates_inst dr i is
    )
  )
.

Definition phi_single_assigment (ps : list phi) : Prop :=
  forall (p : phi), (In p ps) -> (
    ~(exists (p' : phi),
      (In p' ps)
      /\ (phi_reg p) = (phi_reg p')
      /\ (exists (i i' : nat),
        i <> i'
        /\ nth_error ps i = Some p
        /\ nth_error ps i' = Some p'
      )
    )
  )
.

Definition inst_single_assigment (is : list inst) : Prop :=
  forall (i : inst), (In i is) -> (
    ~(exists (i' : inst),
      (In i' is)
      /\ (inst_reg i) = (inst_reg i')
      /\ (exists (j j' : nat),
        j <> j'
        /\ nth_error is j = Some i
        /\ nth_error is j' = Some i'
      )
    )
  )
.

(*
Example succ_example : (successors example_block_1) = (example_block_2 :: example_block_2 :: nil).
Proof. simpl. reflexivity. Qed.
Compute predecessors program_1 example_block_2.

Example pred_example : (predecessors program_1 example_block_2) = (example_block_1 :: nil).
Proof. simpl. reflexivity. Qed.


TODO: Write down propositions (predicates) that enforce that a program is in
SSA form
TODO: Try with assembly instruction instead of definitions and expressions to
avoid unnecessary nesting of data types

*)
