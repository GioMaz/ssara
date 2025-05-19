From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Ssara.

Class RegClass := {
  reg : Set;
  reg_eqb : reg -> reg -> bool;
  reg_eq_dec : forall r r' : reg, {r = r'} + {r <> r'};
}.
Context {reg_instance : RegClass}.

Definition lbl := nat.
Definition ptr := nat.

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
  | Reg x1, Reg x2 => reg_eqb x1 x2
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
  | Add x1 y1, Add x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | Sub x1 y1, Sub x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | Mul x1 y1, Mul x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | Div x1 y1, Div x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | CmpLt x1 y1, CmpLt x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | CmpLe x1 y1, CmpLe x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | CmpGt x1 y1, CmpGt x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | CmpGe x1 y1, CmpGe x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | CmpEq x1 y1, CmpEq x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | CmpNe x1 y1, CmpNe x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
  | _, _ => false
  end
.

Definition phi_arg : Type := (reg * lbl).

(*
  The `phi`, `inst` and `jinst` instructions are separated to avoid having to
  deal with illegal basic blocks
*)
Inductive phi : Type :=
  | Phi (r : reg) (rs: list phi_arg)
.

Definition phi_reg (p : phi) : reg :=
  match p with
  | Phi r _ => r
  end
.

Definition phi_args (p : phi) : list phi_arg :=
  match p with
  | Phi _ rs => rs
  end
.

Inductive inst : Type :=
  | Def (r : reg) (e : expr)
  | Store (v : val) (r : reg)
.

Definition inst_reg (i : inst) : option reg :=
  match i with
  | Def x _ => Some x
  | Store _ _ => None
  end
.

Definition inst_args (i : inst) : list reg :=
  let reg_or_nil (v : val) : list reg :=
    match v with
    | Reg r => [r]
    | _ => []
    end
  in
  match i with
  | Def x y =>
    match y with
    | Val v => reg_or_nil v
    | Neg v => reg_or_nil v
    | Load v => reg_or_nil v
    | Add r v => r :: reg_or_nil v
    | Sub r v => r :: reg_or_nil v
    | Mul r v => r :: reg_or_nil v
    | Div r v => r :: reg_or_nil v
    | CmpLt r v => r :: reg_or_nil v
    | CmpLe r v => r :: reg_or_nil v
    | CmpGt r v => r :: reg_or_nil v
    | CmpGe r v => r :: reg_or_nil v
    | CmpEq r v => r :: reg_or_nil v
    | CmpNe r v => r :: reg_or_nil v
    end
  | Store v r => r :: reg_or_nil v
  end
.

(*
  A block lbl is necessary in order to define the semantics of phi
  instructions.
*)
CoInductive block : Type :=
  | Block (l : lbl) (ps : list phi) (is : list inst) (j : jinst)

with jinst : Type :=
  | Jnz (r : reg) (b1 : block) (b2 : block)
  | Jmp (b : block)
  | Halt
.

Definition jinst_args (j : jinst) : option reg :=
  match j with
  | Jnz r _ _ => Some r
  | Jmp _ => None
  | Halt => None
  end
.

Definition get_lbl (b : block) : lbl :=
  let (l, _, _, _) := b in l
.

Definition get_phis (b : block) : list phi :=
  let (_, ps, _, _) := b in ps
.

Definition get_insts (b : block) : list inst :=
  let (_, _, is, _) := b in is
.

Definition get_jinst (b : block) : jinst :=
  let (_, _, _, j) := b in j
.

(*
Fixpoint eq_jinst (j1 j2 : jinst) : bool :=
  match j1, j2 with
  | Jnz r b1 b2, Jnz r' b1' b2' => (Nat.eqb r r') && (eq_block b1 b1') && (eq_block b2 b2')
  | Jmp b, Jmp b' => eq_block b b'
  | Halt, Halt => true
  | _, _ => false
  end

with eq_block (b1 : block) (b2 : block) : bool :=
  match (b1, b2) with
  | (Block ps1 is1 j1, Block ps2 is2 j2) =>
    (eq_list_phi ps1 ps2)
    && (eq_list_inst is1 is2)
    && (eq_jinst j1 j2)
  end
.
*)

(* The starting block is the first block of CFG *)
Definition program : Type := block.

(*
  Block instruction, represents all the possible instructions that could be
  found inside a basic block
*)
Inductive binst : Type :=
  | Bphi (p : phi)
  | Binst (i : inst)
  | Bjinst (j : jinst)
.

Definition start (p : program) : binst :=
  let (_, ps, is, j) := p in
  match ps with
  | p :: _ => Bphi p
  | nil =>
    match is with
    | i :: _ => Binst i
    | nil => Bjinst j
    end
  end
.

(*
  ### Problems:

  - Allows reassigning the same register (enforced by the single_assignment_program predicate)
  - Allows using unassigned registers (enforced by the assignment_dominates_usage predicate)
  - Allows duplicate labels (solved by defining block recursivey)
  - Allows jumping to unexistent labels (solved by defining block recursivey)

  We assume that all labels have a known destination
  (there is no linking phase, or the linking already happened)
  so we don't need to distinguish between internal jumps (known basic blocks)
  and external jumps (unknown basic blocks that will be linked later)
*)

Definition successors (b : block) : list block :=
  match get_jinst b with
  | Jnz _ b1 b2 => [b1; b2]
  | Jmp b => [b]
  | Halt => []
  end
.

(*
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
*)

End Ssara.

Notation "'r(' x ) <- 'phi' y" :=
  (Phi x y) (at level 50).

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