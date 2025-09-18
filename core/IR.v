From Ssara.Core Require Import Utils.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ListSet.
Import ListNotations.
From Stdlib Require Import Sets.Ensembles.

(* Register independent definitions *)
Inductive cond : Type := CondEq | CondNe | CondLt | CondLe | CondGt | CondGe.

Inductive lbl : Type :=
  | Normal : nat -> lbl
  | Point1 : nat -> lbl
  | Point2 : nat -> lbl
.

Definition nat_of_lbl (l : lbl) : nat :=
  match l with
  | Normal l => l
  | Point1 l => l
  | Point2 l => l
  end
.

Definition lbl_eqb (l l': lbl) : bool :=
  match l, l' with
  | Normal l, Normal l' => l =? l'
  | Point1 l, Point1 l' => l =? l'
  | Point2 l, Point2 l' => l =? l'
  | _, _ => false
  end
.

Lemma lbl_eq_dec : forall l l' : lbl, {l = l'} + {l <> l'}.
Proof.
  intros l l'.
  destruct l as [n | n | n], l' as [m | m | m]; try (right; discriminate).
  - destruct (Nat.eq_dec n m) as [Enm | NEnm].
    + left. f_equal. assumption.
    + right. intros H. injection H as H. contradiction.
  - destruct (Nat.eq_dec n m) as [Enm | NEnm].
    + left. f_equal. assumption.
    + right. intros H. injection H as H. contradiction.
  - destruct (Nat.eq_dec n m) as [Enm | NEnm].
    + left. f_equal. assumption.
    + right. intros H. injection H as H. contradiction.
Defined.

(* Register dependent definitions *)
Module Type IR_PARAMS.
  Parameter reg : Set.
  Parameter reg_eq_dec : forall r r' : reg, {r = r'} + {r <> r'}.
End IR_PARAMS.

Module MakeIR (IR: IR_PARAMS).
  Definition reg := IR.reg.
  Definition reg_eq_dec := IR.reg_eq_dec.
  Definition reg_eqb (r r' : reg) : bool :=
    match reg_eq_dec r r' with
    | left _ => true
    | right _ => false
    end.

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

  Definition val_eqb (v1 v2 : val) : bool :=
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
    | Load : val -> expr
    | Add : reg -> val -> expr
    | Sub : reg -> val -> expr
    | Mul : reg -> val -> expr
    | Div : reg -> val -> expr
  .

  Definition expr_eqb (e1 e2 : expr) : bool :=
    match e1, e2 with
    | Val x1, Val x2 => val_eqb x1 x2
    | Load x1, Load x2 => val_eqb x1 x2
    | Add x1 y1, Add x2 y2 => (reg_eqb x1 x2) && (val_eqb y1 y2)
    | Sub x1 y1, Sub x2 y2 => (reg_eqb x1 x2) && (val_eqb y1 y2)
    | Mul x1 y1, Mul x2 y2 => (reg_eqb x1 x2) && (val_eqb y1 y2)
    | Div x1 y1, Div x2 y2 => (reg_eqb x1 x2) && (val_eqb y1 y2)
    | _, _ => false
    end
  .

  Definition phi_arg : Type := (reg * lbl).

  (*
    The `phi`, `inst` and `jinst` instructions are separated to avoid having to
    deal with illegal basic blocks
  *)
  Inductive phi : Type :=
    | Phi : reg -> list phi_arg -> phi
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
    | Store (r : reg) (r' : reg)
  .

  Definition inst_reg (i : inst) : list reg :=
    match i with
    | Def x _ => [x]
    | Store _ _ => []
    end
  .

  Definition reg_or_nil (v : val) : list reg :=
    match v with
    | Reg r => [r]
    | _ => []
    end
  .

  Definition inst_args (i : inst) : list reg :=
    match i with
    | Def x y =>
      match y with
      | Val v => reg_or_nil v
      | Load v => reg_or_nil v
      | Add r v => r :: reg_or_nil v
      | Sub r v => r :: reg_or_nil v
      | Mul r v => r :: reg_or_nil v
      | Div r v => r :: reg_or_nil v
      end
    | Store r r' => r :: r' :: nil
    end
  .

  (*
    A block lbl is necessary in order to define the semantics of phi
    instructions.
    Unlike some SSA intermediate representations, labels here can collide with
    virtual register.
  *)
  CoInductive block : Type :=
    | Block (l : lbl) (ps : list phi) (is : list inst) (j : jinst)

  with jinst : Type :=
    | CondJump : cond -> reg -> val -> block -> block -> jinst
    | Jump : block -> jinst
    | Ret : reg -> jinst
  .

  CoFixpoint block_empty : block := Block (Normal O) nil nil (Jump block_empty).

  Definition jinst_args (j : jinst) : list reg :=
    match j with
    | CondJump _ r v _ _ => r :: reg_or_nil v
    | Jump _ => nil
    | Ret r => r :: nil
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

  (* The starting block is the first block of CFG *)
  Definition program : Type := block.

  Fixpoint visit_program (p : program) (fuel : nat) : block :=
    match p, fuel with
    | _, O => block_empty
    | Block l ps is j, S fuel' =>
      Block l ps is
      match j with
      | CondJump c r v b1 b2 => CondJump c r v (visit_program b1 fuel') (visit_program b2 fuel')
      | Jump b => Jump (visit_program b fuel')
      | Ret r => Ret r
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
    | CondJump _ _ _ b1 b2 => [b1; b2]
    | Jump b => [b]
    | Ret _ => []
    end
  .

  (* Set of registers *)
  Definition RegSet := Ensemble.
  Definition regs_union   := set_union    reg_eq_dec.
  Definition regs_inter   := set_inter    reg_eq_dec.
  Definition regs_diff    := set_diff     reg_eq_dec.
  Definition regs_add     := set_add      reg_eq_dec.
  Definition regs_remove  := set_remove   reg_eq_dec.
  Definition regs_mem     := set_mem      reg_eq_dec.
  Definition regs_of_list := set_of_list  reg_eq_dec.

  Notation "r( x ) <- 'phi' y" :=
    (Phi x y) (at level 50).

  Notation "'r(' x ) <- 'load' 'r(' y )" :=
    (Def x (Load (Reg y))) (at level 50).
  Notation "'r(' x ) <- 'load' 'i(' y )" :=
    (Def x (Load (Imm y))) (at level 50).
  Notation "'r(' x ) <- 'load' 'p(' y )" :=
    (Def x (Load (Ptr y))) (at level 50).

  Notation "'r(' x ) <- 'r(' y )" :=
    (Def x (Val (Reg y))) (at level 50).
  Notation "'r(' x ) <- 'i(' y )" :=
    (Def x (Val (Imm y))) (at level 50).
  Notation "'r(' x ) <- 'p(' y )" :=
    (Def x (Val (Ptr y))) (at level 50).

  Notation "'r(' x ) <- 'r(' y ) + 'r(' z )" :=
    (Def x (Add y (Reg z))) (at level 50).
  Notation "'r(' x ) <- 'r(' y ) + 'i(' z )" :=
    (Def x (Add y (Imm z))) (at level 50).
  Notation "'r(' x ) <- 'r(' y ) + 'p(' z )" :=
    (Def x (Add y (Ptr z))) (at level 50).

  Notation "'r(' x ) <- 'r(' y ) - 'r(' z )" :=
    (Def x (Sub y (Reg z))) (at level 50).
  Notation "'r(' x ) <- 'r(' y ) - 'i(' z )" :=
    (Def x (Sub y (Imm z))) (at level 50).
  Notation "'r(' x ) <- 'r(' y ) - 'p(' z )" :=
    (Def x (Sub y (Ptr z))) (at level 50).

  Notation "'r(' x ) <- 'r(' y ) * 'r(' z )" :=
    (Def x (Mul y (Reg z))) (at level 50).
  Notation "'r(' x ) <- 'r(' y ) * 'i(' z )" :=
    (Def x (Mul y (Imm z))) (at level 50).
  Notation "'r(' x ) <- 'r(' y ) * 'p(' z )" :=
    (Def x (Mul y (Ptr z))) (at level 50).

  Notation "'r(' x ) <- 'r(' y ) / 'r(' z )" :=
    (Def x (Div y (Reg z))) (at level 50).
  Notation "'r(' x ) <- 'r(' y ) / 'i(' z )" :=
    (Def x (Div y (Imm z))) (at level 50).
  Notation "'r(' x ) <- 'r(' y ) / 'p(' z )" :=
    (Def x (Div y (Ptr z))) (at level 50).

  Notation "'store' 'r(' x ) 'r(' y )" :=
    (Store x y) (at level 50).

  Notation "'if' 'r(' x ) = 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump CondEq x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) = 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump CondEq x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) <> 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump CondNe x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) <> 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump CondNe x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) < 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump CondLt x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) < 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump CondLt x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) <= 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump CondLe x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) <= 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump CondLe x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) > 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump CondGt x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) > 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump CondGt x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) >= 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump CondGe x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) >= 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump CondGe x (Imm y) b1 b2) (at level 50).

  Notation "'jump' x" :=
    (Jump x) (at level 50).

  Notation "'ret' 'r(' x )" :=
    (Ret x) (at level 50).

End MakeIR.
