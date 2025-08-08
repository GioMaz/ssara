From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ListSet.
Import ListNotations.
From Stdlib Require Import Sets.Ensembles.

(* Register independent definitions *)
Inductive cond : Type := Jeq | Jne | Jlt | Jle | Jgt | Jge.

(* Register dependent definitions *)
Module Type IR_PARAMS.
  Parameter reg : Set.
  Parameter reg_eqb : reg -> reg -> bool.
  Parameter reg_eq_dec : forall r r' : reg, {r = r'} + {r <> r'}.
End IR_PARAMS.

Module MakeIR (IR: IR_PARAMS).
  Definition reg := IR.reg.
  Definition reg_eqb := IR.reg_eqb.
  Definition reg_eq_dec := IR.reg_eq_dec.

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

  Definition eq_expr (e1 e2 : expr) : bool :=
    match e1, e2 with
    | Val x1, Val x2 => eq_val x1 x2
    | Load x1, Load x2 => eq_val x1 x2
    | Add x1 y1, Add x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
    | Sub x1 y1, Sub x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
    | Mul x1 y1, Mul x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
    | Div x1 y1, Div x2 y2 => (reg_eqb x1 x2) && (eq_val y1 y2)
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

  CoFixpoint block_empty : block := Block O nil nil (Jump block_empty).

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
  Definition regs_union   := set_union  reg_eq_dec.
  Definition regs_inter   := set_inter  reg_eq_dec.
  Definition regs_diff    := set_diff   reg_eq_dec.
  Definition regs_add     := set_add    reg_eq_dec.
  Definition regs_remove  := set_remove reg_eq_dec.
  Definition regs_mem     := set_mem    reg_eq_dec.

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
    (CondJump Jeq x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) = 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump Jeq x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) <> 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump Jne x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) <> 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump Jne x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) < 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump Jlt x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) < 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump Jlt x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) <= 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump Jle x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) <= 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump Jle x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) > 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump Jgt x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) > 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump Jgt x (Imm y) b1 b2) (at level 50).

  Notation "'if' 'r(' x ) >= 'r(' y ) 'then' b1 'else' b2" :=
    (CondJump Jge x (Reg y) b1 b2) (at level 50).
  Notation "'if' 'r(' x ) >= 'i(' y ) 'then' b1 'else' b2" :=
    (CondJump Jge x (Imm y) b1 b2) (at level 50).

  Notation "'ret' 'r(' x )" :=
    (Ret x) (at level 50).

End MakeIR.