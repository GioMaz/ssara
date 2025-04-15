Require Import ZArith.
Require Import Coq.Lists.List.

Inductive binop : Type :=
    | BAdd
    | BSub
    | BMul
    | BDiv
    | BLt
    | BLe
    | BGt
    | BGe
    | BEq
    | BNe
.

Inductive unop : Type :=
    | UNeg
    | ULoad
.

Definition var := nat.
Definition ptr := nat.
Definition lbl := nat.

(*
    This represents a value that can either be an immediate number `x` or the
    value contained in the variable `v`
*)
Inductive val : Type :=
    | Imm (x : Z)
    | Var (v : var)
    | Ptr (p : ptr)
.

(*
    A `val` and an `expr` are not the same type due to the fact that this is a
    3AC representation, therefore 2 is the maximum arity for an operator.
    The first operator of a binary expression is a `var` because we assume that
    an expression cannot have two constant arguments as the result can be
    calculated in a previous stage of the compilation.
*)
Inductive expr : Type :=
    | Val (arg1 : val)
    | Bin (b : binop) (arg1 : var) (arg2 : val)
    | Un (u : unop) (arg1 : val)
.

Notation "ImmVal( x )" := (Val Imm x).
Notation "VarVal( x )" := (Val Var x).
Notation "PtrVal( x )" := (Val Ptr x).

Notation "x + y" := (Bin BAdd x y).
Notation "x - y" := (Bin BSub x y).
Notation "x * y" := (Bin BMul x y).
Notation "x / y" := (Bin BDiv x y).
Notation "x < y" := (Bin BLt x y).
Notation "x <= y" := (Bin BLe x y).
Notation "x > y" := (Bin BGt x y).
Notation "x >= y" := (Bin BGe x y).
Notation "x == y" := (Bin BEq x y) (at level 50).
Notation "x != y" := (Bin BNe x y) (at level 50).

Notation "- x" := (Un UNeg x).
Notation "Ld( x )" := (Un ULoad (Ptr x)).

(*
    The `phi`, `inst` and `jinst` instructions are separated to avoid having to
    deal with illegal basic blocks
*)
Inductive phi : Type :=
    | Phi (v : var) (vs : list var)
.

Inductive inst : Type :=
    | Def (v : var) (e : expr)
    | Store (v : var) (p : ptr)
.

Notation "x <- y" := (Def x y)
    (at level 30).
Notation "x -> y" := (Store x y).

Inductive block : Type :=
    | Block (p : list phi) (i : list inst) (j : jinst)
with jinst : Type :=
    | Jnz (v : var) (b1 : block) (b2 : block)
    | Jmp (b : block)
    | Halt
.

Definition program : Type := list block.

(*

### Problems:

- Allows reassigning the same variable (TODO: define some propositions that enforce this)
- Allows using unassigned variables (TODO: define some propositions that enforce this)

- Allows duplicate labels (solved by defining block recursivey)
- Allows jumping to unexistent labels (solved by defining block recursivey)

We assume that all labels have a known destination
(there is no linking phase, or the linking already happened)
so we don't need to differentiate between internal jumps (known basic blocks)
and external jumps (unknown basic blocks that will be linked later)

*)

Definition successors (b : block) : list block :=
    let (_, _, j) := b in
    match j with
    | Jnz _ b1 b2 => b1 :: b2 :: nil
    | Jmp b => b :: nil
    | Halt => nil
    end
.

Definition example_block_1 : block :=
    Block (
        nil
    ) (
        nil
    ) (
        Halt
    )
.

Definition example_block_2 : block :=
    Block (
        nil
    ) (
        (0 <- Val (Imm 34)) ::
        (1 <- (0 * (Imm 2))) ::
        (2 <- (1 + (Imm 1))) ::
        (2 -> 0) ::
        (3 <- Ld(0)) ::
        (4 <- (3 < (Imm 420))) ::
        nil
    ) (
        Jmp example_block_1
    )
.

Example succ_example : (successors example_block_2) = (example_block_1 :: nil).
Proof. simpl. reflexivity. Qed.

(*

TODO: Write down propositions (predicates) that enforce that a program is in
SSA form
TODO: Try with assembly instruction instead of definitions and expressions to
avoid unnecessary nesting of data types

*)
