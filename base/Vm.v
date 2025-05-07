Require Import Ssara.Base.Syntax.
Require Import Ssara.Base.SSA.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.

(* Virtual machine primitives *)

Definition cell : Type := Z.

Inductive vm : Type :=
  | Vm : list (reg * cell) -> list cell -> vm
.

Fixpoint get_reg_aux (regs : list (reg * cell)) (r : reg) : cell :=
  match regs with
  | nil => Z0
  | (r', c) :: rs => if r =? r' then c else get_reg_aux rs r
  end
.

Definition get_reg (m : vm) (r : reg) : cell :=
  match m with
  | Vm regs _ => get_reg_aux regs r
  end
.

Fixpoint set_reg_aux (regs : list (reg * cell)) (r : reg) (c : cell) : list (reg * cell) :=
  match regs with
  | nil => (r, c) :: nil
  | (r', c') :: rs => if r =? r' then (r, c) :: rs else (r', c') :: (set_reg_aux rs r c)
  end
.

Definition set_reg (m : vm) (r : reg) (c : cell) : vm :=
  match m with
  | Vm regs cells => Vm (set_reg_aux regs r c) cells
  end
.

From QuickChick Require Import QuickChick.
From Stdlib Require Import Bool.

Definition set_reg_P (r : reg) (c : Z) : bool :=
  let (regs, _) := (set_reg (Vm nil nil) r c) in
  existsb (fun '(r', c') => Nat.eqb r r' && Z.eqb c c') regs
.

QuickChick set_reg_P.

Fixpoint get_cell_aux (cells : list cell) (i : nat) : cell :=
  match cells, i with
  | nil, _ => Z0
  | c :: _, O => c
  | _ :: cs, S i' => get_cell_aux cs i'
  end
.

Definition get_cell (m : vm) (i : nat) : cell :=
  match m with
  | Vm _ cells => get_cell_aux cells i
  end
.

Fixpoint set_cell_aux (cells : list cell) (i : nat) (c : cell) : list cell :=
  match cells, i with
  | nil, O => c :: nil
  | nil, S i' => Z0 :: (set_cell_aux nil i' c)
  | _ :: xs, O => c :: xs
  | x :: xs, S i' => x :: (set_cell_aux xs i' c)
  end
.

Definition set_cell (m : vm) (i : nat) (c : cell) : vm :=
  match m with
  | Vm regs cells => Vm regs (set_cell_aux cells i c)
  end
.

Definition set_cell_P (i : nat) (c : cell) : bool :=
  let (_, cells) := (set_cell (Vm nil nil) i c) in
  match nth_error cells i with
  | Some c' => Z.eqb c c'
  | _ => false
  end
.

QuickChick set_reg_P.

(* Inst semantics *)

Definition eval_binop (m : vm) (op : Z -> Z -> Z) (r : reg) (v : val) : cell :=
  match v with
  | Imm i => op (get_reg m r) i
  | Reg r' => op (get_reg m r) (get_reg m r')
  | Ptr p => op (get_reg m r) (get_cell m p)
  end
.

Definition eval_expr (m : vm) (e : expr) : cell :=
  match e with
  | Val v =>
    match v with
    | Imm i => i
    | Reg r => get_reg m r
    | Ptr p => get_cell m p
    end

  | Neg v =>
    match v with
    | Imm i => Z.opp i
    | Reg r => Z.opp (get_reg m r)
    | Ptr p => Z.opp (get_cell m p)
    end

  | Load v => 
    match v with
    | Imm i => get_cell m (Z.to_nat i)
    | Reg r => get_cell m (Z.to_nat (get_reg m r))
    | Ptr p => get_cell m p
    end

  | Syntax.Add r v => eval_binop m Z.add r v
  | Syntax.Sub r v => eval_binop m Z.sub r v
  | Syntax.Mul r v => eval_binop m Z.mul r v
  | Syntax.Div r v => eval_binop m Z.div r v

  | CmpLt r v => eval_binop m (fun a b => if Z.ltb a b then 1 else 0) r v
  | CmpLe r v => eval_binop m (fun a b => if Z.leb a b then 1 else 0) r v
  | CmpGt r v => eval_binop m (fun a b => if Z.gtb a b then 1 else 0) r v
  | CmpGe r v => eval_binop m (fun a b => if Z.geb a b then 1 else 0) r v
  | CmpEq r v => eval_binop m (fun a b => if Z.eqb a b then 1 else 0) r v
  | CmpNe r v => eval_binop m (fun a b => if Z.eqb a b then 0 else 1) r v

  end%Z
.

Definition run_inst (m : vm) (i : inst) : vm :=
  match i with
  | Def r e => set_reg m r (eval_expr m e)
  | Store v r =>
    match v with
    | Imm i' => set_cell m (Z.to_nat i') (get_reg m r)
    | Reg r' => set_cell m (Z.to_nat (get_reg m r')) (get_reg m r)
    | Ptr p => set_cell m p (get_reg m r)
    end
  end
.

Fixpoint run_insts (m : vm) (is : list inst) : vm :=
  match is with
  | nil => m
  | x :: xs => run_insts (run_inst m x) xs
  end
.

(* Phi semantics *)

Definition option_eqb {A : Type} (eqb : A -> A -> bool) (x y : option A) : bool :=
  match x, y with
  | Some a, Some b => eqb a b
  | None, None => true
  | _, _ => false
  end.

Fixpoint defines_aux {A : Type} (get_reg : A -> option reg) (is : list A) (r : reg) : bool :=
  match is with
  | nil => false
  | x :: xs => option_eqb Nat.eqb (get_reg x) (Some r) || defines_aux get_reg xs r
  end
.

Definition defines (b : block) (r : reg) : bool :=
  match b with
  | Block ps is _ =>
    defines_aux phi_reg ps r || defines_aux inst_reg is r
  end
.

Example defines_sound_complete :
  forall (b : block) (r : reg), defines b r = true <-> SSA.defines b r.
Admitted.

Fixpoint run_phi (m : vm) (pred : block) (r : reg) (rs : list reg) : vm :=
  match rs with
  | nil => m
  | x :: xs =>
    if defines pred x then
      set_reg m r (get_reg m x)
    else
      run_phi m pred r xs
  end
.

Fixpoint run_phis (m : vm) (pred : block) (ps : list phi) : vm :=
  match ps with
  | nil => m
  | Phi r rs :: xs => run_phis (run_phi m pred r rs) pred xs
  end
.

(*
Since the entry block has no predecessors the order of evaluation of
instruction between two blocks b and b' is (instructions of b) (jump
instruction of b) (phi instructions of b')
*)
Fixpoint run_aux (m : vm) (b : block) (fuel : nat) : vm :=
  match b, fuel with
  | _, O => m
  | Block _ is j, S fuel'  =>
    let m' := run_insts m is in
    match j with
    | Jnz r b1 b2 =>
      if Z.eqb (get_reg m' r) 0 then
        run_aux (run_phis m' b (phis b1)) b1 fuel'
      else
        run_aux (run_phis m' b (phis b2)) b2 fuel'
    | Jmp b1 => run_aux (run_phis m' b (phis b1)) b1 fuel'
    | Halt => m'
    end
  end
.

Definition run (m : vm) (p : program) (fuel : nat) : vm :=
  match p with
  | nil => m
  | b :: _ => run_aux m b fuel
  end
.

(* Example 1 *)

Definition example_block : block :=
  Block (
    nil
  ) (
    (r(2) <- (Imm 34)) ::
    (r(3) <- r(2) * (Imm 2)) ::
    (r(4) <- r(3) + (Imm 1)) ::
    (store (Ptr 5) r(4)) ::
    (r(5) <- load (Ptr 5)) ::
    (r(6) <- r(4) < (Imm 420)) ::
    nil
  ) (
    Halt
  )
.

Example run_example_1 :
  run_aux (Vm nil nil) example_block 1 =
    Vm ((2, 34%Z) :: (3, 68%Z) :: (4, 69%Z) :: (5, 69%Z) :: (6, 1%Z) :: nil)
    (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 69%Z :: nil)
.
Proof.
  reflexivity.
Qed.

(* Example 2 *)

CoFixpoint example_block_1 :=
  Block nil nil (Jmp example_block_2)
with example_block_2 :=
  Block nil nil (Jmp (example_block_1))
.

Example run_example_2 : run_aux (Vm nil nil) example_block_1 1000 = (Vm nil nil).
Proof.
  reflexivity.
Qed.

(* Example 3 *)

Definition example_block_3 : block :=
  Block (
    (r(2) <- phi (0 :: 1 :: nil)) ::
    nil
  ) (
    (store (Ptr 0) r(2)) ::
    nil
  ) (
    Halt
  )
.

Definition example_block_4 : block :=
  Block (
    nil
  ) (
    (r(0) <- (Imm 34)) ::
    nil
  ) (
    Jmp example_block_3
  )
.

Definition example_block_5 : block :=
  Block (
    nil
  ) (
    (r(1) <- (Imm 35)) ::
    nil
  ) (
    Jmp example_block_3
  )
.

Example run_example_3_1 :
  run (Vm nil nil) (example_block_4 :: example_block_5 :: example_block_3 :: nil) 10
  = Vm ((0, 34%Z) :: (2, 34%Z) :: nil) (34%Z :: nil)
.
Proof.
  reflexivity.
Qed.

Example run_example_3_2 :
  run (Vm nil nil) (example_block_5 :: example_block_4 :: example_block_3 :: nil) 10
  = Vm ((1, 35%Z) :: (2, 35%Z) :: nil) (35%Z :: nil)
.
Proof.
  reflexivity.
Qed.

(* Tests *)

(*
Check whether after a store the ith cell actually contains the intended value
*)
Definition store_P (i : nat) (c : cell) : bool :=
  let m := Vm nil nil in
  let p := (Block nil ((r(0) <- (Imm c)) :: (store (Ptr i) r(0)) :: nil) Halt) :: nil in
  let (_, cells) := run m p 10 in
  match nth_error cells i with
  | Some c' => Z.eqb c c'
  | _ => false
  end
.

QuickChick store_P.

(*
  - Extraction pipeline
  - Look into QuickChick more
  - Look into CoInductives
  - Liveness analysis
*)

(*
Inductive Tree {A : Type} :=
| Leaf : A -> Tree
| Node : A -> Tree -> Tree -> Tree.

Compute liftGen3.

Import QcDefaultNotation. Open Scope qc_scope.


Fail Fixpoint genTree {A} (g : G A) : G Tree :=
  oneOf [liftGen Leaf g; liftGen3 Node g (genTree g) (genTree g)]
.

(*
  The previous fixpoint cannot guess the decreasing argument.
  This would be correct if coq could prove the termination of
  the generation of the tree, we need to use fuel.
*)

Fixpoint genTreeFuel {A} (fuel : nat) (g : G A) : G Tree :=
  match fuel with
  | O => liftGen Leaf g
  | S fuel' => oneOf [
    liftGen Leaf g;
    liftGen3 Node g (genTreeFuel fuel' g) (genTreeFuel fuel' g)
  ]
  end
.
*)
