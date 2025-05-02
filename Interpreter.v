Require Import Ssara.Syntax.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Ssara.SSA.

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
  | (r', c') :: rs => if r =? r' then (r, c)::rs else (r', c') :: (set_reg_aux rs r c)
  end
.

Definition set_reg (m : vm) (r : reg) (c : cell) : vm :=
  match m with
  | Vm regs cells => Vm (set_reg_aux regs r c) cells
  end
.

Fixpoint get_cell_aux (cells : list cell) (i : nat) : cell :=
  match cells with
  | nil => Z0
  | c :: cs => if i =? 0 then c else get_cell_aux cs (i-1)
  end
.

Definition get_cell (m : vm) (i : nat) : cell :=
  match m with
  | Vm _ cells => get_cell_aux cells i
  end
.

Fixpoint set_cell_aux (cells : list cell) (i : nat) (c : cell) : list cell :=
  match cells with
  | nil => List.repeat Z0 (i+1)
  | x :: xs => if i =? 0 then c :: xs else x :: (set_cell_aux xs (i-1) c)
  end
.

Definition set_cell (m : vm) (i : nat) (c : cell) : vm :=
  match m with
  | Vm regs cells => Vm regs (set_cell_aux cells i c)
  end
.

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

  | CmpLt r v => eval_binop m (fun a b => if Z.ltb a b then 1%Z else 0%Z) r v
  | CmpLe r v => eval_binop m (fun a b => if Z.leb a b then 1%Z else 0%Z) r v
  | CmpGt r v => eval_binop m (fun a b => if Z.gtb a b then 1%Z else 0%Z) r v
  | CmpGe r v => eval_binop m (fun a b => if Z.geb a b then 1%Z else 0%Z) r v
  | CmpEq r v => eval_binop m (fun a b => if Z.eqb a b then 1%Z else 0%Z) r v
  | CmpNe r v => eval_binop m (fun a b => if Z.eqb a b then 0%Z else 1%Z) r v

  end
.

(* INST SEMANTICS *)

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

(* PHI SEMANTICS *)

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

Example defines_soundness_completeness :
  forall (b : block) (r : reg), defines b r = true <-> SSA.defines b r.
Admitted.
    

Fixpoint run_phi (m : vm) (pred : block) (r : reg) (rs : list reg) : vm :=
  match rs with
  | nil => m (* UNEXPECTED *)
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

(* BLOCK SEMANTICS *)

(*
Since the entry block has no predecessors the order of evaluation of
instruction between two blocks b and b' is (instructions of b) (jump
instruction of b) (phi instructions of b')
*)
Fixpoint run_aux (m : vm) (b : block) : vm :=
  match b with
  | Block _ is j =>
    let m' := run_insts m is in
    match j with

    | Jnz r b1 b2 =>
      if Z.eqb (get_reg m' r) 0 then
        run_aux (run_phis m' b (phis b1)) b1
      else
        run_aux (run_phis m' b (phis b2)) b2

    | Jmp b1 => run_aux (run_phis m' b (phis b1)) b1

    | Halt => m'

    end
  end
.

Definition run (m : vm) (p : program) : vm :=
  match p with
  | nil => m
  | b :: _ => run_aux m b
  end
.

(* EXAMPLE EXECUTION *)

Definition example_block : block :=
  Block (
    nil
  ) (
    (r(2) <- (Imm 34)) ::
    (r(3) <- r(2) * (Imm 2)) ::
    (r(4) <- r(3) + (Imm 1)) ::
    (store (Ptr 0) r(4)) ::
    (*
    (r(5) <- load (Ptr 0)) ::
    (r(6) <- r(4) < (Imm 420)) ::
    *)
    nil
  ) (
    Halt
  )
.

Definition example_vm : vm :=
  Vm nil nil
.

Compute run example_vm (example_block :: nil).