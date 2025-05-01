Require Import Ssara.Syntax.
Require Import Coq.Lists.List.
Require Import ZArith.

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
  | nil => nil
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
  

Inductive run (m : vm) (p : program) (fuel : nat) : vm :=
*)
