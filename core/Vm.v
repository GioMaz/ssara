From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import RegClass.
From Ssara.Core Require Import SSA.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.

(* Virtual machine primitives *)

Definition cell : Type := Z.

Inductive vm : Type :=
  | Vm : (reg -> cell) -> list cell -> vm
.

Definition vm_new : vm := Vm (fun _ => Z0) nil.

Definition get_reg (m : vm) (r : reg) : cell :=
  match m with
  | Vm regs _ => regs r
  end
.

Definition set_reg (m : vm) (r : reg) (c : cell) : vm :=
  match m with
  | Vm regs cells =>
    Vm (fun r' => if r' =? r then c else regs r') cells
  end
.

Definition get_cell (m : vm) (i : nat) : cell :=
  let fix get_cell_aux (cells : list cell) (i : nat) : cell :=
    match cells, i with
    | nil, _ => Z0
    | c :: _, O => c
    | _ :: cs, S i' => get_cell_aux cs i'
    end
  in
  match m with
  | Vm _ cells => get_cell_aux cells i
  end
.

Definition set_cell (m : vm) (i : nat) (c : cell) : vm :=
  let fix set_cell_aux (cells : list cell) (i : nat) (c : cell) : list cell :=
    match cells, i with
    | nil, O => c :: nil
    | nil, S i' => Z0 :: (set_cell_aux nil i' c)
    | _ :: xs, O => c :: xs
    | x :: xs, S i' => x :: (set_cell_aux xs i' c)
    end
  in
  match m with
  | Vm regs cells => Vm regs (set_cell_aux cells i c)
  end
.

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

Definition run_insts (m : vm) (is : list inst) : vm :=
  fold_left (fun m_acc i => run_inst m_acc i) is m
.

(* Phi semantics *)

Fixpoint run_phi (m : vm) (pred : block) (r : reg) (rs : list (reg * lbl)) : vm :=
  match rs with
  | nil => m
  | (r', l) :: xs =>
    if l =? get_lbl pred then
      set_reg m r (get_reg m r')
    else
      run_phi m pred r xs
  end
.

Definition run_phis (m : vm) (pred : block) (ps : list phi) : vm :=
  fold_left
    (fun m_acc p =>
      match p with
      | Phi r rs => run_phi m pred r rs
      end) ps m
.

(*
  Since the entry block has no predecessors the order of evaluation of
  instruction between two blocks b and b' is (instructions of b) (jump
  instruction of b) (phi instructions of b')
*)
Fixpoint run (m : vm) (p : program) (fuel : nat) : vm :=
  match p, fuel with
  | _, O => m
  | Block _ _ is j, S fuel' =>
    let m' := run_insts m is in
    match j with
    | Jnz r b1 b2 =>
      if Z.eqb (get_reg m' r) 0 then
        run (run_phis m' p (get_phis b1)) b1 fuel'
      else
        run (run_phis m' p (get_phis b2)) b2 fuel'
    | Jmp b1 => run (run_phis m' p (get_phis b1)) b1 fuel'
    | Halt => m'
    end
  end
.
