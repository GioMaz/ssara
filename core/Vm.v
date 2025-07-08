From Ssara.Core Require Import IR.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.

From Ssara.Core Require Import IRVregModule.
Import IRVreg.

Definition cell : Type := Z.

Inductive vm : Type :=
  | Vm : (reg -> cell) -> list cell -> vm
.

Definition vm_empty : vm := Vm (fun _ => Z0) nil.

(* Virtual machine primitives *)

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
    | Ptr p => Z.of_nat p
    end

  | Neg v =>
    match v with
    | Imm i => Z.opp i
    | Reg r => Z.opp (get_reg m r)
    | Ptr p => Z.opp (Z.of_nat p)
    end

  | Load v => 
    match v with
    | Imm i => get_cell m (Z.to_nat i)
    | Reg r => get_cell m (Z.to_nat (get_reg m r))
    | Ptr p => get_cell m p
    end

  | Add r v => eval_binop m Z.add r v
  | Sub r v => eval_binop m Z.sub r v
  | Mul r v => eval_binop m Z.mul r v
  | Div r v => eval_binop m Z.div r v

  end%Z
.

Definition run_inst (m : vm) (i : inst) : vm :=
  match i with
  | Def r e => set_reg m r (eval_expr m e)
  | Store r r' => set_cell m (Z.to_nat (get_reg m r)) (get_reg m r')
  end
.

Definition run_insts (m : vm) (is : list inst) : vm :=
  fold_left (fun m_acc i => run_inst m_acc i) is m
.

Definition eval_cond (m : vm) (c : cond) (r : reg) (v : val) : bool :=
  let neb x y := negb (Z.eqb x y) in
  let op :=
    match c with
    | Jeq => Z.eqb
    | Jne => neb
    | Jlt => Z.ltb
    | Jle => Z.leb
    | Jgt => Z.gtb
    | Jge => Z.geb
    end
  in
  let x := (get_reg m r) in
  let y :=
    match v with
    | Imm i => i
    | Reg r => (get_reg m r)
    | Ptr p => (get_cell m p)
    end
  in
  op x y
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
    (fun m_acc '(Phi r rs) => run_phi m_acc pred r rs)
    ps m
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
    let m := run_insts m is in
    match j with
    | CondJump c r v b1 b2 =>
      if eval_cond m c r v then
        run (run_phis m p (get_phis b1)) b1 fuel'
      else
        run (run_phis m p (get_phis b2)) b2 fuel'
    | Jump b1 => run (run_phis m p (get_phis b1)) b1 fuel'
    | Halt => m
    end
  end
.