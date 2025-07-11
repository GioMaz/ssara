From Ssara.Core Require Import IR.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.

From Ssara.Core Require Import IRPregModule.
Import IRPreg.

(* https://xavierleroy.org/publi/parallel-move.pdf *)

(*
  The parallel move type is defined as a list of assignments of type src -> dst
*)
Definition moves : Type := list (reg * reg).

Inductive state : Type :=
  | State (l1 : moves) (l2 : moves) (l3 : moves)
.

Fixpoint split_move (t : moves) (d : reg) : option (reg * moves * moves) :=
  match t with
  | nil => None
  | (src, dst) as P :: tl =>
    if reg_eqb src d
    then Some (dst, nil, tl)
    else
      match split_move tl d with
      | None => None
      | Some (mid, lhs, rhs) => Some (mid, P :: lhs, rhs)
      end
  end
.

Compute split_move [(RAX, RBX); (RBX, RCX); (RSP, RBP); (RSI, RBP)] RSP.

Fixpoint is_last_src (src : reg) (t : moves) : bool :=
  match t with
  | nil => false
  | (src', dst) :: nil => reg_eqb src src'
  | _ :: tl => is_last_src src tl
  end
.

Fixpoint replace_last_src (b : moves) (r : reg) : moves :=
  match b with
  | nil => nil
  | (_, dst) :: nil => (r, dst) :: nil
  | _ :: tl => replace_last_src tl r
  end
.

Definition stepf (s : state) : state :=
  match s with
  | State nil nil _ => s
  | State ((src, dst) :: tl) nil l =>
    if reg_eqb src dst
    then State tl nil l
    else State tl ((src, dst) :: nil) l
  | State t ((src, dst) :: b) l =>
    match split_move t dst with
    | Some (mid, lhs, rhs) =>
      State (lhs ++ rhs) ((dst, mid) :: (src, dst) :: b) l
    | None =>
      match b with
      | nil => State t nil ((src, dst) :: l)
      | _ =>
        if is_last_src dst b
        then State t
          (replace_last_src b tmp)
          ((src, dst) :: (dst, tmp) :: l)
        else State t b ((src, dst) :: l)
      end
    end
  end
.

Fixpoint pmove_aux (s : state) (fuel : nat) : state :=
  match fuel, s with
  | O, _ => s
  | S _, State nil nil _ => s
  | S fuel', _ => pmove_aux (stepf s) fuel'
  end
.

Definition pmove (m : moves) (fuel : nat) : moves :=
  match pmove_aux (State m nil nil) fuel with
  | State _ _ tau => rev tau
  end
.

Fixpoint phi_to_move (pred : lbl) (r : reg) (rs : list phi_arg) : option (reg * reg) :=
  match rs with
  | nil => None
  | (r', l) :: tl =>
    if l =? pred
    then Some (r', r)
    else phi_to_move pred r tl
  end
.

Fixpoint phis_to_moves (pred : lbl) (ps : list phi) : moves :=
  match ps with
  | nil => nil
  | (Phi r rs) :: tl =>
    match phi_to_move pred r rs with
    | Some m => m :: phis_to_moves pred tl
    | None => phis_to_moves pred tl
    end
  end
.

Fixpoint moves_to_insts (ms : moves) : list inst :=
  match ms with
  | nil => nil
  | (src, dst) :: tl => Def dst (Val (Reg src)) :: moves_to_insts tl
  end
.

Compute
  let ms := pmove [(RBX, RDX); (RDX, RBX)] 10 in
  moves_to_insts ms
.

Definition succ_to_insts (pred : lbl) (succ : block) : list inst :=
  let ms := phis_to_moves pred (get_phis succ) in
  moves_to_insts ms
.

Definition ssa_destruct (b : block) :=
  let cofix ssa_destruct_aux (pred : lbl) (b : block) : block :=
    match b with
    | Block l ps is j =>
      Block l nil ((succ_to_insts pred b) ++ is)
      match j with
      | CondJump c r v b1 b2 => CondJump c r v (ssa_destruct_aux l b1) (ssa_destruct_aux l b2)
      | Jump b' => Jump (ssa_destruct_aux l b')
      | Ret r => Ret r
      end
    end
  in
  ssa_destruct_aux (get_lbl b) b
.

Module Example1.
  CoFixpoint example_block_2 : block :=
    Block 2 [
      r(RBP) <- phi [(RSP, 1); (RBP, 4)];
      r(RSP) <- phi [(RSP, 1); (RSP, 4)]
    ] [
    ] (
      Jump example_block_3
    )
  with example_block_3 : block :=
    Block 3 [
    ] [
      r(RBP) <- r(RBP) + (Imm 1);
      r(RSP) <- r(RSP) + (Imm 1)
    ] (
      Jump example_block_4
    )
  with example_block_4 : block :=
    Block 4 [
    ] [
    ] (
      Jump example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(RBP) <- (Imm 34);
      r(RSP) <- (Imm 35)
    ] (
      Jump example_block_2
    )
  .

  Definition fuel : nat := 20.

  (* ssa_destruct phis *)
  Compute
    let d := ssa_destruct example_block_1 in
    visit_program d fuel
  .
End Example1.

Module Example2.
  Definition example_block_2 : block :=
    Block 2 [
      r(RBP) <- phi [(RBP, 1)]
    ] [
      r(RBX) <- Ptr 0;
      store r(RBX) r(RBP)
    ] (
      ret r(RBX)
    )
  .

  Definition example_block_3 : block :=
    Block 3 [
      r(RBP) <- phi [(RSP, 1)]
    ] [
      r(RBX) <- Ptr 0;
      store r(RBX) r(RBP)
    ] (
      ret r(RBX)
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(RBP) <- (Imm 34);
      r(RSP) <- (Imm 35)
    ] (
      if r(RBP) < (Reg RSP) then example_block_2 else example_block_3
    )
  .

  Definition fuel : nat := 20.

  (* ssa_destruct phis *)
  Compute
    let d := ssa_destruct example_block_1 in
    visit_program d fuel
  .
End Example2.
