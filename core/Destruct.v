From Ssara.Core Require Import IR.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.

From Ssara.Core Require Import IRPregModule.
Import IRPreg.

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

Fixpoint phi_to_move (curr: lbl) (dst : reg) (rs : list phi_arg) : option (reg * reg) :=
  match rs with
  | nil => None
  | (src, l) :: tl =>
    if lbl_eqb l curr
    then Some (src, dst)
    else phi_to_move curr dst tl
  end
.

Fixpoint phis_to_moves (curr : lbl) (ps : list phi) : moves :=
  match ps with
  | nil => nil
  | (Phi r rs) :: tl =>
    match phi_to_move curr r rs with
    | Some m => m :: phis_to_moves curr tl
    | None => phis_to_moves curr tl
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

Definition succ_to_insts (curr : lbl) (succ : block) (fuel : nat) : list inst :=
  let ms := phis_to_moves curr (get_phis succ) in
  let ms := pmove ms fuel in
  moves_to_insts ms
.

Definition ssa_destruct (fuel : nat) (b : block) :=
  let cofix ssa_destruct_aux (curr: lbl) (b : block) : block :=
    match b with
    | Block l ps is j =>
      match j with
      | CondJump c r v b1 b2 =>
        Block l nil is (CondJump c r v
          (Block (Point1 (nat_of_lbl l)) nil (succ_to_insts l b1 fuel) (Jump (ssa_destruct_aux l b1)))
          (Block (Point2 (nat_of_lbl l)) nil (succ_to_insts l b2 fuel) (Jump (ssa_destruct_aux l b2))))
      | Jump b' =>
        Block l nil (is ++ (succ_to_insts l b' fuel)) (Jump (ssa_destruct_aux l b'))
      | Ret r =>
        Block l nil is (Ret r)
      end
    end
  in
  ssa_destruct_aux (get_lbl b) b
.

Module Example1.
  CoFixpoint example_block_2 : block :=
    Block (Normal 2) [
      r(RBP) <- phi [(RSP, Normal 1); (RBP, Normal 4)];
      r(RSP) <- phi [(RSP, Normal 1); (RSP, Normal 4)]
    ] [
    ] (
      Jump example_block_3
    )
  with example_block_3 : block :=
    Block (Normal 3) [
    ] [
      r(RBP) <- r(RBP) + i(1);
      r(RSP) <- r(RSP) + i(1)
    ] (
      Jump example_block_4
    )
  with example_block_4 : block :=
    Block (Normal 4) [
    ] [
    ] (
      Jump example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [
    ] [
      r(RBP) <- i(34);
      r(RSP) <- i(35)
    ] (
      Jump example_block_2
    )
  .

  Definition fuel : nat := 20.

  (* ssa_destruct phis *)
  (* Compute
    let d := ssa_destruct fuel example_block_1 in
    visit_program d fuel
  . *)
End Example1.

Module Example2.
  Definition example_block_2 : block :=
    Block (Normal 2) [
      r(RBP) <- phi [(RBP, Normal 1)]
    ] [
      r(RBX) <- p(0);
      store r(RBX) r(RBP)
    ] (
      ret r(RBX)
    )
  .

  Definition example_block_3 : block :=
    Block (Normal 3) [
      r(RBP) <- phi [(RSP, Normal 1)]
    ] [
      r(RBX) <- p(0);
      store r(RBX) r(RBP)
    ] (
      ret r(RBX)
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [
    ] [
      r(RBP) <- i(34);
      r(RSP) <- i(35)
    ] (
      if r(RBP) < r(RSP) then example_block_2 else example_block_3
    )
  .

  Definition fuel : nat := 20.

  (* ssa_destruct phis *)
  (* Compute
    let d := ssa_destruct fuel example_block_1 in
    visit_program d fuel
  . *)
End Example2.

Module Example3.
  Definition example_block_3 : block :=
    Block (Normal 3) [
    ] [
    ] (
      ret r(RBX)
    )
  .

  CoFixpoint example_block_2 : block :=
    Block (Normal 2) [
      r(RBX) <- phi [(RBX, Normal 1); (RDX, Normal 2)]; (* (a = a) (a = rdx which is the previous b) *)
      r(RDX) <- phi [(RCX, Normal 1); (RBX, Normal 2)]; (* (b = a) (b = rbx which is the previous b + the previous a) *)
      r(RCX) <- phi [(RDX, Normal 1); (RCX, Normal 2)]  (* (i = i) (i = rcx) *)
    ] [
      r(RBX) <- r(RDX) + r(RBX);  (* rbx = b + a *)
      r(RCX) <- r(RCX) - i(1)     (* rcx = i - 1 *)
    ] (
      if r(RCX) = i(1) then example_block_3 else example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block (Normal 1) [
    ] [
      r(RBX) <- i(0);
      r(RCX) <- i(1);
      r(RDX) <- i(10)
    ] (
      Jump example_block_2
    )
  .

  Definition fuel : nat := 20.

  (* ssa_destruct phis *)
  (* Compute
    let d := ssa_destruct fuel example_block_1 in
    visit_program d fuel
  . *)
End Example3.