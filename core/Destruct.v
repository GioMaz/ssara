From Ssara.Core Require Import RegAlloc.
From Ssara.Core Require Import RegClass.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* https://xavierleroy.org/publi/parallel-move.pdf *)

From Ssara.Core Require Import RegPregInstance.
Existing Instance reg_preg_instance.

(*
  The parallel move type is defined as a list of assignments of type src -> dst
*)
Definition pmove : Type := list (reg * reg).

Inductive state : Type :=
  | State (l1 : pmove) (l2 : pmove) (l3 : pmove)
.

Fixpoint split_move (t : pmove) (d : reg) : option (reg * pmove * pmove) :=
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

Fixpoint is_last_source (src : reg) (t : pmove) : bool :=
  match t with
  | nil => false
  | (src', dst) :: nil => reg_eqb src src'
  | _ :: tl => is_last_source src tl
  end
.

Fixpoint replace_last_source (b : pmove) (r : reg) : pmove :=
  match b with
  | nil => nil
  | (_, dst) :: nil => (r, dst) :: nil
  | _ :: tl => replace_last_source tl r
  end
.

Definition stepf (s : state) : state :=
  match s with
  | State nil nil _ => s
  | State ((src, dst) :: tl) nil l =>
    if reg_eq_dec src dst
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
        if is_last_source dst b
        then State t
          (replace_last_source b RSP)
          ((src, dst) :: (dst, RSP) :: l)
        else State t b ((src, dst) :: l)
      end
    end
  end
.

Fixpoint order (s : state) (fuel : nat) : state :=
  match fuel with
  | O => s
  | S fuel' => order s fuel'
  end
.