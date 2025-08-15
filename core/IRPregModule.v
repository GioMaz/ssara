From Stdlib Require Import PeanoNat.
From Stdlib Require Import ListSet.
From Ssara.Core Require Import IR.
From Ssara.Core Require Import Utils.
From Stdlib Require Import Lists.List.
Import ListNotations.

Inductive preg : Type :=
  | RAX
  | RBX
  | RCX
  | RDX
  | RSI
  | RDI
  | RSP
  | RBP
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  | UNASSIGNED
.

Definition preg_eqb (p : preg) (p' : preg) : bool :=
  match p, p' with
  | RAX, RAX
  | RBX, RBX
  | RCX, RCX
  | RDX, RDX
  | RSI, RSI
  | RDI, RDI
  | RSP, RSP
  | RBP, RBP
  | R8, R8
  | R9, R9
  | R10, R10
  | R11, R11
  | R12, R12
  | R13, R13
  | R14, R14
  | R15, R15
  | UNASSIGNED, UNASSIGNED => true
  | _, _ => false
  end
.

Lemma preg_eqb_eq : forall p p', preg_eqb p p' = true <-> p = p'.
Proof.
  destruct p, p'; simpl; split; try congruence; intros; reflexivity.
Qed.

Lemma preg_eq_dec : forall p p' : preg, {p = p'} + {p <> p'}.
Proof.
  decide equality.
Defined.

Module IRPregParams <: IR_PARAMS.
  Definition reg := preg.
  Definition reg_eqb := preg_eqb.
  Definition reg_eq_dec := preg_eq_dec.
End IRPregParams.

Module IRPreg := MakeIR(IRPregParams).

Definition preg_all : set preg :=
  [RAX; RBX; RCX; RDX; RSI; RDI; RSP; RBP; R8; R9; R10; R11; R12; R13; R14; R15; UNASSIGNED]
.

Lemma preg_all_in :
  forall p, In p preg_all.
Proof.
  intro p.
  destruct p; simpl; tauto.
Qed.

(* Registers that are forbidden during register assignment *)
Definition unassigned : preg  := UNASSIGNED.
Definition tmp : preg         := RAX.
Definition rsp : preg         := RSP.
Definition rbp : preg         := RBP.
Definition preg_forbidden := [unassigned; tmp; rsp; rbp].

Definition preg_allowed := IRPreg.regs_diff preg_all preg_forbidden.

Lemma preg_allowed_in :
  forall p,
    ~ In p preg_forbidden <-> In p preg_allowed.
Proof.
  split.
  intros H.
  unfold preg_allowed.
  apply set_diff_intro.
  apply preg_all_in.
  assumption.
  intros H.
  apply set_diff_elim2 in H.
  assumption.
Qed.