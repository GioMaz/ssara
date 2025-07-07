From Stdlib Require Import PeanoNat.
From Stdlib Require Import ListSet.
From Ssara.Core Require Import IR.
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
  | RBP, RBP => true
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
  [RAX; RBX; RCX; RDX; RSI; RDI; RSP; RBP]
.

Lemma preg_all_in : forall p, In p preg_all.
Proof.
  intros []; simpl; repeat (left; reflexivity) || right; try reflexivity.
Qed.

Definition tmp : preg := RAX.
Definition preg_all_minus_tmp := IRPreg.regs_diff preg_all [tmp].
Lemma preg_all_minus_tmp_in : forall p, p <> tmp -> In p preg_all_minus_tmp.
Proof.
  intros []; unfold tmp; intros H;
  try congruence; repeat (left; reflexivity) || right; try reflexivity.
Qed.