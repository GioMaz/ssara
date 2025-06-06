From Stdlib Require Import PeanoNat.
From Ssara.Core Require Import RegClass.
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
  | RAX, RAX => true
  | RBX, RBX => true
  | RCX, RCX => true
  | RDX, RDX => true
  | RSI, RSI => true
  | RDI, RDI => true
  | RSP, RSP => true
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

Definition preg_all : list preg :=
  [RAX; RBX; RCX; RDX; RSI; RDI; RSP; RBP]
.

Lemma preg_all_in : forall p, In p preg_all.
Proof.
  intros p. destruct p; simpl; repeat (left; reflexivity) || right; try reflexivity.
Qed.

Instance reg_preg_instance : RegClass := {|
  reg := preg;
  reg_eqb := preg_eqb;
  reg_eq_dec := preg_eq_dec;
|}.