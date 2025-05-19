From Stdlib Require Import PeanoNat.
From Ssara.Core Require Import Syntax.

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

Lemma preg_eqb_eq : forall r r', preg_eqb r r' = true <-> r = r'.
Proof.
  destruct r, r'; simpl; split; try congruence; intros; reflexivity.
Qed.

Lemma preg_eq_dec : forall r r' : preg, {r = r'} + {r <> r'}.
Proof.
  decide equality.
Qed.

Instance reg_instance : RegClass := {|
  reg := preg;
  reg_eqb := preg_eqb;
  reg_eq_dec := preg_eq_dec;
|}.