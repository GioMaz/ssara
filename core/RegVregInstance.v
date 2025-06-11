From Stdlib Require Import PeanoNat.
From Stdlib Require Import ListSet.
From Ssara.Core Require Import RegClass.

Definition vreg : Set := nat.

Instance reg_vreg_instance : RegClass := {|
  reg := vreg;
  reg_eqb := Nat.eqb;
  reg_eq_dec := Nat.eq_dec;
|}.