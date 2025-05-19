From Stdlib Require Import PeanoNat.
From Ssara.Core Require Import Syntax.

Instance reg_instance : RegClass := {|
  reg := nat;
  reg_eqb := Nat.eqb;
  reg_eq_dec := Nat.eq_dec;
|}.