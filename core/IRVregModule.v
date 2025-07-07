From Stdlib Require Import PeanoNat.
From Stdlib Require Import ListSet.
From Ssara.Core Require Import IR.

Definition vreg : Set := nat.

Module IRVregParams <: IR_PARAMS.
  Definition reg := vreg.
  Definition reg_eqb := Nat.eqb.
  Definition reg_eq_dec := Nat.eq_dec.
End IRVregParams.

Module IRVreg := MakeIR IRVregParams.