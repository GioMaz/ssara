From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Vm.
From Stdlib Require Import Lists.List.

Inductive metaphi : Type :=
  | Metaphi (p : phi) (def : option reg) (use : list reg) (live_in: list reg) (live_out: list reg)
.

Inductive metainst : Type :=
  | Metainst (i : inst) (def : option reg) (use : list reg) (live_in: list reg) (live_out: list reg)
.

Inductive metablock : Type :=
  | Metablock (ps : list metaphi) (is : list metainst) (j : jinst)
.

Fixpoint analyze_phis (ps : list phi) (live_in : list reg) (live_out : list reg) : list metaphi :=
  match ps with
  | nil => nil
  | x :: nil => (Metaphi x (phi_reg x) (phi_args x) live_in live_out) :: nil
  | x :: _ => (Metaphi x (phi_reg x) (phi_args x) live_in live_out) :: nil
  end
.

(* 
Fixpoint analyze_block : (b : block) (live_in : list reg) : metablock :=
  match b with
  | nil =>  *)