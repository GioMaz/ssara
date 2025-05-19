From Ssara.Core Require Import Syntax.
From Ssara.Core Require Import Vm.
From Stdlib Require Import ZArith.
From Stdlib Require Import ListSet.
From Stdlib Require Import Lists.List.

From Ssara.Core Require Import RegNatInstance.
Existing Instance reg_instance.

(* Set of registers *)
Definition reg_eq_dec : forall r r' : reg, {r = r'} + {r <> r'} := reg_eq_dec.
Definition regs_union := set_union reg_eq_dec.
Definition regs_diff := set_diff reg_eq_dec.
Definition regs_add := set_add reg_eq_dec.
Definition regs_remove := set_remove reg_eq_dec.

(* Lemma regs_remove_absence :
  forall (r : reg) (regs : set reg),
    In r regs -> length (regs_remove r regs) < length regs
.
Proof.
  induction regs as [| x xs IH]; simpl; intros Hin.
  - inversion Hin.
  - destruct reg_eq_dec as [Heq | Hneq].
    + subst.
      apply Nat.lt_succ_diag_r.
    + simpl.
      apply -> Nat.succ_lt_mono.
      assert (In r xs) as Hin_t by (destruct Hin; [contradiction | assumption]). *)

Definition regs_mem := set_mem reg_eq_dec.

(* Set of labels *)
Definition l_eq_dec : forall r r' : reg, {r = r'} + {r <> r'} := Nat.eq_dec.
Definition ls_union := set_union l_eq_dec.
Definition ls_diff := set_diff l_eq_dec.
Definition ls_add := set_add l_eq_dec.

(* Convert option to list *)
Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.