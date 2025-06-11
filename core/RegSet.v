From Stdlib Require Import ListSet.
From Ssara.Core Require Import RegClass.

Section RegSet.

  Context {reg_instance : RegClass}.
  
  (* Set of virtual registers *)
  Definition regs_union := set_union reg_eq_dec.
  Definition regs_diff := set_diff reg_eq_dec.
  Definition regs_add := set_add reg_eq_dec.
  Definition regs_remove := set_remove reg_eq_dec.
  Definition regs_mem := set_mem reg_eq_dec.

End RegSet.