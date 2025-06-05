Class RegClass := {
  reg : Set;
  reg_eqb : reg -> reg -> bool;
  reg_eq_dec : forall r r' : reg, {r = r'} + {r <> r'};
}.