Require Import Ssara.Base.Vm.

Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "run.ml" run.
