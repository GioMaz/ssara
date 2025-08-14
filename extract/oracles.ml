(* Required since the termination of the `Vm.run` function cannot be proved *)
let fuel_vm = 1000;;

(* Required since we don't include a proof for the termination of the liveness analysis algorithm *)
let fuel_analyze = 50;;

(* Required since we don't include the proof for the termination of the SSA destruction algorithm *)
let fuel_destruct = 50;;