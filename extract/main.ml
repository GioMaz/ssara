open Regalloc
open Ssara

let fuel = 100;;

let compare_vm_native irvreg_program =
  let rv_vm = (Vm.get_reg (Vm.run Vm.vm_empty irvreg_program fuel) 0) in
  let rv_native = regalloc_and_run_native irvreg_program in
  Printf.printf "%s: vm_result: %d, native_result: %d\n"
    (if rv_vm = rv_native then "Success" else "Failure")
    rv_vm rv_native
;;

let main () =
  List.iter
    compare_vm_native
    [
      Example1.example_block_1;
      Example2.example_block_1;
      Example3.example_block_1;
      Example4.example_block_1;
      Example5.example_block_1;
    ]
;;

main ();;