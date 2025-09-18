open Regassign
open Ssara
open Oracles

type vm_native_result =
  | Success of int
  | Failure of int * int
;;

let compare_vm_native irvreg_program =
  let rv_vm = (Vm.get_reg (Vm.run Vm.vm_empty irvreg_program fuel_vm) 0) in
  let rv_native = regassign_and_run_native irvreg_program in
  if rv_vm = rv_native then
    Success rv_vm
  else
    Failure (rv_vm, rv_native)
;;

let print_vm_native_result r =
  match r with
  | Success n -> Printf.printf "Success: %d\n" n
  | Failure (n, n') -> Printf.printf "Failure: %d %d\n" n n'
;;

let main () =
  List.iter
    (fun x -> x |> compare_vm_native |> print_vm_native_result)
    [
      Example1.example_block_1;
      Example2.example_block_1;
      Example3.example_block_1;
      Example4.example_block_1;
      Example5.example_block_1;
      Example6.example_block_1;
    ]
;;

main ();;
