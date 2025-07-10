open Regalloc
open Ssara

let main () =
  let _rv = regalloc_and_run_native Example2.example_block_1 in
  let _rv = regalloc_and_run_native Example3.example_block_1 in
  0
;;

main ();;