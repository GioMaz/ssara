open Ssara
open Gen

let regalloc program fuel =
  let (programinfo, _) = analyze_program program fuel in  (* Get liveness info *)
  let interfgraph = get_ig programinfo in                 (* Get interference graph *)
  let peo = eliminate interfgraph in                      (* Get peo *)
  let coloring =                                          (* Get coloring *)
    match get_coloring peo interfgraph with
    | Some c -> c
    | None -> failwith "Not enough registers to complete allocation"
  in
  let irpreg_program = color_program coloring program in  (* SSA destruction *)
  ssa_destruct irpreg_program
;;

let main () =
  let irvreg_program = Example2.example_block_1 in
  let irpreg_program = regalloc irvreg_program 10 in
  gen_irpreg_program irpreg_program
;;

main ()