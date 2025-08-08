open Ssara
open Gen
open Oracles

let regalloc irvreg_program =
  let (programinfo, _) = analyze_program irvreg_program fuel_analyze in (* Get liveness info *)
  let interfgraph = get_ig programinfo in                               (* Get interference graph *)
  let peo = eliminate interfgraph in                                    (* Get peo *)
  let coloring =                                                        (* Get coloring *)
    match get_coloring peo interfgraph with
    | Some c -> c
    | None -> failwith "Not enough registers to complete allocation"
  in
  let irpreg_program = color_program coloring irvreg_program in         (* Color program *)
  ssa_destruct fuel_destruct  irpreg_program                            (* SSA destruction *)
;;

let command_fail cmd =
  failwith (Printf.sprintf "Failed to execute command: %s\n" cmd)
;;

let run_native irpreg_program =
  let asm_filename = "/tmp/main.asm" in
  let obj_filename = "/tmp/main.o" in
  let bin_filename = "/tmp/main" in

  (* Generate asm file*)
  let out = Out_channel.open_text asm_filename in
  gen_irpreg_program stdout irpreg_program;
  gen_irpreg_program out irpreg_program;
  Out_channel.close out;

  (* Define commands *)
  let cmd_asm = Printf.sprintf "nasm -f elf64 -o %s %s" obj_filename asm_filename in
  let cmd_obj = Printf.sprintf "ld -o %s %s" bin_filename obj_filename in
  let cmd_bin = bin_filename in

  (* Assemble asm file *)
  let rv = Sys.command cmd_asm in
  if rv <> 0 then command_fail cmd_asm;

  (* Link object file *)
  let rv = Sys.command cmd_obj in
  if rv <> 0 then command_fail cmd_obj;

  (* Run binary file and clean compilation files *)
  let rv = Sys.command cmd_bin in
  Sys.remove asm_filename; Sys.remove obj_filename; Sys.remove bin_filename;
  rv
;;

let regalloc_and_run_native irvreg_program =
  irvreg_program |> regalloc |> run_native
;;