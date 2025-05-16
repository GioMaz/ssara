open Ssara

let vm_new () = Vm ([], []);;

let block_new l ps is j = Lazy.from_val (
  Block (l, ps, is, Lazy.from_val j)
  )
;;

let program_new = block_new;;

let run_example_1 () =
  let vm = vm_new () in
  let program = program_new 0 [] [] Halt in
  let Vm (_, cells) = run vm program 4 in
  if List.is_empty cells then
    print_string "None\n"
  else
    print_string "Some\n"
;;

let run_example_2 () =
  let i1 = Def (1, (Val (Imm Z0))) in
  let i2 = Def (2, (Val (Imm Z0))) in
  let i3 = Store ((Ptr 0), 1) in
  let i4 = Store ((Ptr 0), 2) in
  let p = (program_new 0 [] [i1; i2; i3; i4] Halt) in
  let g = get_ig p 10 in
  List.iter print_int (g 1); print_char '\n';
  List.iter print_int (g 2); print_char '\n';
;;

run_example_1 ();;
run_example_2 ();;