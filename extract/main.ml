open Ssara

let vm_new () = Vm ([], []);;

let block_new l ps is j = Lazy.from_val (
  Block (l, ps, is, Lazy.from_val j)
  );;

let program_new = block_new;;

let run_example () =
  let vm = vm_new () in
  let program = program_new 0 [] [] Halt in
  let Vm (_, cells) = run vm program 4 in
  match cells with
  | [] -> None
  | x :: _ -> Some x
;;

match run_example () with
| Some _ -> print_string "Some"
| None -> print_string "None"
;;