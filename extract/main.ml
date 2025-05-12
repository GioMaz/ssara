open Run

let vm_new () = Vm (Nil, Nil);;

let block_new ps is j = Lazy.from_val (
  Block (ps, is, Lazy.from_val j)
);;
let program_new = block_new;;

let vm = vm_new ();;
let program = program_new Nil Nil Halt;;
let Vm (_, cells) = run vm program (S O);;

match cells with
| Nil -> print_string "None"
| Cons _ -> print_string "Some"
;;
