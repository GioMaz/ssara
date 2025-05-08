open Run

let vm_new () = Vm (Nil, Nil);;

let vm = vm_new ();;
let block = Lazy.from_val (
  Block (
    Nil,
    Nil,
    Lazy.from_val Halt
  )
);;
let program = Cons (block, Nil);;
let Vm (_, cells) = run vm program (S O);;

match cells with
| Nil -> print_string "None"
| Cons _ -> print_string "Some"
;;