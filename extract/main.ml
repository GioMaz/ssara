open Run

let vm = Vm (Nil, Nil);;
let program = Nil;;
let Vm (_, cells) = run vm program (S O);;

match cells with
| Nil -> print_string "None"
| Cons _ -> print_string "Some"
;;