open Run

let vm_new () = Vm (Nil, Nil);;

let block_new ps is j = Lazy.from_val (
  Block (ps, is, Lazy.from_val j)
);;

let rec program_new bs =
  match bs with
  | [] -> Nil
  | x :: xs -> Cons (x, (program_new xs))
;;

let vm = vm_new ();;
let block = block_new Nil Nil Halt;;
let program = program_new [block];;
let Vm (_, cells) = run vm program (S O);;

match cells with
| Nil -> print_string "None"
| Cons _ -> print_string "Some"
;;