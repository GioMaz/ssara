open Ssara

let regalloc program fuel =
  let (pi, _) = analyze_program program fuel in (* Get liveness info *)
  let g = get_ig pi in                          (* Get interference graph *)
  let peo = eliminate g in                      (* Get peo *)
  let c = get_coloring peo g in                 (* Get coloring *)
  match c with
  | Some c' -> Some (color_program c' program)
  | None -> None
;;

let program_empty = IRPreg.Block (0, [], [], Lazy.from_val IRPreg.Halt);;

let gen_label l =
  Printf.printf "%d:\n" l
;;

let string_of_preg preg =
  match preg with
  | RAX -> "%rax"
  | RBX -> "%rbx"
  | RCX -> "%rcx"
  | RDX -> "%rdx"
  | RSI -> "%rsi"
  | RDI -> "%rdi"
  | RSP -> "%rsp"
  | RBP -> "%rbp"
;;

let gen_insts is =
  let gen_inst i =
    Printf.printf "\t";
    (match i with
    | IRPreg.Def (r, IRPreg.Val _)  -> (Printf.printf "mov %s" (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Neg _)  -> (Printf.printf "neg %s" (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Load _) -> (Printf.printf "load %s" (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Add _)  -> (Printf.printf "add %s" (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Sub _)  -> (Printf.printf "sub %s" (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Mul _)  -> (Printf.printf "mul %s" (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Div _)  -> (Printf.printf "div %s" (string_of_preg r))
    | IRPreg.Store (_, _) -> ());
    Printf.printf "\n"
  in
  List.iter gen_inst is
;;

let gen_IRPreg_program program =
  match Lazy.force_val program with
  | IRPreg.Block (l, _ps, is, _j) ->
    gen_label l;
    gen_insts is
;;


let main () =
  let irvreg_program = Example1.example_block_1 in
  let irvreg_program = regalloc irvreg_program 10 in
  match irvreg_program with
  | Some program -> gen_IRPreg_program program
  | None -> Printf.printf "Failed to perform register allocation"
;;

main ()

(* Repress compiler errors *)
let _ = regalloc;;
let _ = program_empty;;
let _ = gen_IRPreg_program;;
let _ = regalloc Example1.example_block_1 10;;








































(* match regalloc Example1.example_block_1 10 with
| Some _ -> print_string "Yes\n"
| None -> print_string "No\n"
;; *)

(* module LblSet = Set.Make(Int);;

(* Get all the labels from a program until a fixpoint is reached *)
let get_labels_fixpoint p =
  let rec get_labels_aux p visited =
    let l = get_lbl p in
    if LblSet.mem l visited then
      visited
    else
      let visited' = LblSet.add l visited in
      List.fold_left
        (fun v s -> LblSet.union v (get_labels_aux s visited'))
        LblSet.empty
        (successors p)
  in
    get_labels_aux p LblSet.empty
;;

module RegSet = Set.Make(Int);;

(* Calculate the interference graph until a fixpoint is reached *)
let get_ig_fixpoint p =
  let labels = RegSet.cardinal (get_labels_fixpoint p) in
  let rec get_ig_fixpoint_aux prev_g prev_fuel =
    let fuel = prev_fuel + labels in
    let g = get_ig p fuel in
    let fixpoint =
      List.length (ig_v g) == List.length (ig_v prev_g) &&
      List.fold_left
      (fun b r ->
        b &&
        RegSet.equal
          (RegSet.of_list (ig_nbors g r))
          (RegSet.of_list (ig_nbors prev_g r))
      )
      true
      (ig_v g)
    in
    if fixpoint then
      g
    else
      get_ig_fixpoint_aux g fuel
  in
  get_ig_fixpoint_aux dict_empty 0
;;

(* Eliminate nodes following a PEO until a fixpoint is reached *)
let rec eliminate_fixpoint g =
  match find_next g with
  | Some next ->
    let g' = ig_remove_node g next in
    let (g'', peo) = eliminate_fixpoint g' in
    (g'', next :: peo)
  | None -> (g, [])
;;

(* let run_example_4 () =
  let p = Example4.example_block_1 in
  let g = get_ig_fixpoint p in
  List.iter
    (fun r ->
      Printf.printf "%d: " r;
      List.iter (Printf.printf "%d ") (ig_map g r);
      print_newline ()
    )
    (ig_dom g)
;; *)

let run_example_4 () =
  let p = Example4.example_block_1 in
  let g = get_ig_fixpoint p in
  let (_, peo) = eliminate_fixpoint g in
  List.iter
    (Printf.printf "%d\n")
    peo
;;

run_example_4 ();; *)