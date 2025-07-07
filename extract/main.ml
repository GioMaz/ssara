open Ssara

module LblSet = Set.Make(Int);;

let regalloc program fuel =
  let (pi, _) = analyze_program program fuel in (* Get liveness info *)
  let g = get_ig pi in                          (* Get interference graph *)
  let peo = eliminate g in                      (* Get peo *)
  let coloring =                                (* Get coloring *)
    match get_coloring peo g with 
    | Some c -> c
    | None -> failwith "Error, there aren't enough registers"
  in
  let irpreg_program = color_program coloring program in
  ssa_destruct irpreg_program
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

let string_of_val v = 
  match v with
  | IRPreg.Imm x -> Printf.sprintf "$%d" x
  | IRPreg.Reg r -> Printf.sprintf "%s" (string_of_preg r)
  | IRPreg.Ptr p -> Printf.sprintf "(%d)" p
;;

let gen_insts is =
  let gen_inst i =
    Printf.printf "\t";
    (match i with
    | IRPreg.Def (r, IRPreg.Val v)       -> (Printf.printf "mov   %s, %s"   (string_of_val v) (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Neg v)       -> (Printf.printf "neg   %s, %s"   (string_of_val v) (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Load v)      -> (Printf.printf "load  %s, %s"   (string_of_val v) (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Add (_, v))  -> (Printf.printf "add   %s, %s"   (string_of_val v) (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Sub (_, v))  -> (Printf.printf "sub   %s, %s"   (string_of_val v) (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Mul (_, v))  -> (Printf.printf "mul   %s, %s"   (string_of_val v) (string_of_preg r))
    | IRPreg.Def (r, IRPreg.Div (_, v))  -> (Printf.printf "div   %s, %s"   (string_of_val v) (string_of_preg r))
    | IRPreg.Store (_, _) -> ());
    Printf.printf "\n"
  in
  List.iter gen_inst is
;;

let gen_condjump c r v b1 b2 =
  Printf.printf "\tcmp %s %s\n" (string_of_preg r) (string_of_val v);
  Printf.printf "\t";
  (match c with
  | Jeq -> Printf.printf "jeq %d\n" (IRPreg.get_lbl b1)
  | Jne -> Printf.printf "jne %d\n" (IRPreg.get_lbl b1)
  | Jlt -> Printf.printf "jlt %d\n" (IRPreg.get_lbl b1)
  | Jle -> Printf.printf "jle %d\n" (IRPreg.get_lbl b1)
  | Jgt -> Printf.printf "jgt %d\n" (IRPreg.get_lbl b1)
  | Jge -> Printf.printf "jge %d\n" (IRPreg.get_lbl b1));
  Printf.printf "\tjmp %d\n" (IRPreg.get_lbl b2)
;;

let gen_jump b =
  Printf.printf "\tjmp %d\n" (IRPreg.get_lbl b)
;;

let gen_halt () =
  Printf.printf "\tret 0\n"
;;

let gen_IRPreg_program program =
  let rec gen_IRPreg_program_aux program visited =
    match Lazy.force_val program with
    | IRPreg.Block (l, ps, is, j) ->
      if List.is_empty ps then (
        gen_label l;
        gen_insts is;
        match (Lazy.force_val j) with
        | IRPreg.CondJump (c, r, v, b1, b2) ->
          let l1 = IRPreg.get_lbl b1 in
          let l2 = IRPreg.get_lbl b2 in
          gen_condjump c r v b1 b2;
          if not (LblSet.mem l1 visited) then
            gen_IRPreg_program_aux b1 (LblSet.add l1 visited);
          if not (LblSet.mem l2 visited) then
            gen_IRPreg_program_aux b2 (LblSet.add l2 visited);
        | IRPreg.Jump b ->
          let l = IRPreg.get_lbl b in
          gen_jump b;
          if not (LblSet.mem l visited) then
            gen_IRPreg_program_aux b (LblSet.add l visited);
        | IRPreg.Halt ->
          gen_halt ()
      ) else
        failwith "Malformed program, should not contain phi instructions"
  in
  gen_IRPreg_program_aux program LblSet.empty
;;

let main () =
  let irvreg_program = Example1.example_block_1 in
  let irpreg_program = regalloc irvreg_program 10 in
  gen_IRPreg_program irpreg_program
;;

main ()

(* Suppress compiler errors *)
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