open Ssara

module LblSet = Set.Make(Int);;

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
      List.length (ig_dom g) == List.length (ig_dom prev_g) &&
      List.fold_left
      (fun b r ->
        b &&
        RegSet.equal
          (RegSet.of_list (ig_map g r))
          (RegSet.of_list (ig_map prev_g r))
      )
      true
      (ig_dom g)
    in
    if fixpoint then
      g
    else
      get_ig_fixpoint_aux g fuel
  in
  get_ig_fixpoint_aux ig_empty 0
;;

(* Eliminate nodes following a PEO until a fixpoint is reached *)
let rec eliminate_fixpoint g =
  match find_next g with
  | Some next ->
    let g' = ig_remove_node g next in
    let (g'', regs) = eliminate_fixpoint g' in
    (g'', next :: regs)
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

run_example_4 ();;