open Ssara

module LblSet = Set.Make(Int);;

(* Get all the labels from a program *)
let get_labels p =
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

(* Get all the registers used in a program *)
let get_regs p =
  let inst_defs (is : inst list) =
    fold_left (
      fun rs i ->
        match inst_reg i with
        | Some r -> r :: rs
        | None -> rs
    )
    is
    []
  in
  let rec get_regs_aux p visited =
    let p' = Lazy.force p in
    match p' with
    | Block (l, ps, is, _) ->
      if LblSet.mem l visited then
        RegSet.empty
      else
        let visited' = LblSet.add l visited in
        let regs = fold_left (fun acc s -> RegSet.union acc (get_regs_aux s visited')) (successors p) RegSet.empty in
        let regs' = RegSet.union
          (ps |> phi_defs |> RegSet.of_list)
          (is |> inst_defs |> RegSet.of_list)
        in
        RegSet.union regs regs'
  in
  get_regs_aux p LblSet.empty
;;

(* Calculate the interference graph until a fixpoint is reached *)
let get_ig_fixpoint p =
  let labels = RegSet.cardinal (get_labels p) in
  let regs = RegSet.to_list (get_regs p) in
  let rec get_ig_aux prev_g prev_fuel =
    let fuel = prev_fuel + labels in
    let g = get_ig p fuel in
    let fixpoint = List.fold_left
      (fun b r ->
        b &&
        RegSet.equal
          (RegSet.of_list (g r))
          (RegSet.of_list (prev_g r))
      )
      true
      regs
    in
    if fixpoint then
      g
    else
      get_ig_aux g fuel
  in
  get_ig_aux (fun _ -> []) 0
;;

let run_example_4 () =
  let p = Example4.example_block_1 in
  let g = get_ig_fixpoint p in
  RegSet.iter
    (fun r ->
      Printf.printf "%d: " r;
      List.iter (Printf.printf "%d ") (g r);
      print_newline ()
    )
    (get_regs p)
;;

run_example_4 ();;