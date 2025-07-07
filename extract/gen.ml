open Ssara

module LblSet = Set.Make(Int);;

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

let string_of_cond c =
  match c with
  | Jeq -> "jeq"
  | Jne -> "jne"
  | Jlt -> "jl"
  | Jle -> "jle"
  | Jgt -> "jg"
  | Jge -> "jge"
;;

let string_of_val v = 
  match v with
  | IRPreg.Imm x -> Printf.sprintf "$%d" x
  | IRPreg.Reg r -> Printf.sprintf "%s" (string_of_preg r)
  | IRPreg.Ptr p -> Printf.sprintf "(%d)" p
;;

(*
  Since we are generating X86 assembly where the ALU instructions take only two
  arguments we have to convert our three address code instructions to fit into
  the X86 ones.
  To do so we simply prepend an instruction that moves the first argument of
  the operation into the target register.
*)
let gen_3ac_2ac_move r r' =
  if r <> r' then Printf.printf "mov %s, %s" (string_of_preg r') (string_of_preg r)
;;

let gen_insts is =
  let gen_inst i =
    Printf.printf "\t";
    (match i with
    | IRPreg.Def (r, IRPreg.Val v)        -> Printf.printf "mov  %s, %s" (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Neg v)        -> Printf.printf "neg  %s, %s" (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Load v)       -> Printf.printf "load %s, %s" (string_of_val v) (string_of_preg r)
    | IRPreg.Store (v, r)                 -> Printf.printf "mov  %s, %s" (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Add (r', v))  -> gen_3ac_2ac_move r r'; Printf.printf "add  %s, %s" (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Sub (r', v))  -> gen_3ac_2ac_move r r'; Printf.printf "sub  %s, %s" (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Mul (r', v))  -> gen_3ac_2ac_move r r'; Printf.printf "mul  %s, %s" (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Div (r', v))  -> gen_3ac_2ac_move r r'; Printf.printf "div  %s, %s" (string_of_val v) (string_of_preg r));
    Printf.printf "\n"
  in
  List.iter gen_inst is
;;

let gen_condjump c r v b1 b2 =
  Printf.printf "\tcmp %s, %s\n" (string_of_preg r) (string_of_val v);
  Printf.printf "\t%s %d\n" (string_of_cond c) (IRPreg.get_lbl b1);
  Printf.printf "\tjmp %d\n" (IRPreg.get_lbl b2)
;;

let gen_jump b =
  Printf.printf "\tjmp %d\n" (IRPreg.get_lbl b)
;;

let gen_halt () =
  Printf.printf "\tret\n"
;;

let gen_irpreg_program program =
  let rec gen_irpreg_program_aux program visited =
    let IRPreg.Block(l, ps, is, j) = Lazy.force_val program in

    if not (List.is_empty ps) then
      failwith "Malformed program, should not contain phi instructions";

    (* Generate labels, instructions and jump instruction *)
    gen_label l;
    gen_insts is;

    match Lazy.force_val j with
    | IRPreg.CondJump (c, r, v, b1, b2) ->
      (* Generate code for conditional jump *)
      let l1 = IRPreg.get_lbl b1 in
      let l2 = IRPreg.get_lbl b2 in
      gen_condjump c r v b1 b2;
      if not (LblSet.mem l1 visited) then
        gen_irpreg_program_aux b1 (LblSet.add l1 visited);
      if not (LblSet.mem l2 visited) then
        gen_irpreg_program_aux b2 (LblSet.add l2 visited);

    | IRPreg.Jump b ->
      (* Generate code for unconditional jump *)
      let l = IRPreg.get_lbl b in
      gen_jump b;
      if not (LblSet.mem l visited) then
        gen_irpreg_program_aux b (LblSet.add l visited);

    | IRPreg.Halt ->
      (* Generate code for program halt *)
      gen_halt ()
  in
  gen_irpreg_program_aux program LblSet.empty
;;