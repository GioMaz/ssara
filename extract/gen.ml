open Ssara

module LblSet = Set.Make(Int);;

type opcode =
  | MOV
  | NEG
  | ADD
  | SUB
  | MUL
  | DIV
  | RET
  | JMP
  | CMP
  | JL
  | JLE
  | JG
  | JGE
  | JE
  | JNE
;;

let string_of_opcode i =
  match i with
  | MOV -> "mov"
  | NEG -> "neg"
  | ADD -> "add"
  | SUB -> "sub"
  | MUL -> "mul"
  | DIV -> "div"
  | RET -> "ret"
  | JMP -> "jmp"
  | CMP -> "cmp"
  | JL  -> "jl"
  | JLE -> "jle"
  | JG  -> "jg"
  | JGE -> "jge"
  | JE  -> "je"
  | JNE -> "jne"
;;

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

let opcode_of_cond c =
  match c with
  | Jeq -> JE
  | Jne -> JNE
  | Jlt -> JL
  | Jle -> JLE
  | Jgt -> JG
  | Jge -> JGE
;;

let string_of_val v = 
  match v with
  | IRPreg.Imm x -> Printf.sprintf "$%d" x
  | IRPreg.Reg r -> Printf.sprintf "%s" (string_of_preg r)
  | IRPreg.Ptr p -> Printf.sprintf "(%d)" p
;;

let gen_bininst opcode arg1 arg2 =
  Printf.printf "\t%s\t%s,\t%s\t;\n" (string_of_opcode opcode) arg1 arg2
;;

let gen_uninst opcode arg =
  Printf.printf "\t%s\t%s\t\t;\n" (string_of_opcode opcode) arg
;;

let gen_nullinst opcode =
  Printf.printf "\t%s\t\t\t;\n" (string_of_opcode opcode)
;;

(*
  Since we are generating x86 assembly where the ALU instructions take only two
  arguments we have to convert our three address code instructions to fit into
  the x86 ones.
  To do so we simply prepend an instruction that moves the first argument of
  the operation into the target register.
*)
let gen_3ac_2ac_move r r' =
  if r <> r' then gen_bininst MOV (string_of_preg r') (string_of_preg r)
;;

let gen_insts is =
  let gen_inst i =
    (match i with
    | IRPreg.Def (r, IRPreg.Val v)        -> gen_bininst MOV  (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Neg v)        -> gen_bininst NEG  (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Load v)       -> gen_bininst MOV (string_of_val v) (string_of_preg r)
    | IRPreg.Store (v, r)                 -> gen_bininst MOV  (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Add (r', v))  -> gen_3ac_2ac_move r r'; gen_bininst ADD (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Sub (r', v))  -> gen_3ac_2ac_move r r'; gen_bininst SUB (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Mul (r', v))  -> gen_3ac_2ac_move r r'; gen_bininst MUL (string_of_val v) (string_of_preg r)
    | IRPreg.Def (r, IRPreg.Div (r', v))  -> gen_3ac_2ac_move r r'; gen_bininst DIV (string_of_val v) (string_of_preg r));
  in
  List.iter gen_inst is
;;

let gen_condjump c r v b1 b2 =
  gen_bininst CMP                 (string_of_preg r) (string_of_val v);
  gen_uninst  (opcode_of_cond c)  (string_of_int (IRPreg.get_lbl b1));
  gen_uninst  JMP                 (string_of_int (IRPreg.get_lbl b2))
;;

let gen_jump b =
  gen_uninst JMP (string_of_int (IRPreg.get_lbl b))
;;

let gen_halt () =
  gen_nullinst RET
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