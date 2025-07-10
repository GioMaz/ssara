open Ssara

module LblSet = Set.Make(Int);;

type opcode =
  | MOV

  (* Arithmetic *)
  | ADD
  | SUB
  | IMUL
  | IDIV

  (* Bitwise *)
  | AND
  | OR
  | XOR
  | NOT

  (* Control *)
  | JMP
  | CMP
  | JL
  | JLE
  | JG
  | JGE
  | JE
  | JNE
  | SYSCALL
;;

let string_of_opcode i =
  match i with
  | MOV     -> "mov"
  | ADD     -> "add"
  | SUB     -> "sub"
  | IMUL    -> "imul"
  | IDIV    -> "idiv"
  | AND     -> "and"
  | OR      -> "or"
  | XOR     -> "xor"
  | NOT     -> "not"
  | JMP     -> "jmp"
  | CMP     -> "cmp"
  | JL      -> "jl"
  | JLE     -> "jle"
  | JG      -> "jg"
  | JGE     -> "jge"
  | JE      -> "je"
  | JNE     -> "jne"
  | SYSCALL -> "syscall"
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

let string_of_preg preg =
  match preg with
  | RAX     -> "rax"
  | RBX     -> "rbx"
  | RCX     -> "rcx"
  | RDX     -> "rdx"
  | RSI     -> "rsi"
  | RDI     -> "rdi"
  | RSP     -> "rsp"
  | RBP     -> "rbp"
  | R8      -> "r8"
  | R9      -> "r9"
  | R10     -> "r10"
  | R11     -> "r11"
  | R12     -> "r12"
  | R13     -> "r13"
  | R14     -> "r14"
  | R15     -> "r15"
;;

(* Emit an argument that represents the memory location pointed by preg *)
let string_of_preg_deref preg =
  Printf.sprintf "[%s]" (string_of_preg preg)
;;

let string_of_val v = 
  match v with
  | IRPreg.Imm x -> Printf.sprintf "%d" x
  | IRPreg.Reg r -> Printf.sprintf "%s" (string_of_preg r)
  | IRPreg.Ptr p -> Printf.sprintf "%d" p
;;

(*
  Emit an argument that represents
  - The memory location pointed by x if x is an immediate value
  - The memory location pointed by the content of r if r is a register
  - The memory location pointed by p if p is a pointer
*)
let string_of_val_deref v =
  match v with
  | IRPreg.Imm x -> Printf.sprintf "[%d]" x
  | IRPreg.Reg r -> string_of_preg_deref r
  | IRPreg.Ptr p -> Printf.sprintf "[%d]" p
;;

let label_of_int l =
  Printf.sprintf "L%d" l
;;

let gen_bininst out opcode arg1 arg2 =
  Printf.fprintf out "\t%s\t%s,\t%s\t;\n" (string_of_opcode opcode) arg1 arg2
;;

let gen_uninst out opcode arg =
  Printf.fprintf out "\t%s\t%s\t\t;\n" (string_of_opcode opcode) arg
;;

let gen_nullinst out opcode =
  Printf.fprintf out "\t%s\t\t\t;\n" (string_of_opcode opcode)
;;

(*
  Since we are generating x86 assembly where the ALU instructions take only two
  arguments we have to convert our three address code instructions to fit into
  the x86 ones.
  To do so we simply prepend an instruction that moves the first argument of
  the operation into the target register.
*)
let gen_3ac_2ac_move out r r' =
  if r <> r' then gen_bininst out MOV (string_of_preg r) (string_of_preg r')
;;

let gen_insts out is =
  let gen_inst i =
    (match i with
    | IRPreg.Def (r, IRPreg.Val v)        -> gen_bininst out MOV (string_of_preg r) (string_of_val v)
    | IRPreg.Def (r, IRPreg.Load v)       -> gen_bininst out MOV (string_of_preg r) (string_of_val_deref v)
    | IRPreg.Store (r, r')                -> gen_bininst out MOV (string_of_preg_deref r) (string_of_preg r')
    | IRPreg.Def (r, IRPreg.Add (r', v))  -> gen_3ac_2ac_move out r r'; gen_bininst out ADD   (string_of_preg r) (string_of_val v)
    | IRPreg.Def (r, IRPreg.Sub (r', v))  -> gen_3ac_2ac_move out r r'; gen_bininst out SUB   (string_of_preg r) (string_of_val v)
    | IRPreg.Def (r, IRPreg.Mul (r', v))  -> gen_3ac_2ac_move out r r'; gen_bininst out IMUL  (string_of_preg r) (string_of_val v)
    | IRPreg.Def (r, IRPreg.Div (r', v))  -> gen_3ac_2ac_move out r r'; gen_bininst out IDIV  (string_of_preg r) (string_of_val v));
  in
  List.iter gen_inst is
;;

let gen_jump out b =
  gen_uninst out JMP (label_of_int (IRPreg.get_lbl b))
;;

let gen_condjump out c r v b1 b2 =
  gen_bininst out CMP                 (string_of_preg r) (string_of_val v);
  gen_uninst  out (opcode_of_cond c)  (label_of_int (IRPreg.get_lbl b1));
  gen_jump    out b2
;;

let gen_halt out () =
  gen_bininst   out MOV (string_of_preg RAX) (string_of_int 60);
  gen_bininst   out XOR (string_of_preg RDI) (string_of_preg RDI);
  gen_nullinst  out SYSCALL
;;

let gen_label out l =
  Printf.fprintf out "%s:\n" (label_of_int l)
;;

let gen_start out program =
  Printf.fprintf out "global _start\n";
  Printf.fprintf out "_start:\n";
  gen_jump out program
;;

let gen_section out s =
  Printf.fprintf out "section %s\n" s
;;

let gen_irpreg_program out program =
  let visited = ref LblSet.empty in
  let rec gen_irpreg_program_aux out program =
    let IRPreg.Block(l, ps, is, j) = Lazy.force_val program in

    if not (LblSet.mem l !visited) then (
      visited := LblSet.add l !visited;

      if not (List.is_empty ps) then
        failwith "Malformed program, should not contain phi instructions";

      (* Generate label *)
      gen_label out l;

      (* Generate instructions *)
      gen_insts out is;

      (* Generate jump instruction *)
      match Lazy.force_val j with
      | IRPreg.CondJump (c, r, v, b1, b2) ->
        gen_condjump out c r v b1 b2;
        gen_irpreg_program_aux out b1;
        gen_irpreg_program_aux out b2;

      | IRPreg.Jump b ->
        gen_jump out b;
        gen_irpreg_program_aux out b;

      | IRPreg.Halt ->
        gen_halt out ()
    )
  in
  gen_section out ".text";
  gen_start out program;
  gen_irpreg_program_aux out program
;;