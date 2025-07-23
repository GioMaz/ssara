From Ssara.Core Require Import LivenessInfo.
From Ssara.Core Require Import InterfGraph.
From Ssara.Core Require Import Peo.
From Ssara.Core Require Import Dict.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Ssara.Core Require Import IR.
From Stdlib Require Import Bool.

From Ssara.Core Require Import IRVregModule.
From Ssara.Core Require Import IRPregModule.

Module ColoringParams <: DICT_PARAMS.
  Definition key := IRVreg.reg.
  Definition value := IRPreg.reg.
  Definition default : value := tmp.
  Definition key_eq_dec := Nat.eq_dec.
End ColoringParams.
Module Coloring := MakeDict ColoringParams.

(*
  The coloring is performed this way:
  - Get a perfect elimination order (ordering that eliminates simplicial nodes first)
  - For each node in the peo reinsert it into the graph and color it differently wrt its neighbors
*)
Definition preg_compl (colors : list preg) : option preg :=
  match IRPreg.regs_diff preg_all_minus_tmp colors with
  | nil => None
  | c :: _ => Some c
  end
.

(*
  IMPORTANT: by definition of PEO the `nbors` list contains all the neighbors of `v`
  TODO: prove this
*)
Definition color_vreg (v : IRVreg.reg) (c : Coloring.dict) (g : InterfGraph.dict) : option preg :=
  let nbors := InterfGraph.get g v in
  let used := map (Coloring.get c) nbors in
  preg_compl used
.

(*
  The None constructor is returned if there aren't enough physical registers
  for the coloring to happen, this may happen if we don't perform spilling
  before the coloring.
*)
Definition get_coloring (peo : list IRVreg.reg) (g : InterfGraph.dict) : option Coloring.dict :=
  let fix get_coloring_aux (peo : list IRVreg.reg) (c : Coloring.dict ) (g : InterfGraph.dict) : option Coloring.dict :=
    match peo with
    | nil => Some c
    | v :: peo =>
      match color_vreg v c g with
      | Some p =>
        let c := Coloring.update c v p in
        get_coloring_aux peo c g
      | None => None
      end
    end
  in
  get_coloring_aux peo Coloring.empty g
.

(*
  Converting the intermediate representation into one using physical registers
  instead.
*)

Definition color_phi (c : Coloring.dict) (p : IRVreg.phi) : IRPreg.phi :=
  match p with
  | IRVreg.Phi v vs =>
    IRPreg.Phi
    (Coloring.get c v)
    (map (fun '(v, l) => (Coloring.get c v, l)) vs)
  end
.

Definition color_val (c : Coloring.dict) (v : IRVreg.val) : IRPreg.val :=
  match v with
  | IRVreg.Imm x => IRPreg.Imm x
  | IRVreg.Reg v => IRPreg.Reg (Coloring.get c v)
  | IRVreg.Ptr p => IRPreg.Ptr p
  end
.

Definition color_expr (c : Coloring.dict) (e : IRVreg.expr) : IRPreg.expr :=
  match e with
  | IRVreg.Val v => IRPreg.Val (color_val c v)
  | IRVreg.Load v => IRPreg.Load (color_val c v)
  | IRVreg.Add v v' => IRPreg.Add (Coloring.get c v) (color_val c v')
  | IRVreg.Sub v v' => IRPreg.Sub (Coloring.get c v) (color_val c v')
  | IRVreg.Mul v v' => IRPreg.Mul (Coloring.get c v) (color_val c v')
  | IRVreg.Div v v' => IRPreg.Div (Coloring.get c v) (color_val c v')
  end
.

Definition color_inst (c : Coloring.dict) (i : IRVreg.inst) : IRPreg.inst :=
  match i with
  | IRVreg.Def v e =>
    IRPreg.Def
    (Coloring.get c v)
    (color_expr c e)
  | IRVreg.Store r r' =>
    IRPreg.Store
    (Coloring.get c r)
    (Coloring.get c r')
  end
.

CoFixpoint color_program (c : Coloring.dict) (p : IRVreg.program) : IRPreg.program :=
  match p with
  | IRVreg.Block l ps is j =>
    IRPreg.Block
    l
    (map (color_phi c) ps)
    (map (color_inst c) is)
    (match j with
    | IRVreg.CondJump c' r v b1 b2 =>
      IRPreg.CondJump c'
      (Coloring.get c r)
      (color_val c v)
      (color_program c b1)
      (color_program c b2)
    | IRVreg.Jump b => IRPreg.Jump (color_program c b)
    | IRVreg.Ret r => IRPreg.Ret (Coloring.get c r)
    end)
  end
.

Import IRVreg.

Module Example1.
  Definition example_block_4 : block :=
    Block 4 [
    ] [
      r(7) <- r(5) + (Reg 6)
    ] (
      ret r(7)
    )
  .

  Definition example_block_3 : block :=
    Block 3 [
    ] [
      r(5) <- r(3) + (Imm 1);
      r(6) <- r(4) + (Imm 1)
    ] (
      Jump example_block_4
    )
  .

  Definition example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(1, 1)];
      r(4) <- phi [(2, 1)]
    ] [
    ] (
      Jump example_block_3
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(1) <- (Imm 34);
      r(2) <- (Imm 35)
    ] (
      Jump example_block_2
    )
  .
  Compute 0.

  Definition ig :=
    let (pi, _) := analyze_program example_block_1 10 in
    InterfGraph.get_ig pi
  .
  Compute InterfGraph.listify ig.

  Definition peo := eliminate_fuel ig 10.
  Compute peo.

  Definition c := get_coloring peo ig.
  Compute
    match c with
    | Some c => Coloring.listify c
    | None => nil
    end
  .
End Example1.

Module Example2.
  Definition example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(0, 1)]
    ] [
      r(4) <- Ptr 0
      (* store r(4) r(3) *)
    ] (
      ret r(4)
    )
  .

  Definition example_block_3 : block :=
    Block 3 [
      r(5) <- phi [(1, 1)]
    ] [
      r(6) <- Ptr 0
      (* store r(6) r(5) *)
    ] (
      ret r(6)
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(0) <- (Imm 34);
      r(1) <- (Imm 35)
    ] (
      if r(0) < (Reg 1) then example_block_2 else example_block_3
    )
  .
End Example2.

(* Example 3 *)
Module Example3.
  Definition example_block_3 : block :=
    Block 3 [
    ] [
    ] (
      ret r(5)
    )
  .

  CoFixpoint example_block_2 : block :=
    Block 2 [
      r(2) <- phi [(0, 1); (4, 2)];  (* Iterator *)
      r(3) <- phi [(1, 1); (5, 2)]   (* Accumulator *)
    ] [
      r(4) <- r(2) - (Imm 1);
      r(5) <- r(3) * (Reg 4)
    ] (
      if r(4) <= (Imm 1) then example_block_3 else example_block_2
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(0) <- Imm 5;  (* Iterator *)
      r(1) <- Reg 0   (* Accumulator *)
    ] (
      Jump example_block_2
    )
  .
End Example3.

(* Example 4 *)
Module Example4.
  Definition example_block_3 : block :=
    Block 3 [
    ] [
    ] (
      ret r(3)
    )
  .

  CoFixpoint example_block_2 : block :=
    Block 2 [
      r(2) <- phi [(0, 1); (3, 2)]
    ] [
      r(3) <- r(2) + (Imm 2)
    ] (
      if r(3) < (Reg 1) then example_block_2 else example_block_3
    )
  .

  Definition example_block_1 : block :=
    Block 1 [
    ] [
      r(0) <- Imm 0;
      r(1) <- Imm 20
    ] (
      Jump example_block_2
    )
  .
End Example4.