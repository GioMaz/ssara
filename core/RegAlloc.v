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
  By definition of PEO the `nbors` list contains all the neighbors of `v`
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
  | IRVreg.Neg v => IRPreg.Neg (color_val c v)
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
  | IRVreg.Store v v' =>
    IRPreg.Store
    (color_val c v)
    (Coloring.get c v')
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
    | IRVreg.Halt => IRPreg.Halt
    end)
  end
.

Import IRVreg.

Module Example1.
  CoFixpoint example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(1, 1); (5, 4)];
      r(4) <- phi [(2, 1); (6, 4)]
    ] [
    ] (
      Jump example_block_3
    )
  with example_block_3 : block :=
    Block 3 [
    ] [
      r(5) <- r(3) + (Imm 1);
      r(6) <- r(4) + (Imm 1)
    ] (
      Jump example_block_4
    )
  with example_block_4 : block :=
    Block 4 [
    ] [
    ] (
      Jump example_block_2
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
End Example1.

Module Example2.
  Definition example_block_2 : block :=
    Block 2 [
      r(3) <- phi [(0, 1)]
    ] [
      store (Ptr 0) r(3)
    ] (
      Halt
    )
  .

  Definition example_block_3 : block :=
    Block 3 [
      r(4) <- phi [(1, 1)]
    ] [
      store (Ptr 0) r(4)
    ] (
      Halt
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