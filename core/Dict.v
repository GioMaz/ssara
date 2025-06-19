From Stdlib Require Import Lists.List.
From Stdlib Require Import ListSet.

(* Section Dict.
  Class DictClass := {
    key : Set;
    value : Type;
    default : value;
    key_eq_dec : forall k k' : key, {k = k'} + {k <> k'};
  }.
  Context {dict_instance : DictClass}.

  Definition dict : Type := set key * (key -> value).
  Definition dict_empty : dict := (nil, fun _ => default).

  Definition dict_update (d : dict) (k : key) (v : value) : dict :=
    let (keys, m) := d in
    (set_add key_eq_dec k keys, fun k' => if key_eq_dec k k' then v else m k')
  .

  Definition dict_map (d : dict) (k : key) : value := (snd d) k.

  Definition dict_keys (d : dict) : set key := fst d.

  Definition dict_values (d : dict) : set value :=
    let (keys, m) := d in map m keys
  .

  Definition dict_list (d : dict) : list (key * value) :=
    let (keys, m) := d in map (fun k => (k, m k)) keys
  .

  Definition dict_mem (d : dict) (k : key) : bool :=
    existsb (fun k' => if key_eq_dec k k' then true else false) (dict_keys d)
  .

  Definition dict_size (d : dict) : nat :=
    length (dict_keys d)
  .

End Dict. *)

Module Type DICT_PARAMS.
  Parameter key : Set.
  Parameter value : Type.
  Parameter default : value.
  Parameter key_eq_dec : forall k k' : key, {k = k'} + {k <> k'}.
End DICT_PARAMS.

Module MakeDict (P : DICT_PARAMS).
  Definition dict : Type := set P.key * (P.key -> P.value).

  Definition empty : dict := (nil, fun _ => P.default).

  Definition update (d : dict) (k : P.key) (v : P.value) : dict :=
    let (keys, m) := d in
    (set_add P.key_eq_dec k keys, fun k' => if P.key_eq_dec k k' then v else m k')
  .

  Definition get (d : dict) (k : P.key) : P.value := (snd d) k.

  Definition keys (d : dict) : set P.key := fst d.

  Definition values (d : dict) : set P.value :=
    let (keys, m) := d in map m keys
  .

  Definition list (d : dict) : list (P.key * P.value) :=
    let (keys, m) := d in map (fun k => (k, m k)) keys
  .

  Definition mem (d : dict) (k : P.key) : bool :=
    existsb (fun k' => if P.key_eq_dec k k' then true else false) (keys d)
  .

  Definition size (d : dict) : nat :=
    length (keys d)
  .
End MakeDict.