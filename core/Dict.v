From Stdlib Require Import Lists.List.
From Stdlib Require Import ListSet.

Section Dict.
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
    (set_add key_eq_dec k keys, fun k' => if key_eq_dec k' k then v else m k')
  .

  Definition dict_map (d : dict) (k : key) : value :=
    let (_, m) := d in m k
  .

  Definition dict_keys (d : dict) : set key :=
    let (keys, _) := d in keys
  .

  Definition dict_values (d : dict) : set value :=
    let (keys, m) := d in map m keys
  .

  Definition dict_list (d : dict) : list (key * value) :=
    let (keys, m) := d in map (fun k => (k, m k)) keys
  .

  Definition dict_size (d : dict) : nat :=
    length (dict_keys d)
  .

End Dict.