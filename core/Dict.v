From Stdlib Require Import Lists.List.
From Stdlib Require Import ListSet.

Module Type DICT_PARAMS.
  Parameter key : Set.
  Parameter value : Type.
  Parameter default : value.
  Parameter key_eq_dec : forall k k' : key, {k = k'} + {k <> k'}.
End DICT_PARAMS.

Module MakeDict (D : DICT_PARAMS).
  Definition key := D.key.
  Definition value := D.value.
  Definition default := D.default.
  Definition key_eq_dec := D.key_eq_dec.

  Definition dict : Type := set key * (key -> value).
  Definition empty : dict := (nil, fun _ => default).

  Definition update (d : dict) (k : key) (v : value) : dict :=
    let (keys, m) := d in
    (set_add key_eq_dec k keys, fun k' => if key_eq_dec k k' then v else m k')
  .

  Definition get (d : dict) (k : key) : value := (snd d) k.

  Definition keys (d : dict) : set key := fst d.

  Definition values (d : dict) : set value :=
    let (keys, m) := d in map m keys
  .

  Definition listify (d : dict) : list (key * value) :=
    let (keys, m) := d in map (fun k => (k, m k)) keys
  .

  Definition mem (d : dict) (k : key) : bool :=
    existsb (fun k' => if key_eq_dec k k' then true else false) (keys d)
  .

  Definition size (d : dict) : nat :=
    length (keys d)
  .

End MakeDict.