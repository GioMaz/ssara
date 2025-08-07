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

  Definition get (d : dict) (k : key) : value := (snd d) k.

  Definition keys (d : dict) : set key := fst d.

  Definition update (d : dict) (k : key) (v : value) : dict :=
    (set_add key_eq_dec k (keys d), fun k' => if key_eq_dec k k' then v else get d k')
  .

  Definition values (d : dict) : set value :=
    map (get d) (keys d)
  .

  Definition listify (d : dict) : list (key * value) :=
    map (fun k => (k, get d k)) (keys d)
  .

  Definition mem (d : dict) (k : key) : bool :=
    existsb (fun k' => if key_eq_dec k k' then true else false) (keys d)
  .

  Definition size (d : dict) : nat :=
    length (keys d)
  .

End MakeDict.