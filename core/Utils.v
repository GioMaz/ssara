From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.

Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.

Definition conjunction {A : Type} (f : A -> bool) (l : list A) : bool :=
  fold_left (fun b x => b && f x) l true
.