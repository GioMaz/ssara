From Stdlib Require Import Lists.List.
From Stdlib Require Import ListSet.
From Stdlib Require Import Bool.

Definition option_to_list {A : Type} (x : option A) : list A :=
  match x with
  | Some x' => x' :: nil
  | None => nil
  end
.

Fixpoint list_option_to_list {A : Type} (l : list (option A)) : list A :=
  match l with
  | nil => nil
  | x :: xs =>
    match x with
    | Some x => x :: (list_option_to_list xs)
    | None => list_option_to_list xs
    end
  end
.

Definition conjunction {A : Type} (f : A -> bool) (l : list A) : bool :=
  fold_left (fun b x => b && f x) l true
.

Definition set_of_list {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (l : list A) : set A :=
  fold_right (fun x s => if set_mem dec x s then s else x :: s) nil l.