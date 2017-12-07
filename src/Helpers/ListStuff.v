Require Import List.
Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Fixpoint pad T (l : list (option T)) len : list (option T) :=
  match len with
  | O => l
  | S len' =>
    match l with
    | x :: l' =>
      x :: pad l' len'
    | nil =>
      None :: pad nil len'
    end
  end.

Fixpoint list_upd T (l : list (option T)) (idx : nat) (v : option T) :=
  match l with
  | nil => nil
  | x :: l' =>
    match idx with
    | O => v :: l'
    | S idx' => x :: list_upd l' idx' v
    end
  end.
