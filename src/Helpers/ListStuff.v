Require Import List.
Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Fixpoint pad `(l : list T) len val : list T :=
  match len with
  | O => l
  | S len' =>
    match l with
    | x :: l' =>
      x :: pad l' len' val
    | nil =>
      val :: pad nil len' val
    end
  end.

Fixpoint list_upd `(l : list T) (idx : nat) (v : T) :=
  match l with
  | nil => nil
  | x :: l' =>
    match idx with
    | O => v :: l'
    | S idx' => x :: list_upd l' idx' v
    end
  end.
