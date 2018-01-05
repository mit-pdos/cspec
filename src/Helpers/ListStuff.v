Require Import Omega.
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

Lemma pad_is_append : forall n `(l : list T) v,
  pad l n v = l ++ repeat v (n - length l).
Proof.
  induction n; simpl; intros.
  - rewrite app_nil_r; eauto.
  - destruct l; simpl.
    + rewrite IHn; simpl. replace (n - 0) with n by omega. reflexivity.
    + rewrite IHn. eauto.
Qed.

Lemma repeat_app : forall n m `(x : T),
  repeat x (n + m) = repeat x n ++ repeat x m.
Proof.
  induction n; simpl; eauto; intros.
  f_equal. eauto.
Qed.

Lemma repeat_tl : forall n `(x : T),
  repeat x (S n) = repeat x n ++ [x].
Proof.
  induction n; simpl; eauto; intros.
  f_equal. rewrite <- IHn. reflexivity.
Qed.

Lemma rev_repeat : forall n T (x : T),
  rev (repeat x n) = repeat x n.
Proof.
  induction n; simpl; eauto; intros.
  rewrite IHn.
  rewrite <- repeat_tl.
  reflexivity.
Qed.

Lemma length_list_upd: forall `(l: list T) i d,
  Datatypes.length (list_upd l i d) = Datatypes.length l.
Proof.
  induction l; intros; simpl.
  + auto.
  + destruct i.
    replace (d::l) with ([d]++l) by auto.
    apply app_length.
    replace (a :: (list_upd l i d)) with ([a] ++ (list_upd l i d)) by auto.
    rewrite app_length. simpl.
    rewrite IHl; auto.
Qed.