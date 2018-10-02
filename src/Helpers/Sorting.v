Require Import Permutation.
Require Import Recdef.
Require List.

Import List.ListNotations.
Open Scope list.

Section Sorting.
  Context {A:Type}.
  Variable lt: A -> A -> bool.
  Infix "<?" := lt (at level 20).

  Fixpoint insert (x: A) (xs: list A) : list A :=
    match xs with
    | nil => [x]
    | x'::xs' => if x <? x'
                 then x::x'::xs'
                 else x'::insert x xs'
    end.

  Hint Constructors Permutation.

  Theorem inserted_permutation : forall x xs,
      Permutation (x::xs) (insert x xs).
  Proof.
    induction xs; simpl; eauto.
    destruct (x <? a); eauto.
  Qed.

  Fixpoint insert_sort (xs: list A) (acc: list A) : list A :=
    match xs with
      | nil => acc
      | x::xs => insert_sort xs (insert x acc)
    end.

  Definition sort xs := insert_sort xs [].

  Theorem insert_sort_permutation : forall xs acc,
      Permutation (xs++acc) (insert_sort xs acc).
  Proof.
    induction xs; intros; simpl.
    - auto.
    - etransitivity; [ | eauto ].
      pose proof (inserted_permutation a acc).
      transitivity (xs ++ a :: acc).
      apply Permutation_cons_app; auto.
      apply Permutation_app; auto.
  Qed.

  Theorem sort_permutation : forall xs,
      Permutation xs (sort xs).
  Proof.
    unfold sort.
    intros.
    replace xs with (xs ++ []) at 1.
    apply insert_sort_permutation.
    rewrite List.app_nil_r; auto.
  Qed.

End Sorting.

Require Import PeanoNat.

Definition sortBy {A} (key: A -> option nat) (xs: list A) : list A :=
  sort (fun x y => Nat.leb (match key x with
                            | Some n => S n
                            | None => 0
                            end)
                           (match key y with
                            | Some n => S n
                            | None => 0
                            end)) xs.

Theorem sortBy_permutation : forall A key (xs: list A),
    Permutation xs (sortBy key xs).
Proof.
  unfold sortBy; intros.
  apply sort_permutation.
Qed.
