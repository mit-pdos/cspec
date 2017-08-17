Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.

(* Several exercises with a functional data structure (binary search tree) and
 * proofs by induction.
 * 
 * Author: Eddie Kohler.  
 * Source: https://github.com/readablesystems/cs260r-17 
 *
 * Finish this file; the exercises are marked with EXERCISE
 *)

Module Lab0Btree.
  
  Import ListNotations.

  (* These comparison tactics are useful for this module. *)
  Lemma compare_dec (n m:nat):
    {n < m /\ n ?= m = Lt}
    + {n = m /\ n ?= m = Eq}
    + {n > m /\ n ?= m = Gt}.
  Proof.
    destruct (lt_eq_lt_dec n m); try destruct s.
    - left; left; split; auto; apply nat_compare_lt; auto.
    - left; right; split; auto; apply nat_compare_eq_iff; auto.
    - right; split; auto; apply nat_compare_gt; auto.
  Qed.

  Ltac destruct_compare n m :=
    let Hlt := fresh "Hlt" in
    let Hc := fresh "Hc" in
    let Hp := fresh "Hp" in
    destruct (compare_dec n m) as [Hlt | Hlt];
    try destruct Hlt as [Hlt | Hlt];
    destruct Hlt as [Hp Hc].


  (* A `nattree` is a tree of natural numbers, where every internal
     node has an associated number and leaves are empty. There are
     two constructors, L (empty leaf) and I (internal node).
     I's arguments are: left-subtree, number, right-subtree. *)
  Inductive nattree : Set :=
    | L : nattree                                (* Leaf *)
    | I : nattree -> nat -> nattree -> nattree.  (* Internal nodes *)

  (* Some example nattrees. *)
  Definition empty_nattree := L.
  Definition singleton_nattree := I L 0 L.
  Definition right_nattree := I L 0 (I L 1 (I L 2 (I L 3 L))).
  Definition left_nattree := I (I (I (I L 0 L) 1 L) 2 L) 3 L.
  Definition balanced_nattree := I (I L 0 (I L 1 L)) 2 (I L 3 L).
  Definition unsorted_nattree := I (I L 3 (I L 1 L)) 0 (I L 2 L).


  (* Flatten a `nattree` into a list of nats using inorder traversal. *)
  Function flatten (t:nattree) : list nat :=
    match t with
    | L => nil
    | I l n r => flatten l ++ (n :: flatten r)
    end.

  Eval compute in flatten empty_nattree.
  Eval compute in flatten singleton_nattree.
  Eval compute in flatten right_nattree.
  Eval compute in flatten left_nattree.
  Eval compute in flatten balanced_nattree.
  Eval compute in flatten unsorted_nattree.


  (* EXERCISE: Complete this proposition, which should be `True`
     iff `x` is located somewhere in `t` (even if `t` is unsorted,
     i.e., not a valid binary search tree). *)
  Function btree_in (x:nat) (t:nattree) : Prop :=
    False.

  (* EXERCISE: Complete these examples, which show `btree_in` works.
     Hint: The same proof will work for every example.
     End each example with `Qed.`. *)
  Example btree_in_ex1 : ~ btree_in 0 empty_nattree.
    Abort.
  Example btree_in_ex2 : btree_in 0 singleton_nattree.
    Abort.
  Example btree_in_ex3 : btree_in 2 right_nattree.
    Abort.
  Example btree_in_ex4 : btree_in 2 left_nattree.
    Abort.
  Example btree_in_ex5 : btree_in 2 balanced_nattree.
    Abort.
  Example btree_in_ex6 : btree_in 2 unsorted_nattree.
    Abort.
  Example btree_in_ex7 : ~ btree_in 10 balanced_nattree.
    Abort.


  (* EXERCISE: Complete this function, which should return `true`
     iff `x` is in the valid binary search tree `t` (and `false`
     otherwise).

     Note that this function returns `bool` (lower-case `true` and
     `false`), not `Prop` (upper-case `True` and `False`), because
     we imagine using it at execution time, not only in proofs. *)
  Function binsearch (x:nat) (t:nattree) : bool :=
    false.


  (* In the rest of this module you will prove that your `binsearch`
     is correct. There are two parts. First, we prove that if
     `binsearch` returns true, then the searched-for number is in the
     tree. *)

  (* EXERCISE: Complete this lemma, which says that every nat that
     bsearch can find is in the tree. *)
  Lemma binsearch_in {x:nat} {t:nattree}:
    binsearch x t = true -> btree_in x t.
  Proof.
    (* Remember the `destruct_compare n m` tactic! *)
  Abort.


  (* Then, we prove that if the searched-for number is in the
     tree *and the tree is valid binary search tree*, then `binsearch`
     returns true.

     For this we need a definition of “valid binary search tree.”

     It's important to choose a good definition. Think more like a prover
     than an implementer. For proof purposes, use high-level lemmas
     with less-complicated types, and don't worry about traversing the
     tree multiple times. *)

  (* EXERCISE: Complete this proposition, which is True iff every
     number in the tree is `<= ub`. *)
  Function btree_le (t:nattree) (ub:nat) : Prop :=
    True.

  (* EXERCISE: Complete this proposition, which is True iff every
     number in the tree is `>= lb`. *)
  Function btree_ge (t:nattree) (lb:nat) : Prop :=
    True.

  (* EXERCISE: Complete this proposition, which is True iff `t`
     is a valid binary search tree---that is, an in-order traversal
     visits the numbers in increasing order. *)
  Function btree_sorted (t:nattree) : Prop :=
    True.


  (* EXERCISE: Complete this lemma, which says that every element
     of a tree with an upper bound is `<=` that upper bound.

     Note that the arguments are in {curly braces}, not (parens).
     Arguments in curly braces are implicit; Coq will determine
     them from context when the lemma is applied. *)
  Lemma btree_in_le {x:nat} {t:nattree} {ub:nat}:
    btree_in x t -> btree_le t ub -> x <= ub.
  Proof.
    (* You will probably find the `destruct_pairs` tactic useful.
       This tactic unpacks long `and` chains `X /\ Y /\ ...` into
       individual hypotheses. *)
  Abort.

  (* EXERCISE: Complete this lemma, which says that every element
     of a tree with a lower bound is `>=` that lower bound. *)
  Lemma btree_in_ge {x:nat} {t:nattree} {lb:nat}:
    btree_in x t -> btree_ge t lb -> x >= lb.
  Proof.
  Abort.


  (* EXERCISE: Complete this lemma, says which that in a binary
     search tree, smaller elements are in left subtrees. *)
  Lemma btree_sorted_in_left {x:nat} {l:nattree} {y:nat} {r:nattree}:
    btree_sorted (I l y r) -> btree_in x (I l y r) -> x < y
    -> btree_in x l.
  Proof.
  Abort.

  (* EXERCISE: Complete this lemma, which says that in a binary
     search tree, large elements are in right subtrees. *)
  Lemma btree_sorted_in_right {x:nat} {l:nattree} {y:nat} {r:nattree}:
    btree_sorted (I l y r) -> btree_in x (I l y r) -> x > y
    -> btree_in x r.
  Proof.
  Abort.


  (* EXERCISE: Complete the main lemma, which says that `binsearch`
     can find every element in a binary search tree. *)
  Lemma in_binsearch {x:nat} {t:nattree}:
    btree_sorted t -> btree_in x t -> binsearch x t = true.
  Proof.
  Abort.


  (* Finally, we relate the `flatten` function to the tree's contents.
     The proposition `In x l` is True iff `x` is a member of `l`. *)

  (* EXERCISE: Complete this lemma. *)
  Lemma In_btree {x:nat} {t:nattree}:
    btree_in x t <-> In x (flatten t).
  Proof.
  Abort.

End Lab0Btree.
