Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.

Module Lab0Compare.
  
Import ListNotations.

(* These exercises are warmups about natural number comparison. 
 *
 * Author: Eddie Kohler.  
 * Source: https://github.com/readablesystems/cs260r-17
 *
 * Finish this file; the exercises are marked with EXERCISE.
 *)

Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.

Module Lab0Compare.

  Import ListNotations.

  (* COMPARISON PROPOSITIONS
     `n < m` is a proposition that's True if `n` is less than `m`, and
     False otherwise.
     Similarly for `n = m`, `n > m`.
     Comparison propositions are useful during proofs. Like all propositions
     (statements of kind `Prop`), they are ignored when Coq is compiled to
     efficient executable code.

     COMPARISON OBJECTS (SETS)
     `n ?= m` is a function that takes two `nat`s and returns an object
     of type `comparison`.
     `n ?= m` is `Lt` if `n` is less than `m`, `Eq` if they are equal, and
     `Gt` if `n` is greater than `m`.
     Comparison object functions are useful for executable code.

     The library has named lemmas showing that the two notions of comparison
     mean the same thing. *)

  (* Example computations *)
  Eval compute in 1 < 2.
  Eval compute in 2 < 1.
  Eval compute in 1 ?= 2.

  (* Look up some facts about comparison notation *)
  Locate "_ ?= _".
  Check Nat.compare.
  Print Nat.compare.
  Check comparison.

  (* Look up some comparison lemmas *)
  Search (_ ?= _).
  Search (_ ?= _ = Lt -> _ < _).

  (* Prove our own version of `Lt => <`.
     Demonstrate several tactics. *)
  Lemma my_compare_Lt_lt (n m:nat):
    n ?= m = Lt -> n < m.
  Proof.
    intros.
    Search (_ ?= _ = Lt -> _ < _).
    apply nat_compare_Lt_lt.
    auto.
    (* we're done but *) Restart.

    (* this works too: *)
    intros.
    apply nat_compare_Lt_lt in H.
      (* Quiz: how's that different? *)
    auto.
    Restart.

    (* all at once: *)
    apply nat_compare_Lt_lt.
    Restart.

    (* `apply` can take a full expression: *)
    intros.
    apply (nat_compare_Lt_lt n m H).
  Qed.



  (* EXERCISE: Prove this lemma. *)
  Lemma nat_compare_Lt_gt (n m:nat):
    n ?= m = Lt -> m > n.
  Proof.
  (* If you want to skip this exercise for now, replace `Abort`
     with `Admitted`. But remember to finish it! You want to end
     with `Qed`. *)
  Abort.


  (* Coq provides a powerful tactic `omega` that knows a lot about
     arithmetic---but not everything. Let's see how smart it is. *)

  Lemma arithmetic1 (n m:nat):
    100 < n -> 30 < 3 * m -> 110 < n + m.
  Proof.
    (* Without `omega`, look what we'd need.
       Useful to know all the lemmas exist, but a pain. *)
    intros.
    simpl in H0.
    Search (_ + 0).
    rewrite <- plus_n_O in H0.
    Search (_ + (_ + _)).
    rewrite <- plus_assoc_reverse in H0.
    assert (10 < m).
      (* Now we'll prove by contradiction that m > 10. *)
      Search (~ _ >= _ -> _ < _).
      apply not_ge.
      intro. (* Because `~ (10 >= m)` means `10 >= m -> False`. *)
      unfold ge in H1. (* `ge`/`>=` is an abbreviation for `le`/`<=`,
                          so there are more lemmas about `<=`. *)
      Search (_ <= _ -> _ + _ <= _ + _).
      assert (m + m + m <= 10 + 10 + 10).
        apply plus_le_compat; auto.
        apply plus_le_compat; auto.
      simpl in H2.
      Search (_ <= _ -> ~ _ > _).
      apply le_not_gt in H2.
      unfold gt in H2.
      contradiction.
    Search (_ + _ < _ + _).
    apply (plus_lt_compat 100 n 10 m).
    auto.
    auto.
    Restart.

    (* But `omega`, on the other hand! *)
    omega.
  Qed.


  (* DECIDABILITY *)
  (* Types like `{A} + {B}` represent cases where (at least) one of two
     propositions hold. For instance, given two natural numbers,
     n and m, we know that one of `n < m`, `n = m`, `m < n` holds.
     This is represented by `lt_eq_lt_dec`: *)
  Check lt_eq_lt_dec.
  (* Decidability propositions are especially useful for `destruct`,
     as you'll see now. *)

  (* EXERCISE *)
  Lemma lt_or_le (n m:nat):
    n < m \/ m <= n.
  Proof.
    destruct (lt_eq_lt_dec n m).
    destruct s.
    (* You now have three cases. `omega` could complete each case, but
       you should use `omega` AT MOST ONCE. Use `left`, `right`, `auto`,
       etc. *)
  Abort.


  (* Let's prove our own decidability proposition, which will decide
     comparison propositions and objects simultaneously. *)

  Lemma compare_dec (n m:nat):
    {n < m /\ n ?= m = Lt}
    + {n = m /\ n ?= m = Eq}
    + {n > m /\ n ?= m = Gt}.
  Proof.
    (* EXERCISE: Complete the proof. Use `Search` to find the tactics
       that link `?=` with comparison propositions. *)
  Abort.


  (* An example proof using `compare_dec` (redundant with the standard library) *)
  Lemma nat_compare_Lt_lt (n m:nat):
    n ?= m = Lt -> n < m.
  Proof.
    intros. destruct (compare_dec n m). destruct s.
    - (* Case 1: < *) destruct a. auto.
    - (* Case 2: = *) destruct a. rewrite H in H1. discriminate.
    - (* Case 3: > *) destruct a. rewrite H in H1. discriminate.
  Qed.


  (* EXERCISE: Use `compare_dec` to prove: *)
  Lemma lt_eq_Lt (n m p:nat):
    n < m -> p = m -> n ?= p = Lt.
  Proof.
    (* Use tactic `destruct` to unpack a logical-and hypothesis. *)
    (* Don't forget `omega` knows a lot about arithmetic. *)
  Abort.


  (* Working with `compare_dec` is kind of irritating; there's
     a lot of make-work: you're always destructing `s`.
     We can make it a lot easier by *writing our own tactic.*
     After this statement, we can say `destruct_compare n m` instead
     of `destruct (compare_dec n m); try destruct s; ...`. *)
  Ltac destruct_compare n m :=
    let Hlt := fresh "Hlt" in
    let Hc := fresh "Hc" in
    let H := fresh "Hp" in
    destruct (compare_dec n m) as [Hlt | Hlt];
    try destruct Hlt as [Hlt | Hlt];
    destruct Hlt as [H Hc].


  (* EXERCISE: Use `destruct_compare` to prove: *)
  Lemma gt_Gt_Gt (n m p:nat):
    n > m -> m ?= p = Gt -> n ?= p = Gt.
  Proof.
    (* `destruct_compare` may not lead to the shortest possible
       proof, but it does have the advantage that there's fewer
       lemma names to remember -- `destruct_compare` introduces
       a lot of facts about comparison all at once.

       You will need a lemma about greater-than's transitivity.
       Coq, of course, has one already. You can't `apply` it
       directly -- you'll need to supply arguments:
       `apply (LEMMA_NAME ARG1 ARG2 ARG3 HYPOTHESIS) in ...`. *)
  Abort.

End Lab0Compare.
