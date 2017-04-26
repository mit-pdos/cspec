Require Export Disk.
Require Import Implements.
Require Import FunctionalExtensionality.

Module DSpec.
  Record State :=
    Disk { sdisk : disk }.

  Lemma state_eq : forall (state state':State),
      (forall a, sdisk state a = sdisk state' a) ->
      state = state'.
  Proof.
    intros.
    destruct state, state'; simpl in *; f_equal.
    extensionality a.
    eauto.
  Qed.

  Definition Read a : Semantics block :=
    StepRel (fun state r state' =>
               match sdisk state a with
               | Some v0 => r = v0
               | None => True
               end /\ state' = state).

  Definition Write a b : Semantics unit :=
    StepRel (fun state r state' =>
               match sdisk state a with
               | Some v0 => state' = Disk (upd (sdisk state) a b)
               | None => state' = state
               end /\ r = tt).

End DSpec.
