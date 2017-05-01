Require Export Disk.
Require Import Implements.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

Module DSpec.
  Record State :=
    Disk { sdisk : disk }.

  Lemma state_eq : forall (state state':State),
      size (sdisk state) = size (sdisk state') ->
      (forall a, sdisk state a = sdisk state' a) ->
      state = state'.
  Proof.
    intros.
    destruct state, state'; simpl in *; f_equal.
    destruct sdisk0, sdisk1.
    simpl in *; subst.
    assert (diskMem = diskMem0).
    extensionality a; auto.
    subst.
    assert (diskMem_domain = diskMem_domain0).
    apply proof_irrelevance.
    subst.
    auto.
  Qed.

  Definition Read a : Semantics block :=
    StepRel (fun state r state' =>
               match sdisk state a with
               | Some v0 => r = v0
               | None => True
               end /\ state' = state).

  Definition Write a b : Semantics unit :=
    StepRel (fun state r state' =>
               state' = Disk (diskUpd (sdisk state) a b) /\ r = tt).

End DSpec.
