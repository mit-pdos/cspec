Require Export FunctionalExtensionality.

Require Import Helpers.Automation.

Global Set Implicit Arguments.

(* [mem A V] is a partial function from A to V, which we interpret as a very
general type of memory with addresses of type A and values of type V. *)
Definition mem A V := A -> option V.
Definition empty_mem {A V} : @mem A V := fun _ => None.

(* This enables Coq's generalization feature: definitions will use [`(m: mem A
V)] (note the backtic); A and V, even if not bound, will be added as parameters
before [m]. By default no variables can be generalized; [Generalizable
Variables] allows to add identifers that are legal to generalize. *)
Global Generalizable Variables A V.

Section Memories.

  Variable A:Type.
  Variable V:Type.

  Implicit Type (m:mem A V).

  Definition mem_union m1 m2 : mem A V :=
    fun a => match m1 a with
          | Some a => Some a
          | None => m2 a
          end.

  Definition mem_disjoint m1 m2 :=
    forall a v1 v2,
      m1 a = Some v1 ->
      m2 a = Some v2 ->
      False.

  Theorem mem_union_comm : forall m1 m2,
      mem_disjoint m1 m2 ->
      mem_union m1 m2 = mem_union m2 m1.
  Proof.
    unfold mem_disjoint, mem_union; intuition.
    extensionality a.
    destruct matches; intuition.
    exfalso; eauto.
  Qed.

  Theorem mem_disjoint_comm : forall m1 m2,
      mem_disjoint m1 m2 ->
      mem_disjoint m2 m1.
  Proof.
    firstorder.
  Qed.

  Theorem mem_disjoint_from_union_1 : forall m1 m2 m3,
      mem_disjoint (mem_union m1 m2) m3 ->
      mem_disjoint m1 m3.
  Proof.
    unfold mem_disjoint, mem_union; intros.
    specialize (H a v1 v2); simpl_match; intuition.
  Qed.

  Theorem mem_disjoint_from_union_2 : forall m1 m2 m3,
      mem_disjoint (mem_union m1 m2) m3 ->
      mem_disjoint m2 m3.
  Proof.
    unfold mem_disjoint, mem_union; intros.
    case_eq (m1 a); intros.
    specialize (H a v v2); simpl_match; intuition.
    specialize (H a v1 v2); simpl_match; intuition.
  Qed.

  Theorem mem_disjoint_both_to_union : forall m1 m2 m3,
      mem_disjoint m1 m2 ->
      mem_disjoint m1 m3 ->
      mem_disjoint m1 (mem_union m2 m3).
  Proof.
    unfold mem_disjoint, mem_union; intros.
    specialize (H a).
    specialize (H0 a).
    destruct (m2 a); eauto.
  Qed.

  Theorem mem_union_assoc : forall m1 m2 m3,
      mem_disjoint m1 m2 ->
      mem_disjoint m1 m3 ->
      mem_disjoint m2 m3 ->
      mem_union (mem_union m1 m2) m3 = mem_union m1 (mem_union m2 m3).
  Proof.
    unfold mem_union, mem_disjoint; intros.
    extensionality a.
    destruct matches.
  Qed.

  Lemma mem_union_empty : forall m,
      mem_union empty_mem m = m.
  Proof.
    intros.
    extensionality a.
    reflexivity.
  Qed.

End Memories.
