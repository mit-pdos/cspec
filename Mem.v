Require Export EquivDec.
Require Export FunctionalExtensionality.
Require Import Automation.

Set Implicit Arguments.

Definition mem A {AEQ:EqDec A eq} V := A -> option V.

Arguments mem A {AEQ} V.

Section Memories.

  Variable A:Type.
  Context {AEQ:EqDec A eq}.
  Variable V:Type.

  Implicit Type (m:mem A V).

  Definition mem_union m1 m2 : mem A V :=
    fun a =>
      match m1 a with
      | Some v => Some v
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
    specialize (H a).
    destruct matches; intuition.
    exfalso; eauto.
  Qed.

  Theorem mem_disjoint_comm : forall m1 m2,
      mem_disjoint m1 m2 ->
      mem_disjoint m2 m1.
  Proof.
    firstorder.
  Qed.

  Definition upd m a v : mem A V :=
    fun a' => if AEQ a a' then Some v else m a'.

  Theorem upd_eq : forall m a v,
      upd m a v a = Some v.
  Proof.
    unfold upd; intros.
    destruct matches.
  Qed.

  Theorem upd_neq : forall m a v a',
      a <> a' ->
      upd m a v a' = m a'.
  Proof.
    unfold upd; intros.
    destruct matches.
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
    repeat match goal with
           | [ H: forall (a:A), _ |- _ ] =>
             specialize (H a)
           end.
    destruct matches.
  Qed.

  Section EmptyMemory.

    Definition emptyMem : mem A V :=
      fun _ => None.

    Theorem mem_union_empty_r : forall m,
        mem_union m emptyMem = m.
    Proof.
      unfold mem_union, emptyMem; intros.
      extensionality a.
      destruct matches.
    Qed.

    Theorem mem_union_empty_l : forall m,
        mem_union emptyMem m = m.
    Proof.
      unfold mem_union, emptyMem; intros; auto.
    Qed.

    Theorem mem_disjoint_empty : forall m,
        mem_disjoint m emptyMem.
    Proof.
      unfold mem_disjoint, emptyMem; intros; congruence.
    Qed.

  End EmptyMemory.

End Memories.

Arguments emptyMem {A AEQ V}.

Hint Rewrite upd_eq : upd.
Hint Rewrite upd_neq using (solve [ auto ]) : upd.
