Require Import ConcurProc.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import List.
Require Import Omega.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Inclusion of traces across state abstraction *)

Section StateAbstraction.

  Variable opLoT : Type -> Type.
  Variable opHiT : Type -> Type.

  Variable StateLo : Type.
  Variable StateHi : Type.
  Variable absR : StateLo -> StateHi -> Prop.

  Variable lo_step : OpSemantics opLoT StateLo.
  Variable hi_step : OpSemantics opLoT StateHi.

  Definition op_abs := forall `(op : opLoT T) s1 s1' s2 tid r,
    absR s1 s2 ->
    lo_step op tid s1 r s1' ->
      exists s2',
        absR s1' s2' /\
        hi_step op tid s2 r s2'.

  Variable op_abs_holds : op_abs.

  Theorem atomic_exec_abs : forall `(p : proc opLoT opHiT T) s1 s1' s2 tid r evs,
    absR s1 s2 ->
    atomic_exec lo_step p tid s1 r s1' evs ->
      exists s2',
        absR s1' s2' /\
        atomic_exec hi_step p tid s2 r s2' evs.
  Proof.
    intros.
    generalize dependent s2.
    induction H0; intros.
    all: try solve [ eexists; eauto ].
    - edestruct IHatomic_exec1; intuition eauto.
      edestruct IHatomic_exec2; intuition eauto.
    - eapply op_abs_holds in H; eauto; deex.
      eexists; eauto.
    - edestruct IHatomic_exec; intuition eauto.
  Qed.

  Theorem exec_tid_abs : forall `(p : proc opLoT opHiT T) s1 s1' s2 tid res evs,
    absR s1 s2 ->
    exec_tid lo_step tid s1 p s1' res evs ->
      exists s2',
        absR s1' s2' /\
        exec_tid hi_step tid s2 p s2' res evs.
  Proof.
    intros.
    induction H0.
    all: try solve [ eexists; eauto ].
    - eapply op_abs_holds in H0; eauto; deex.
      eexists; eauto.
    - eapply atomic_exec_abs in H0; eauto; deex.
      eexists; eauto.
    - destruct IHexec_tid; intuition eauto.
  Qed.

  Theorem trace_incl_abs :
    forall s1 s2 (ts : @threads_state opLoT opHiT) tr,
      absR s1 s2 ->
      exec lo_step s1 ts tr ->
      exec hi_step s2 ts tr.
  Proof.
    intros.
    generalize dependent s2.
    induction H0; intros.
    - eapply exec_tid_abs in H0; eauto; deex.
      eapply ExecOne with (tid := tid); eauto.
    - eapply ExecEmpty; eauto.
  Qed.

End StateAbstraction.
