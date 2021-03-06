Require Import ConcurExec.
Require Import Morphisms.
Require Import ProofAutomation.
Require Import Helpers.ListStuff.
Require Import List.
Require Import Omega.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Inclusion of traces across state abstraction *)

Section StateAbstraction.

  Variable OpLo : Type -> Type.

  Variable StateLo : Type.
  Variable StateHi : Type.
  Variable absR : StateLo -> StateHi -> Prop.

  Variable lo_step : OpSemantics OpLo StateLo.
  Variable hi_step : OpSemantics OpLo StateHi.

  Hint Constructors exec_tid.

  Definition op_abs := forall T (op : OpLo T) s1 s1' s2 tid r evs,
    absR s1 s2 ->
    lo_step op tid s1 r s1' evs ->
      exists s2',
        absR s1' s2' /\
        hi_step op tid s2 r s2' evs.

  Variable op_abs_holds : op_abs.

  Theorem atomic_exec_abs : forall `(p : proc OpLo T) s1 s1' s2 tid r evs,
    absR s1 s2 ->
    atomic_exec lo_step p tid s1 r s1' evs ->
      exists s2',
        absR s1' s2' /\
        atomic_exec hi_step p tid s2 r s2' evs.
  Proof.
    intros.
    generalize dependent s2.
    induct H0; eauto.
    - edestruct IHatomic_exec1; intuition eauto.
      edestruct IHatomic_exec2; intuition eauto.
    - eapply op_abs_holds in H; eauto; deex.
      eexists; eauto.
    - edestruct IHatomic_exec; intuition eauto.
  Qed.

  Theorem exec_tid_abs : forall `(p : proc OpLo T) s1 s1' s2 tid res spawned evs,
    absR s1 s2 ->
    exec_tid lo_step tid s1 p s1' res spawned evs ->
      exists s2',
        absR s1' s2' /\
        exec_tid hi_step tid s2 p s2' res spawned evs.
  Proof.
    intros.
    induct H0; eauto.
    - eapply op_abs_holds in H0; eauto; deex.
      eexists; eauto.
    - eapply atomic_exec_abs in H0; eauto; deex.
      eexists; eauto.
  Qed.

  Theorem trace_incl_abs :
    forall s1 s2 (ts : threads_state OpLo) tr,
      absR s1 s2 ->
      exec lo_step s1 ts tr ->
      exec hi_step s2 ts tr.
  Proof.
    intros.
    generalize dependent s2.
    induct H0; eauto.
    - eapply exec_tid_abs in H3; propositional; eauto.
  Qed.

End StateAbstraction.
