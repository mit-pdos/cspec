Require Import POCS.
Require Import MailboxAPI.
Require Import MailboxTmpAbsAPI.
Require Import MailServerLockAbsAPI.


Module MailboxTmpAbs <: LayerImpl MailboxTmpAbsAPI MailboxAPI.

  Definition absR (s1 : MailboxTmpAbsAPI.State) (s2 : MailboxAPI.State) :=
    MailboxTmpAbsAPI.maildir s1 = MailServerLockAbsAPI.maildir s2 /\
    (MailboxTmpAbsAPI.locked s1 = false <-> MailServerLockAbsAPI.locked s2 = None).

  Definition compile_ts (ts : @threads_state MailboxAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : @threads_state MailboxAPI.opT),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.

  Theorem absR_ok :
    op_abs absR MailboxTmpAbsAPI.step MailboxAPI.step.
  Proof.
    unfold op_abs, absR; intros.
    destruct s1.
    destruct s2.
    intuition idtac.
    simpl in *; subst.
    inversion H0; clear H0; subst; repeat sigT_eq.
    all: simpl.
    all: eexists; split; [ | eauto ].
    all: simpl.
    all: try intuition congruence.
    all: try ( destruct locked0; try intuition congruence ).
    all: eauto.
    simpl.
    intuition congruence.
  Qed.

  Hint Resolve absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR
        MailboxTmpAbsAPI.initP
        MailboxTmpAbsAPI.step
        MailboxAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eexists; intuition idtac.
    eapply trace_incl_abs; eauto.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailboxTmpAbsAPI.initP s1 ->
      absR s1 s2 ->
      MailboxAPI.initP s2.
  Proof.
    eauto.
  Qed.

End MailboxTmpAbs.
