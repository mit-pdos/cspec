Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailServerLockAbsAPI.


Module MailServerLockAbsImpl <: LayerImpl MailServerLockAbsAPI MailServerAPI.

  Definition absR (s1 : MailServerLockAbsAPI.State) (s2 : MailServerAPI.State) :=
    MailServerLockAbsAPI.maildir s1 = s2.

  Definition compile_ts (ts : @threads_state MailServerAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : @threads_state MailServerAPI.opT),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Hint Extern 1 (MailServerAPI.step _ _ _ _ _ _) => econstructor.

  Theorem absR_ok :
    op_abs absR MailServerLockAbsAPI.step MailServerAPI.step.
  Proof.
    unfold op_abs; intros.
    unfold absR in *.
    inversion H0; clear H0; subst; repeat sigT_eq.
    all: eauto.
  Qed.

  Hint Resolve absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR
        MailServerLockAbsAPI.initP
        MailServerLockAbsAPI.step
        MailServerAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eexists; intuition idtac.
    eapply trace_incl_abs; eauto.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailServerLockAbsAPI.initP s1 ->
      absR s1 s2 ->
      MailServerAPI.initP s2.
  Proof.
    eauto.
  Qed.

End MailServerLockAbsImpl.
