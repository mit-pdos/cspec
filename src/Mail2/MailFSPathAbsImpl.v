Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailServerDirAPI.
Require Import MailboxTmpAbsAPI.
Require Import MailFSAPI.
Require Import MailFSPathAbsAPI.

Import ListNotations.
Open Scope string.

Module MailFSPathAbsImpl <: LayerImpl MailFSPathAbsAPI MailFSAPI.

  Definition absR (s1 : MailFSPathAbsAPI.State) (s2 : MailFSAPI.State) := 
    forall tid fn, FMap.In ("tmp", (tid, fn)) s1 <-> FMap.In (tid, fn) (MailboxTmpAbsAPI.tmpdir s2) /\
              FMap.In ("maildir", (tid, fn)) s1 <-> FMap.In (tid, fn) (MailboxTmpAbsAPI.maildir s2).
                                              
  Definition compile_ts (ts : @threads_state MailFSAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : @threads_state MailFSAPI.opT),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Hint Extern 1 (MailFSAPI.step _ _ _ _ _ _) => econstructor.

  Theorem absR_ok :
    op_abs absR MailFSPathAbsAPI.step MailFSAPI.step.
  Proof.
    unfold op_abs, absR; intros.
    destruct s1; simpl in *; subst.
    inversion H0; clear H0; subst; repeat sigT_eq.
    all: eauto 10.
  Admitted.

  Hint Resolve absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR
        MailFSPathAbsAPI.initP
        MailFSPathAbsAPI.step
        MailFSAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eexists; intuition idtac.
    eapply trace_incl_abs; eauto.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailFSPathAbsAPI.initP s1 ->
      absR s1 s2 ->
      MailFSAPI.initP s2.
  Proof.
    eauto.
  Qed.
  


End MailFSPathAbsImpl.
