Require Import POCS.
Require Import MailboxAPI.
Require Import MailFSAPI.
Require Import MailFSStringAbsAPI.
Require Import MailServerDirAPI.
Require Import MailboxTmpAbsAPI.


Module MailFSStringAbsImpl <: LayerImpl MailFSStringAbsAPI MailFSAPI.

  Definition dirR (d1 : MailFSStringAbsAPI.dir_contents)
                  (d2 : MailServerDirAPI.dir_contents) : Prop :=
    d1 = FMap.map_keys (fun '(tid, fn) => encode_tid_fn tid fn) d2.

  Definition absR (s1 : MailFSStringAbsAPI.State) (s2 : MailFSAPI.State) :=
    dirR (MailFSStringAbsAPI.maildir s1) (MailboxTmpAbsAPI.maildir s2) /\
    dirR (MailFSStringAbsAPI.tmpdir  s1) (MailboxTmpAbsAPI.tmpdir  s2).

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
    op_abs absR MailFSStringAbsAPI.step MailFSAPI.step.
  Proof.
    unfold op_abs, absR; intros.
    destruct s1; simpl in *; subst.
(*
    inversion H0; clear H0; subst; repeat sigT_eq.
    all: eauto 10.
  Qed.
*)
  Admitted.

  Hint Resolve absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR
        MailFSStringAbsAPI.initP
        MailFSStringAbsAPI.step
        MailFSAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eexists; intuition idtac.
    eapply trace_incl_abs; eauto.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailFSStringAbsAPI.initP s1 ->
      absR s1 s2 ->
      MailFSAPI.initP s2.
  Proof.
    eauto.
  Qed.

End MailFSStringAbsImpl.
