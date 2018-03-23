Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailServerLockAbsAPI.
Require Import MailServerLockAbsImpl.
Require Import MailboxAPI.
Require Import MailboxImpl.


Module HLayer (l : Layer) <: Layer.

  Definition opT := horizOpT string l.opT.
  Definition State := horizState string l.State.
  Definition step := horizStep string l.step.

  Definition indexValid (u : string) := u = "Alice"%string \/ u = "Bob"%string.

  Definition initP : State -> Prop :=
    horizInitP indexValid l.initP.

End HLayer.


Module MailServerHAPI := HLayer MailServerAPI.
Module MailServerLockAbsHAPI := HLayer MailServerLockAbsAPI.
Module MailboxRestrictedHAPI := HLayer MailboxRestrictedAPI.


Module MailServerH <: LayerImpl MailServerLockAbsHAPI MailServerHAPI.

  Definition absR := horizAbsR string MailServerLockAbsImpl.absR.

  Definition compile_ts (ts : @threads_state MailServerHAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : @threads_state MailServerHAPI.opT),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Theorem absR_ok :
    op_abs absR MailServerLockAbsHAPI.step MailServerHAPI.step.
  Proof.
    eapply horizAbsR_ok.
    apply MailServerLockAbsImpl.absR_ok.
  Qed.

  Hint Resolve absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR MailServerLockAbsHAPI.initP MailServerLockAbsHAPI.step MailServerHAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eexists; intuition idtac.
    eapply trace_incl_abs; eauto.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailServerLockAbsHAPI.initP s1 ->
      absR s1 s2 ->
      MailServerHAPI.initP s2.
  Proof.
    eapply horizAbsR_initP_ok.
    eapply MailServerLockAbsImpl.absInitP.
  Qed.

End MailServerH.


Module MailboxH <: LayerImpl MailServerLockAbsHAPI MailboxRestrictedHAPI.

  Definition compile_op T (op : MailServerLockAbsHAPI.opT T) : proc MailboxRestrictedHAPI.opT T :=
    match op with
    | Slice i op => SliceProc i (AtomicReaderRestricted.compile_op op)
    end.

  