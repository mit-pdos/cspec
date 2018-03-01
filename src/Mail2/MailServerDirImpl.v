Require Import POCS.
Require Import MailServerAPI.
Require Import MailServerDirAPI.


Module MailServerDir <: LayerImpl MailServerDirAPI MailServerAPI.

  Definition absR (s1 : MailServerDirAPI.State) (s2 : MailServerAPI.State) :=
    FMap.is_permutation_val (FSet.elements s2) s1.

  Definition compile_ts (ts : @threads_state MailServerAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : @threads_state MailServerAPI.opT),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Theorem absR_ok :
    op_abs absR MailServerDirAPI.step MailServerAPI.step.
  Proof.
    unfold op_abs; intros.
(*
    destruct s1; inversion H; clear H.
    simpl in *; subst.
    unfold absR.
    destruct op; inversion H0; clear H0; repeat sigT_eq.
    all: eexists; intuition eauto; constructor.
  Qed.
*)
  Admitted.

  Hint Resolve absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR
        MailServerDirAPI.initP MailServerDirAPI.step
        MailServerAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, traces_match_abs; intros.
    eexists; intuition idtac.
    eapply trace_incl_abs; eauto.
    eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailServerDirAPI.initP s1 ->
      absR s1 s2 ->
      MailServerAPI.initP s2.
  Proof.
    eauto.
  Qed.

End MailServerDir.
