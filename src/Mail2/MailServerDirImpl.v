Require Import POCS.
Require Import MailServerAPI.
Require Import MailServerDirAPI.

Import List.ListNotations.

Lemma is_permutation_map_set_add: forall s m (fn: (nat*nat)) d,
    ~ FMap.In fn m ->
    FMap.is_permutation_val (FSet.elements s) m ->
    FMap.is_permutation_val (FSet.elements (FSet.add d s)) (FMap.add fn d m).
Proof.
  intros.
  unfold FSet.elements, FSet.add in *.
  assert (FMap.is_permutation (d:: (FMap.keys s)) (FMap.keys (FMap.add d tt s))).
  apply FMap.is_permutation_cons_add_key.
  apply FMap.permutation_is_permutation_val with (l2 := (d :: (FMap.keys s))); auto.
  apply FMap.is_permutation_val_add; auto.
Qed.

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
    inversion H0; clear H0; simpl in *; subst; repeat sigT_eq.
    all: unfold absR in *.
    - exists (FSet.add m s2).
      split; [ | constructor].
      apply is_permutation_map_set_add; eauto.
    - eexists; intuition eauto; constructor.
      eapply FMap.permutation_val_is_permutation in H; eauto.
    - eexists; intuition eauto; constructor.
    - eexists; intuition eauto; constructor.
  Qed.

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
