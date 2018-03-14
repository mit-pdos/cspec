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

  Lemma dirR_mapsto :
    forall d1 d2 tid fn data,
      dirR d1 d2 ->
      FMap.MapsTo (encode_tid_fn tid fn) data d1 ->
      FMap.MapsTo (tid, fn) data d2.
  Proof.
    unfold dirR; intros; subst.
    eapply FMap.map_keys_mapsto' in H0; deex.
    destruct k'.
    apply encode_tid_eq in H0; inversion H0; clear H0; subst.
    eauto.
  Qed.

  Lemma dirR_mapsto' :
    forall d1 d2 tid fn data,
      dirR d1 d2 ->
      FMap.MapsTo (tid, fn) data d2 ->
      FMap.MapsTo (encode_tid_fn tid fn) data d1.
  Proof.
    unfold dirR; intros; subst.
    eapply FMap.map_keys_mapsto in H0.
    exact H0.
    eauto.
  Qed.

  Lemma dirR_fmap_in :
    forall d1 d2 tid fn,
      dirR d1 d2 ->
      FMap.In (encode_tid_fn tid fn) d1 ->
      FMap.In (tid, fn) d2.
  Proof.
    intros.
    eapply FMap.in_mapsto_exists in H0; destruct H0.
    eapply FMap.mapsto_in.
    eapply dirR_mapsto; eauto.
  Qed.

  Lemma dirR_fmap_in' :
    forall d1 d2 tid fn,
      dirR d1 d2 ->
      FMap.In (tid, fn) d2 ->
      FMap.In (encode_tid_fn tid fn) d1.
  Proof.
    intros.
    eapply FMap.in_mapsto_exists in H0; destruct H0.
    eapply FMap.mapsto_in.
    eapply dirR_mapsto'; eauto.
  Qed.

  Lemma dirR_add :
    forall d1 d2 tid fn data,
      dirR d1 d2 ->
      dirR (FMap.add (encode_tid_fn tid fn) data d1)
           (FMap.add (tid, fn) data d2).
  Proof.
  Admitted.

  Lemma dirR_remove :
    forall d1 d2 tid fn,
      dirR d1 d2 ->
      dirR (FMap.remove (encode_tid_fn tid fn) d1)
           (FMap.remove (tid, fn) d2).
  Proof.
  Admitted.

  Lemma dirR_is_permutation_key :
    forall d1 d2 l,
      dirR d1 d2 ->
      FMap.is_permutation_key l d1 ->
      FMap.is_permutation_key (map decode_tid_fn l) d2.
  Proof.
  Admitted.

  Hint Resolve dirR_fmap_in.
  Hint Resolve dirR_fmap_in'.
  Hint Resolve dirR_mapsto.
  Hint Resolve dirR_add.
  Hint Resolve dirR_remove.
  Hint Resolve dirR_is_permutation_key.

  Theorem absR_ok :
    op_abs absR MailFSStringAbsAPI.step MailFSAPI.step.
  Proof.
    unfold op_abs, absR; intros.
    destruct s1; simpl in *; subst.
    destruct s2; simpl in *; subst.
    intuition idtac.
    inversion H0; clear H0; subst; repeat sigT_eq; simpl in *.
    all: eexists; split; [ split | econstructor ]; simpl.
    all: eauto.
  Qed.

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
