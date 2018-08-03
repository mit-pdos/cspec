Require Import CSPEC.
Require Import MailboxAPI.
Require Import MailFSAPI.
Require Import MailFSStringAbsAPI.
Require Import MailServerAPI.
Require Import MailboxTmpAbsAPI.


Module MailFSStringAbsImpl' <:
  HLayerImplAbsT MailFSOp
    MailFSStringAbsState MailFSStringAbsAPI
    MailboxTmpAbsState MailFSAPI.

  Definition dirR (d1 : MailFSStringAbsState.dir_contents)
                  (d2 : MailServerState.dir_contents) : Prop :=
    d1 = FMap.map_keys (fun '(tid, fn) => encode_tid_fn tid fn) d2.

  Definition absR (s1 : MailFSStringAbsState.State) (s2 : MailboxTmpAbsState.State) :=
    dirR (MailFSStringAbsState.maildir s1) (MailboxTmpAbsState.maildir s2) /\
    dirR (MailFSStringAbsState.tmpdir  s1) (MailboxTmpAbsState.tmpdir  s2) /\
    MailFSStringAbsState.locked s1 = MailboxTmpAbsState.locked s2.

  Hint Extern 1 (MailFSAPI.step _ _ _ _ _ _) => econstructor.

  Lemma dirR_empty : dirR FMap.empty FMap.empty.
  Proof.
    unfold dirR; intros.
    symmetry.
    apply FMap.mapsto_empty_def; intros.
    unfold not; intros.
    apply FMap.map_keys_mapsto' in H; propositional.
  Qed.

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
    unfold dirR; intros; subst.
    rewrite FMap.map_keys_add; eauto.
  Qed.

  Lemma dirR_remove :
    forall d1 d2 tid fn,
      dirR d1 d2 ->
      dirR (FMap.remove (encode_tid_fn tid fn) d1)
           (FMap.remove (tid, fn) d2).
  Proof.
    unfold dirR; intros; subst.
    rewrite FMap.map_keys_remove; eauto.
  Qed.

  Lemma dirR_is_permutation_key :
    forall d1 d2 l,
      dirR d1 d2 ->
      FMap.is_permutation_key l d1 ->
      FMap.is_permutation_key (map decode_tid_fn l) d2.
  Proof.
    unfold dirR, FMap.is_permutation_key.
    split; subst; intros.
    - eapply in_map_iff in H; deex.
      eapply H0 in H1.
      eapply FMap.map_keys_in' in H1; deex.
      destruct k'.
      rewrite encode_decode_tid_fn; eauto.
    - destruct x.
      eapply FMap.map_keys_in in H.
      eapply H0 in H.
      eapply in_map_iff.
      eexists; split; eauto.
      rewrite encode_decode_tid_fn; eauto.
  Qed.

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
    all:
      solve [ eexists; split; [ split | econstructor ]; simpl; intuition eauto ].
  Qed.

  Definition initP_map (s1: MailFSStringAbsState.State) :
    {s2:MailboxTmpAbsState.State |
     MailFSStringAbsState.initP s1 -> absR s1 s2 /\ MailboxTmpAbsState.initP s2}.
  Proof.
    unfold MailFSStringAbsState.initP, MailboxTmpAbsState.initP, absR.
    destruct s1; simpl.
    exists_econstructor; (intuition eauto); propositional.
  Qed.

End MailFSStringAbsImpl'.

Module MailFSStringAbsImpl :=
  HLayerImplAbs MailFSOp
    MailFSStringAbsState MailFSStringAbsAPI
    MailboxTmpAbsState MailFSAPI
    MailFSStringAbsImpl'.

Module MailFSStringAbsImplH' :=
  LayerImplAbsHT
    MailFSOp
    MailFSStringAbsState MailFSStringAbsAPI
    MailboxTmpAbsState MailFSAPI
    MailFSStringAbsImpl'
    UserIdx.

Module MailFSStringAbsImplH :=
  LayerImplAbs MailFSHOp
    MailFSStringAbsHState MailFSStringAbsHAPI
    MailboxTmpAbsHState MailFSHAPI
    MailFSStringAbsImplH'.
