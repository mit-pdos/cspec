Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailFSStringAbsAPI.
Require Import MailFSStringAPI.
Require Import MailFSPathAbsAPI.


Module MailFSPathAbsImpl' <:
  HLayerImplAbsT MailFSStringOp
    MailFSPathAbsState MailFSPathAbsAPI
    MailFSStringAbsState MailFSStringAPI.

  Definition absR (s1 : MailFSPathAbsState.State) (s2 : MailFSStringAbsState.State) :=
    MailFSPathAbsState.locked s1 = MailFSStringAbsState.locked s2 /\
    forall dirname filename contents,
      FMap.MapsTo (dirname, filename) contents (MailFSPathAbsState.fs s1) <->
      ( dirname = tmp_string /\ FMap.MapsTo filename contents (MailFSStringAbsState.tmpdir s2) \/
        dirname = mail_string /\ FMap.MapsTo filename contents (MailFSStringAbsState.maildir s2) ).

  Hint Extern 1 (MailFSStringAPI.step _ _ _ _ _ _) => econstructor.

  Lemma fn_ne : forall (dirname fn1 fn2 : string),
    (dirname, fn1) <> (dirname, fn2) ->
    fn1 <> fn2.
  Proof.
    congruence.
  Qed.

  Lemma tmp_mail_ne_pair : forall (fn1 fn2 : string),
    (tmp_string, fn1) <> (mail_string, fn2).
  Proof.
    intros; intro; apply tmp_mail_ne; congruence.
  Qed.

  Hint Resolve FMap.add_mapsto.
  Hint Resolve FMap.mapsto_add_ne'.
  Hint Resolve fn_ne.
  Hint Resolve tmp_mail_ne_pair.
  Hint Resolve tmp_mail_ne.

  Lemma absR_add_tmp :
    forall fs tmp mail fn data lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      absR (MailFSPathAbsState.mk_state (FMap.add (tmp_string, fn) data fs) lock)
           (MailFSStringAbsState.mk_state (FMap.add fn data tmp) mail lock').
  Proof.
    unfold absR; simpl; intuition subst.
    - eapply FMap.mapsto_add_or in H; intuition subst.
      + inversion H; clear H; subst.
        eauto.
      + eapply H1 in H2; clear H1.
        intuition eauto; subst.
        destruct (filename == fn); try congruence.
        intuition eauto.
    - eapply FMap.mapsto_add_or in H3; intuition subst; eauto.
      eapply FMap.mapsto_add_ne'; try congruence.
      eapply H1; eauto.
    - eapply FMap.mapsto_add_ne'; try congruence; eauto.
      eapply H1; eauto.
  Qed.

  Lemma absR_remove_tmp :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      absR (MailFSPathAbsState.mk_state (FMap.remove (tmp_string, fn) fs) lock)
           (MailFSStringAbsState.mk_state (FMap.remove fn tmp) mail lock').
  Proof.
    unfold absR; simpl; intuition subst.
    - eapply FMap.mapsto_remove in H; intuition subst.
      eapply H1 in H2; clear H1.
      intuition subst.
      destruct (filename == fn); try congruence.
      left; split; try reflexivity.
      eapply FMap.remove_mapsto with (x := fn) in H2; auto.
    - destruct (filename == fn); try congruence; subst.
      eapply FMap.mapsto_remove in H3; intuition subst.
      eapply FMap.mapsto_remove in H3; intuition subst.
      specialize (H1 tmp_string filename contents); simpl in *.
      intuition try congruence.
      eapply FMap.remove_mapsto; congruence.
      exfalso; eauto.
    - specialize (H1 mail_string filename contents); simpl in *.
      intuition try congruence.
      exfalso; eauto.
      eapply FMap.remove_mapsto; eauto.
  Qed.

  Lemma absR_add_mail :
    forall fs tmp mail fn data lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      absR (MailFSPathAbsState.mk_state (FMap.add (mail_string, fn) data fs) lock)
           (MailFSStringAbsState.mk_state tmp (FMap.add fn data mail) lock').
  Proof.
    unfold absR; simpl; intuition subst.
    - eapply FMap.mapsto_add_or in H; intuition subst.
      + inversion H; clear H; subst.
        eauto.
      + eapply H1 in H2; clear H1.
        intuition eauto; subst.
        destruct (filename == fn); try congruence.
        intuition eauto.
    - eapply FMap.mapsto_add_ne'; try congruence; eauto.
      eapply H1; eauto.
    - eapply FMap.mapsto_add_or in H3; intuition subst; eauto.
      eapply FMap.mapsto_add_ne'; try congruence.
      eapply H1; eauto.
  Qed.

  Lemma absR_remove_mail :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      absR (MailFSPathAbsState.mk_state (FMap.remove (mail_string, fn) fs) lock)
           (MailFSStringAbsState.mk_state tmp (FMap.remove fn mail) lock').
  Proof.
    unfold absR; simpl; intuition subst.
    - eapply FMap.mapsto_remove in H; intuition subst.
      eapply H1 in H2; clear H1.
      intuition subst.
      destruct (filename == fn); try congruence.
      right; split; try reflexivity.
      eapply FMap.remove_mapsto with (x := fn) in H2; auto.
    - specialize (H1 tmp_string filename contents); simpl in *.
      intuition try congruence.
      eapply FMap.remove_mapsto; eauto.
      exfalso; eauto.
    - destruct (filename == fn); try congruence; subst.
      eapply FMap.mapsto_remove in H3; intuition subst.
      eapply FMap.mapsto_remove in H3; intuition subst.
      specialize (H1 mail_string filename contents); simpl in *.
      intuition try congruence.
      exfalso; eauto.
      eapply FMap.remove_mapsto; congruence.
  Qed.

  Lemma absR_in_tmp :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      FMap.In fn tmp ->
      FMap.In (tmp_string, fn) fs.
  Proof.
    unfold absR; intros.
    eapply FMap.in_mapsto_exists in H0; destruct H0.
    eapply FMap.mapsto_in.
    eapply H; eauto.
  Qed.

  Lemma absR_mapsto_tmp :
    forall fs tmp mail fn data lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      FMap.MapsTo (tmp_string, fn) data fs ->
      FMap.MapsTo fn data tmp.
  Proof.
    unfold absR; intros.
    eapply H in H0; intuition eauto.
    exfalso; eauto.
  Qed.

  Lemma absR_in_tmp' :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      FMap.In (tmp_string, fn) fs ->
      FMap.In fn tmp.
  Proof.
    unfold absR; intros.
    eapply FMap.in_mapsto_exists in H0; destruct H0.
    eapply FMap.mapsto_in.
    eapply absR_mapsto_tmp; eauto.
  Qed.

  Lemma absR_in_mail :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      FMap.In fn mail ->
      FMap.In (mail_string, fn) fs.
  Proof.
    unfold absR; intros.
    eapply FMap.in_mapsto_exists in H0; destruct H0.
    eapply FMap.mapsto_in.
    eapply H; eauto.
  Qed.

  Lemma absR_mapsto_mail :
    forall fs tmp mail fn data lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      FMap.MapsTo (mail_string, fn) data fs ->
      FMap.MapsTo fn data mail.
  Proof.
    unfold absR; intros.
    eapply H in H0; intuition eauto.
    exfalso; eauto.
  Qed.

  Lemma absR_in_mail' :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      FMap.In (mail_string, fn) fs ->
      FMap.In fn mail.
  Proof.
    intros.
    eapply FMap.in_mapsto_exists in H0; deex.
    eapply FMap.mapsto_in.
    eapply absR_mapsto_mail; eauto.
  Qed.

  Lemma absR_is_permutation_key :
    forall r fs tmp mail lock lock',
      absR (MailFSPathAbsState.mk_state fs lock)
           (MailFSStringAbsState.mk_state tmp mail lock') ->
      FMap.is_permutation_key r
        (MailFSPathAbsAPI.drop_dirname
           (MailFSPathAbsAPI.filter_dir mail_string fs)) ->
      FMap.is_permutation_key r mail.
  Proof.
    intros.
    unfold FMap.is_permutation_key in *.
    intros.
    split; intros.
    + apply H0 in H1.
      eapply MailFSPathAbsAPI.drop_dirname_filter_dir in H1 as Hx.
      unfold absR in *.
      apply FMap.in_mapsto_get in Hx.
      destruct Hx.
      intuition idtac.
      specialize (H3 mail_string x x0) as Hy.
      apply Hy in m.
      intuition; try solve [ exfalso; eauto ].
      simpl in *.
      apply FMap.mapsto_in in H9; auto.
    + unfold absR in *.
      intuition idtac.
      apply FMap.in_mapsto_get in H1.
      destruct H1.
      specialize (H3 mail_string x x0) as Hy.
      intuition; try solve [ exfalso; eauto ].
      simpl in *.
      apply FMap.mapsto_in in H4.
      apply MailFSPathAbsAPI.filter_dir_drop_dirname in H4.
      apply H0 in H4; auto.
  Qed.

  Lemma absR_change_lock :
    forall fs tmp mail lock0 lock1 lock2,
      absR (MailFSPathAbsState.mk_state fs lock0)
           (MailFSStringAbsState.mk_state tmp mail lock1) ->
      absR (MailFSPathAbsState.mk_state fs lock2)
           (MailFSStringAbsState.mk_state tmp mail lock2).
  Proof.
    unfold absR; intuition eauto.
  Qed.

  Hint Resolve absR_add_tmp.
  Hint Resolve absR_remove_tmp.
  Hint Resolve absR_add_mail.
  Hint Resolve absR_remove_mail.
  Hint Resolve absR_in_tmp.
  Hint Resolve absR_in_tmp'.
  Hint Resolve absR_mapsto_tmp.
  Hint Resolve absR_in_mail.
  Hint Resolve absR_in_mail'.
  Hint Resolve absR_mapsto_mail.
  Hint Resolve absR_is_permutation_key.
  Hint Resolve absR_change_lock.

  Theorem absR_ok :
    op_abs absR MailFSPathAbsAPI.step MailFSStringAPI.step.
  Proof.
    unfold op_abs; intros.
    destruct s2; simpl in *; subst.
    inversion H0; clear H0; subst; repeat sigT_eq.
    all:
      try solve [ eexists; split; [ | try econstructor ]; simpl; intuition eauto 10 ].

    inversion H; simpl in *; subst.
    eexists; split; eauto.
  Qed.

  Definition initP_map (s1: MailFSPathAbsState.State) :
    {s2: MailFSStringAbsState.State |
     MailFSPathAbsState.initP s1 -> absR s1 s2 /\ MailFSStringAbsState.initP s2}.
  Proof.
    unfold MailFSPathAbsState.initP, MailFSStringAbsState.initP, absR; intros.
    destruct s1; simpl.
    exists_econstructor; (intuition eauto); propositional.
    apply FMap.empty_mapsto in H; propositional.
  Qed.

End MailFSPathAbsImpl'.

Module MailFSPathAbsImpl :=
 HLayerImplAbs MailFSStringOp
    MailFSPathAbsState MailFSPathAbsAPI
    MailFSStringAbsState MailFSStringAPI
    MailFSPathAbsImpl'.

Module MailFSPathAbsImplH' :=
 LayerImplAbsHT MailFSStringOp
    MailFSPathAbsState MailFSPathAbsAPI
    MailFSStringAbsState MailFSStringAPI
    MailFSPathAbsImpl'
    UserIdx.

Module MailFSPathAbsImplH :=
 LayerImplAbs MailFSStringHOp
    MailFSPathAbsHState MailFSPathAbsHAPI
    MailFSStringAbsHState MailFSStringHAPI
    MailFSPathAbsImplH'.
