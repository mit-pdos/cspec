Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSStringAbsAPI.
Require Import MailFSStringAPI.
Require Import MailFSPathAbsAPI.


Module MailFSPathAbsImpl <: LayerImpl MailFSPathAbsAPI MailFSStringAPI.

  Definition absR (s1 : MailFSPathAbsAPI.State) (s2 : MailFSStringAPI.State) :=
    MailFSPathAbsAPI.locked s1 = MailFSStringAbsAPI.locked s2 /\
    forall dirname filename contents,
      FMap.MapsTo (dirname, filename) contents (MailFSPathAbsAPI.fs s1) <->
      ( dirname = "tmp"%string /\ FMap.MapsTo filename contents (MailFSStringAbsAPI.tmpdir s2) \/
        dirname = "mail"%string /\ FMap.MapsTo filename contents (MailFSStringAbsAPI.maildir s2) ).

  Definition compile_ts (ts : @threads_state MailFSStringAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall (ts : @threads_state MailFSStringAPI.opT),
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Hint Extern 1 (MailFSStringAPI.step _ _ _ _ _ _) => econstructor.

  Lemma fn_ne : forall (dirname fn1 fn2 : string),
    (dirname, fn1) <> (dirname, fn2) ->
    fn1 <> fn2.
  Proof.
    congruence.
  Qed.

  Hint Resolve FMap.add_mapsto.
  Hint Resolve FMap.mapsto_add_ne'.
  Hint Resolve fn_ne.

  Lemma absR_add_tmp :
    forall fs tmp mail fn data lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      absR (MailFSPathAbsAPI.mk_state (FMap.add ("tmp"%string, fn) data fs) lock)
           (MailFSStringAbsAPI.mk_state (FMap.add fn data tmp) mail lock').
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
    - eapply FMap.mapsto_add_ne'; try congruence.
      eapply H1; eauto.
  Qed.

  Lemma absR_remove_tmp :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      absR (MailFSPathAbsAPI.mk_state (FMap.remove ("tmp"%string, fn) fs) lock)
           (MailFSStringAbsAPI.mk_state (FMap.remove fn tmp) mail lock').
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
      specialize (H1 "tmp"%string filename contents); simpl in *.
      intuition try congruence.
      eapply FMap.remove_mapsto; congruence.
    - specialize (H1 "mail"%string filename contents); simpl in *.
      intuition try congruence.
      eapply FMap.remove_mapsto; congruence.
  Qed.

  Lemma absR_add_mail :
    forall fs tmp mail fn data lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      absR (MailFSPathAbsAPI.mk_state (FMap.add ("mail"%string, fn) data fs) lock)
           (MailFSStringAbsAPI.mk_state tmp (FMap.add fn data mail) lock').
  Proof.
    unfold absR; simpl; intuition subst.
    - eapply FMap.mapsto_add_or in H; intuition subst.
      + inversion H; clear H; subst.
        eauto.
      + eapply H1 in H2; clear H1.
        intuition eauto; subst.
        destruct (filename == fn); try congruence.
        intuition eauto.
    - eapply FMap.mapsto_add_ne'; try congruence.
      eapply H1; eauto.
    - eapply FMap.mapsto_add_or in H3; intuition subst; eauto.
      eapply FMap.mapsto_add_ne'; try congruence.
      eapply H1; eauto.
  Qed.

  Lemma absR_remove_mail :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      absR (MailFSPathAbsAPI.mk_state (FMap.remove ("mail"%string, fn) fs) lock)
           (MailFSStringAbsAPI.mk_state tmp (FMap.remove fn mail) lock').
  Proof.
    unfold absR; simpl; intuition subst.
    - eapply FMap.mapsto_remove in H; intuition subst.
      eapply H1 in H2; clear H1.
      intuition subst.
      destruct (filename == fn); try congruence.
      right; split; try reflexivity.
      eapply FMap.remove_mapsto with (x := fn) in H2; auto.
    - specialize (H1 "tmp"%string filename contents); simpl in *.
      intuition try congruence.
      eapply FMap.remove_mapsto; congruence.
    - destruct (filename == fn); try congruence; subst.
      eapply FMap.mapsto_remove in H3; intuition subst.
      eapply FMap.mapsto_remove in H3; intuition subst.
      specialize (H1 "mail"%string filename contents); simpl in *.
      intuition try congruence.
      eapply FMap.remove_mapsto; congruence.
  Qed.

  Lemma absR_in_tmp :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      FMap.In fn tmp ->
      FMap.In ("tmp"%string, fn) fs.
  Proof.
    unfold absR; intros.
    eapply FMap.in_mapsto_exists in H0; destruct H0.
    eapply FMap.mapsto_in.
    eapply H; eauto.
  Qed.

  Lemma absR_mapsto_tmp :
    forall fs tmp mail fn data lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      FMap.MapsTo ("tmp"%string, fn) data fs ->
      FMap.MapsTo fn data tmp.
  Proof.
    unfold absR; intros.
    eapply H in H0; intuition congruence.
  Qed.

  Lemma absR_in_mail :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      FMap.In fn mail ->
      FMap.In ("mail"%string, fn) fs.
  Proof.
    unfold absR; intros.
    eapply FMap.in_mapsto_exists in H0; destruct H0.
    eapply FMap.mapsto_in.
    eapply H; eauto.
  Qed.

  Lemma absR_mapsto_mail :
    forall fs tmp mail fn data lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      FMap.MapsTo ("mail"%string, fn) data fs ->
      FMap.MapsTo fn data mail.
  Proof.
    unfold absR; intros.
    eapply H in H0; intuition congruence.
  Qed.

  Lemma absR_in_mail' :
    forall fs tmp mail fn lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      FMap.In ("mail"%string, fn) fs ->
      FMap.In fn mail.
  Proof.
    intros.
    eapply FMap.in_mapsto_exists in H0; deex.
    eapply FMap.mapsto_in.
    eapply absR_mapsto_mail; eauto.
  Qed.

  Lemma absR_is_permutation_key :
    forall r fs tmp mail lock lock',
      absR (MailFSPathAbsAPI.mk_state fs lock)
           (MailFSStringAbsAPI.mk_state tmp mail lock') ->
      FMap.is_permutation_key r
        (MailFSPathAbsAPI.drop_dirname
           (MailFSPathAbsAPI.filter_dir "mail" fs)) ->
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
      specialize (H3 "mail"%string x x0) as Hy.
      apply Hy in m.
      intuition; try congruence.
      simpl in *.
      apply FMap.mapsto_in in H9; auto.
    + unfold absR in *.
      intuition idtac.
      apply FMap.in_mapsto_get in H1.
      destruct H1.
      specialize (H3 "mail"%string x x0) as Hy.
      intuition; try congruence.
      simpl in *.
      apply FMap.mapsto_in in H4.
      apply MailFSPathAbsAPI.filter_dir_drop_dirname in H4.
      apply H0 in H4; auto.
  Qed.

  Lemma absR_change_lock :
    forall fs tmp mail lock0 lock1 lock2,
      absR (MailFSPathAbsAPI.mk_state fs lock0)
           (MailFSStringAbsAPI.mk_state tmp mail lock1) ->
      absR (MailFSPathAbsAPI.mk_state fs lock2)
           (MailFSStringAbsAPI.mk_state tmp mail lock2).
  Proof.
    unfold absR; intuition eauto.
  Qed.

  Hint Resolve absR_add_tmp.
  Hint Resolve absR_remove_tmp.
  Hint Resolve absR_add_mail.
  Hint Resolve absR_remove_mail.
  Hint Resolve absR_in_tmp.
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

  Hint Resolve absR_ok.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR
        MailFSPathAbsAPI.initP
        MailFSPathAbsAPI.step
        MailFSStringAPI.step (compile_ts ts) ts.
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
      MailFSStringAPI.initP s2.
  Proof.
    eauto.
  Qed.

End MailFSPathAbsImpl.
