Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSStringAbsAPI.
Require Import MailFSStringAPI.
Require Import MailFSPathAbsAPI.


Module MailFSPathAbsImpl <: LayerImpl MailFSPathAbsAPI MailFSStringAPI.

  Definition absR (s1 : MailFSPathAbsAPI.State) (s2 : MailFSStringAPI.State) :=
    forall dirname filename contents,
      FMap.MapsTo (dirname, filename) contents s1 <->
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
    forall fs tmp mail fn data,
      absR fs (MailFSStringAbsAPI.mk_state tmp mail) ->
      absR (FMap.add ("tmp"%string, fn) data fs)
           (MailFSStringAbsAPI.mk_state (FMap.add fn data tmp) mail).
  Proof.
  Admitted.

  Lemma absR_remove_tmp :
    forall fs tmp mail fn,
      absR fs (MailFSStringAbsAPI.mk_state tmp mail) ->
      absR (FMap.remove ("tmp"%string, fn) fs)
           (MailFSStringAbsAPI.mk_state (FMap.remove fn tmp) mail).
  Proof.
  Admitted.

  Lemma absR_add_mail :
    forall fs tmp mail fn data,
      absR fs (MailFSStringAbsAPI.mk_state tmp mail) ->
      absR (FMap.add ("mail"%string, fn) data fs)
           (MailFSStringAbsAPI.mk_state tmp (FMap.add fn data mail)).
  Proof.
  Admitted.

  Lemma absR_in_tmp :
    forall fs tmp mail fn,
      absR fs (MailFSStringAbsAPI.mk_state tmp mail) ->
      FMap.In fn tmp ->
      FMap.In ("tmp"%string, fn) fs.
  Admitted.

  Lemma absR_mapsto_tmp :
    forall fs tmp mail fn data,
      absR fs (MailFSStringAbsAPI.mk_state tmp mail) ->
      FMap.MapsTo ("tmp"%string, fn) data fs ->
      FMap.MapsTo fn data tmp.
  Admitted.

  Lemma absR_in_mail :
    forall fs tmp mail fn,
      absR fs (MailFSStringAbsAPI.mk_state tmp mail) ->
      FMap.In fn mail ->
      FMap.In ("mail"%string, fn) fs.
  Admitted.

  Lemma absR_mapsto_mail :
    forall fs tmp mail fn data,
      absR fs (MailFSStringAbsAPI.mk_state tmp mail) ->
      FMap.MapsTo ("mail"%string, fn) data fs ->
      FMap.MapsTo fn data mail.
  Admitted.

  Hint Resolve absR_add_tmp.
  Hint Resolve absR_remove_tmp.
  Hint Resolve absR_add_mail.
  Hint Resolve absR_in_tmp.
  Hint Resolve absR_mapsto_tmp.
  Hint Resolve absR_in_mail.
  Hint Resolve absR_mapsto_mail.

  Theorem absR_ok :
    op_abs absR MailFSPathAbsAPI.step MailFSStringAPI.step.
  Proof.
    unfold op_abs; intros.
    destruct s2; simpl in *; subst.
    inversion H0; clear H0; subst; repeat sigT_eq.
    all: eexists.
    all: split; [ | econstructor ].
    all: simpl.
    all: eauto 10.

    admit.
    admit.
  Admitted.

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
