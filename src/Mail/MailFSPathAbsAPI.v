Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailFSStringAPI.

Module MailFSPathAbsState.

  Definition fs_contents := FMap.t (string * string) string.

  Record state_rec := mk_state {
    fs : fs_contents;
    locked : bool;
  }.

  Definition State := state_rec.
  Definition initP (s : State) := locked s = false /\
                              fs s = FMap.empty.

End MailFSPathAbsState.
Definition MailFSPathAbsHState := HState MailFSPathAbsState.State UserIdx.idx.


Module MailFSPathAbsAPI.

  Import MailFSStringOp.
  Import MailFSPathAbsState.

  Definition filter_dir (dirname : string) (fs : fs_contents) :=
    FMap.filter (fun '(dn, fn) => if dn == dirname then true else false) fs.

  Definition drop_dirname (fs : fs_contents) :=
    FMap.map_keys (fun '(dn, fn) => fn) fs.

  Lemma in_filter_dir_eq: forall dirname k s,
      FMap.In (dirname, k) s ->
      FMap.In (dirname, k) (filter_dir dirname s).
  Proof.
    intros.
    unfold filter_dir.
    apply FMap.filter_complete; auto.
    destruct (dirname == dirname); simpl in *; try congruence.
  Qed.

  Lemma filter_dir_in_eq: forall dirname k s,
      FMap.In (dirname, k) (filter_dir dirname s) ->
      FMap.In (dirname, k) s.
  Proof.
    intros.
    unfold filter_dir in *.
    eapply FMap.filter_in; eauto.
  Qed.

  Lemma in_drop_dirname_eq: forall dirname k s,
      FMap.In (dirname, k) (filter_dir dirname s) ->
      FMap.In k (drop_dirname (filter_dir dirname s)).
  Proof.
    intros.
    eapply FMap.map_keys_in in H.
    exact H.
  Qed.

  Lemma drop_dirname_in_eq: forall dirname k s,
      FMap.In k (drop_dirname (filter_dir dirname s)) ->
      FMap.In (dirname, k) (filter_dir dirname s).
  Proof.
    unfold drop_dirname, filter_dir.
    intros.
    eapply FMap.map_keys_in' in H; deex.
    destruct k'.
    eapply FMap.filter_holds in H as H'.
    destruct (s0 == dirname); congruence.
  Qed.

  Lemma drop_dirname_filter_dir: forall s dirname k,
      FMap.In k (drop_dirname (filter_dir dirname s)) ->
      FMap.In (dirname, k) s.
  Proof.
    intros.
    apply filter_dir_in_eq.
    apply drop_dirname_in_eq; auto.
  Qed.

  Lemma filter_dir_drop_dirname: forall s dirname k,
      FMap.In (dirname, k) s ->
      FMap.In k (drop_dirname (filter_dir dirname s)).
  Proof.
    intros.
    apply in_drop_dirname_eq.
    apply in_filter_dir_eq; auto.
  Qed.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepCreateWriteTmpOk : forall fs tid tmpfn data lock,
    xstep (CreateWriteTmp tmpfn data) tid
      (mk_state fs lock)
      true
      (mk_state (FMap.add (tmp_string, tmpfn) data fs) lock)
      nil

  | StepCreateWriteTmpErr1 : forall fs tid tmpfn data lock,
    xstep (CreateWriteTmp tmpfn data) tid
      (mk_state fs lock)
      false
      (mk_state fs lock)
      nil
  | StepCreateWriteTmpErr2 : forall fs tid tmpfn data data' lock,
    xstep (CreateWriteTmp tmpfn data) tid
      (mk_state fs lock)
      false
      (mk_state (FMap.add (tmp_string, tmpfn) data' fs) lock)
      nil

  | StepUnlinkTmp : forall fs tid tmpfn lock,
    xstep (UnlinkTmp tmpfn) tid
      (mk_state fs lock)
      tt
      (mk_state (FMap.remove (tmp_string, tmpfn) fs) lock)
      nil
  | StepLinkMailOK : forall fs tid mailfn data tmpfn lock,
    FMap.MapsTo (tmp_string, tmpfn) data fs ->
    ~ FMap.In (mail_string, mailfn) fs ->
    xstep (LinkMail tmpfn mailfn) tid
      (mk_state fs lock)
      true
      (mk_state (FMap.add (mail_string, mailfn) data fs) lock)
      nil
  | StepLinkMailErr : forall fs tid mailfn tmpfn lock,
    xstep (LinkMail tmpfn mailfn) tid
      (mk_state fs lock)
      false
      (mk_state fs lock)
      nil

  | StepList : forall fs tid r lock,
    FMap.is_permutation_key r (drop_dirname (filter_dir mail_string fs)) ->
    xstep List tid
      (mk_state fs lock)
      r
      (mk_state fs lock)
      nil

  | StepGetTID : forall s tid,
    xstep GetTID tid
      s
      tid
      s
      nil
  | StepRandom : forall s tid r,
    xstep Random tid
      s
      r
      s
      nil

  | StepReadOK : forall fn fs tid m lock,
    FMap.MapsTo (mail_string, fn) m fs ->
    xstep (Read fn) tid
      (mk_state fs lock)
      (Some m)
      (mk_state fs lock)
      nil
  | StepReadNone : forall fn fs tid lock,
    ~ FMap.In (mail_string, fn) fs ->
    xstep (Read fn) tid
      (mk_state fs lock)
      None
      (mk_state fs lock)
      nil

  | StepDelete : forall fn fs tid lock,
    xstep (Delete fn) tid
      (mk_state fs lock)
      tt
      (mk_state (FMap.remove (mail_string, fn) fs) lock)
      nil

  | StepLock : forall fs tid,
    xstep Lock tid
      (mk_state fs false)
      tt
      (mk_state fs true)
      nil
  | StepUnlock : forall fs tid lock,
    xstep Unlock tid
      (mk_state fs lock)
      tt
      (mk_state fs false)
      nil

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

  Definition initP := initP.

  Definition l : Layer.t MailFSStringOp.Op MailFSPathAbsState.State.
    refine {| Layer.step := step;
              Layer.initP := initP; |}.
  Defined.
                            
End MailFSPathAbsAPI.
Definition MailFSPathAbsHAPI := HLayer.t MailFSPathAbsAPI.l UserIdx.idx.
