Require Import POCS.
Require Import String.
Require Import MailboxAPI.
Require Import DeliverAPI.
Require Import DeliverListTidAPI.


Module DeliverListTidRestrictedImpl <: LayerImplFollowsRule DeliverListTidRestrictedAPI DeliverAPI LinkMailRule.

  Fixpoint nextfn (files : list string) (r : string) : string :=
    match files with
    | nil => r
    | fn' :: files' =>
      let r' :=
        if (le_dec (String.length r) (String.length fn')) then
          ("a" ++ fn')%string
        else
          r
        in
      nextfn files' r'
    end.

  Lemma nextfn_ok' : forall (tid : nat) `(s : FMap.t _ V) r1 r0 n,
    ( forall fn, FMap.In (tid, fn) s -> In fn (r0 ++ r1) ) ->
    ( forall fn, In fn r0 -> String.length n > String.length fn ) ->
    ~ FMap.In (tid, nextfn r1 n) s.
  Proof.
    induction r1; simpl; intros.
    - intro.
      specialize (H _ H1). rewrite app_nil_r in *.
      specialize (H0 _ H).
      omega.
    - eapply IHr1 with (r0 := r0 ++ (a :: nil)); clear IHr1; intros.
      + rewrite <- app_assoc; simpl. eauto.
      + eapply in_app_or in H1; intuition eauto.
        * specialize (H0 _ H2).
          destruct (le_dec (length n) (length a)); simpl; omega.
        * inversion H2; subst. 2: inversion H1.
          destruct (le_dec (length n) (length fn)); simpl; omega.
  Qed.

  Lemma nextfn_ok : forall (tid : nat) `(s : FMap.t _ V) r n,
    ( forall fn, In fn r <-> FMap.In (tid, fn) s ) ->
    ~ FMap.In (tid, nextfn r n) s.
  Proof.
    intros.
    eapply nextfn_ok' with (r0 := nil); simpl; intros.
    eapply H; eauto.
    omega.
  Qed.

  Definition linkmail_core (tmpfn : string) :=
    files <- Op DeliverListTidAPI.ListTid;
    let newname := nextfn files ""%string in
    _ <- Op (DeliverListTidAPI.LinkMail tmpfn newname);
    Ret tt.

  Definition createtmp_core :=
    r <- Op DeliverListTidAPI.CreateTmp;
    Ret r.

  Definition writetmp_core fn data :=
    r <- Op (DeliverListTidAPI.WriteTmp fn data);
    Ret r.

  Definition unlinktmp_core fn :=
    r <- Op (DeliverListTidAPI.UnlinkTmp fn);
    Ret r.

  Definition list_core :=
    l <- Op (DeliverListTidAPI.List);
    Ret l.

  Definition read_core fn :=
    r <- Op (DeliverListTidAPI.Read fn);
    Ret r.

  Definition getrequest_core :=
    r <- Op (DeliverListTidAPI.GetRequest);
    Ret r.

  Definition respond_core T (r : T) :=
    r <- Op (DeliverListTidAPI.Respond r);
    Ret r.

  Definition compile_op T (op : DeliverAPI.opT T) : proc _ T :=
    match op with
    | DeliverAPI.CreateTmp => createtmp_core
    | DeliverAPI.WriteTmp fn data => writetmp_core fn data
    | DeliverAPI.LinkMail m => linkmail_core m
    | DeliverAPI.UnlinkTmp fn => unlinktmp_core fn
    | DeliverAPI.List => list_core
    | DeliverAPI.Read fn => read_core fn
    | DeliverAPI.GetRequest => getrequest_core
    | DeliverAPI.Respond r => respond_core r
    end.

  Ltac step_inv :=
    match goal with
    | H : DeliverAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidRestrictedAPI.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidRestrictedAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (DeliverAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverListTidAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (DeliverListTidRestrictedAPI.step_allow _ _ _) => econstructor.
  Hint Extern 1 (DeliverListTidRestrictedAPI.step _ _ _ _ _ _) => econstructor.

  Lemma listtid_right_mover :
    right_mover
      DeliverListTidRestrictedAPI.step
      (DeliverListTidAPI.ListTid).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.
    eexists; split.
    econstructor; eauto.
    econstructor; intros; eauto.
    econstructor; intros; eauto.
    split; intros.
    - eapply H4 in H0.
      eapply FMap.in_add; eauto.
    - eapply H4.
      eapply FMap.in_add_ne; eauto.
      congruence.
  Qed.

  Hint Resolve listtid_right_mover.

  Theorem linkmail_atomic : forall `(rx : _ -> proc _ T) m,
    trace_incl DeliverListTidRestrictedAPI.step
      (Bind (compile_op (DeliverAPI.LinkMail m)) rx)
      (Bind (atomize compile_op (DeliverAPI.LinkMail m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold linkmail_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl DeliverListTidRestrictedAPI.step
      (Bind (compile_op (DeliverAPI.List)) rx)
      (Bind (atomize compile_op (DeliverAPI.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem read_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl DeliverListTidRestrictedAPI.step
      (Bind (compile_op (DeliverAPI.Read fn)) rx)
      (Bind (atomize compile_op (DeliverAPI.Read fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold read_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem createtmp_atomic : forall `(rx : _ -> proc _ T),
    trace_incl DeliverListTidRestrictedAPI.step
      (Bind (compile_op (DeliverAPI.CreateTmp)) rx)
      (Bind (atomize compile_op (DeliverAPI.CreateTmp)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold createtmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem writetmp_atomic : forall `(rx : _ -> proc _ T) fn data,
    trace_incl DeliverListTidRestrictedAPI.step
      (Bind (compile_op (DeliverAPI.WriteTmp fn data)) rx)
      (Bind (atomize compile_op (DeliverAPI.WriteTmp fn data)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold writetmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem unlinktmp_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl DeliverListTidRestrictedAPI.step
      (Bind (compile_op (DeliverAPI.UnlinkTmp fn)) rx)
      (Bind (atomize compile_op (DeliverAPI.UnlinkTmp fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold unlinktmp_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem getrequest_atomic : forall `(rx : _ -> proc _ T),
    trace_incl DeliverListTidRestrictedAPI.step
      (Bind (compile_op (DeliverAPI.GetRequest)) rx)
      (Bind (atomize compile_op (DeliverAPI.GetRequest)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold getrequest_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem respond_atomic : forall `(rx : _ -> proc _ T) Tr (r : Tr),
    trace_incl DeliverListTidRestrictedAPI.step
      (Bind (compile_op (DeliverAPI.Respond r)) rx)
      (Bind (atomize compile_op (DeliverAPI.Respond r)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold respond_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op DeliverListTidRestrictedAPI.step DeliverAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: repeat atomic_exec_inv; repeat step_inv; eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op DeliverListTidRestrictedAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op.
    + rewrite createtmp_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite writetmp_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite linkmail_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite unlinktmp_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite list_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite read_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite getrequest_atomic.
      eapply trace_incl_bind_a; eauto.
    + rewrite respond_atomic.
      eapply trace_incl_bind_a; eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts DeliverListTidRestrictedAPI.step DeliverAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : DeliverListTidRestrictedAPI.State) (s2 : DeliverAPI.State) :=
    s1 = s2.

  Definition compile_ts := Compile.compile_ts compile_op.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply Compile.compile_ts_no_atomics.
    destruct op; compute; eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts2,
      no_atomics_ts ts2 ->
      traces_match_abs absR
        DeliverListTidRestrictedAPI.initP
        DeliverListTidRestrictedAPI.step
        DeliverAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      DeliverListTidRestrictedAPI.initP s1 ->
      absR s1 s2 ->
      DeliverAPI.initP s2.
  Proof.
    eauto.
  Qed.

  Lemma list_follows_protocol : forall tid s,
    follows_protocol_proc
      DeliverListTidAPI.step
      DeliverListTidRestrictedAPI.step_allow
      LinkMailRule.loopInv tid s list_core.
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.
    constructor; intros.
  Qed.

  Lemma createtmp_follows_protocol : forall tid s,
    follows_protocol_proc
      DeliverListTidAPI.step
      DeliverListTidRestrictedAPI.step_allow
      LinkMailRule.loopInv tid s createtmp_core.
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.
    constructor; intros.
  Qed.

  Lemma writetmp_follows_protocol : forall tid s fn data,
    follows_protocol_proc
      DeliverListTidAPI.step
      DeliverListTidRestrictedAPI.step_allow
      LinkMailRule.loopInv tid s (writetmp_core fn data).
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.
    constructor; intros.
  Qed.

  Lemma unlinktmp_follows_protocol : forall tid s fn,
    follows_protocol_proc
      DeliverListTidAPI.step
      DeliverListTidRestrictedAPI.step_allow
      LinkMailRule.loopInv tid s (unlinktmp_core fn).
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.
    constructor; intros.
  Qed.

  Lemma getrequest_follows_protocol : forall tid s,
    follows_protocol_proc
      DeliverListTidAPI.step
      DeliverListTidRestrictedAPI.step_allow
      LinkMailRule.loopInv tid s getrequest_core.
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.
    constructor; intros.
  Qed.

  Lemma respond_follows_protocol : forall tid s T (r : T),
    follows_protocol_proc
      DeliverListTidAPI.step
      DeliverListTidRestrictedAPI.step_allow
      LinkMailRule.loopInv tid s (respond_core r).
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.
    constructor; intros.
  Qed.

  Lemma read_follows_protocol : forall tid s fn,
    follows_protocol_proc
      DeliverListTidAPI.step
      DeliverListTidRestrictedAPI.step_allow
      LinkMailRule.loopInv tid s (read_core fn).
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.
    constructor; intros.
  Qed.

  Lemma linkmail_follows_protocol : forall tid s data,
    follows_protocol_proc
      DeliverListTidAPI.step
      DeliverListTidRestrictedAPI.step_allow
      LinkMailRule.loopInv tid s (linkmail_core data).
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.

    constructor; intros.
      constructor; intros.

    {
      eapply exec_any_op in H; repeat deex.
      destruct H0.
      repeat step_inv.

      econstructor.
      eapply nextfn_ok; eauto.
    }

    constructor; intros.
  Qed.

  Hint Resolve linkmail_follows_protocol.
  Hint Resolve read_follows_protocol.
  Hint Resolve list_follows_protocol.
  Hint Resolve createtmp_follows_protocol.
  Hint Resolve writetmp_follows_protocol.
  Hint Resolve unlinktmp_follows_protocol.
  Hint Resolve getrequest_follows_protocol.
  Hint Resolve respond_follows_protocol.

  Theorem compile_ts_follows_protocol :
    forall ts,
      no_atomics_ts ts ->
      LinkMailRule.follows_protocol (compile_ts ts).
  Proof.
    unfold compile_ts.
    unfold LinkMailRule.follows_protocol.
    unfold follows_protocol_s.
    intros.

    edestruct proc_match_pick with (tid := tid).
      eapply Compile.compile_ts_ok with (compile_op := compile_op); eauto.
    unfold DeliverListTidAPI.opT, DeliverListTidRestrictedAPI.opT in *.
      intuition congruence.
    unfold DeliverListTidAPI.opT, DeliverListTidRestrictedAPI.opT in *.
      repeat deex.
    match goal with
    | H1 : _ [[ tid ]] = Proc _,
      H2 : _ [[ tid ]] = Proc _ |- _ =>
      rewrite H1 in H2; clear H1; inversion H2; clear H2;
        subst; repeat sigT_eq
    end.

    clear dependent ts.
    generalize dependent s.

    match goal with
    | H : Compile.compile_ok _ _ _ |- _ =>
      induction H; intros; eauto
    end.

    destruct op; simpl; eauto.

    unfold LinkMailRule.loopInv.
    econstructor; eauto.
  Qed.

End DeliverListTidRestrictedImpl.


Module DeliverListTidImpl' <: LayerImplRequiresRule DeliverListTidAPI DeliverListTidRestrictedAPI LinkMailRule.

  Import LinkMailRule.

  Definition absR (s1 : DeliverListTidAPI.State) (s2 : DeliverListTidRestrictedAPI.State) :=
    s1 = s2.

  Ltac step_inv :=
    match goal with
    | H : DeliverListTidAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidRestrictedAPI.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : DeliverListTidRestrictedAPI.step _ _ _ _ _ _ |- _ =>
      destruct H; intuition idtac
    end.

  Theorem allowed_stable :
    forall `(op : DeliverListTidRestrictedAPI.opT T) `(op' : DeliverListTidRestrictedAPI.opT T') tid tid' s s' r evs,
      tid <> tid' ->
      DeliverListTidRestrictedAPI.step_allow op tid s ->
      DeliverListTidRestrictedAPI.step op' tid' s r s' evs ->
      DeliverListTidRestrictedAPI.step_allow op tid s'.
  Proof.
    intros.
    destruct op; destruct op'; repeat step_inv; subst; eauto.
    constructor.
    contradict H4.
    eapply FMap.in_add_ne; eauto.
    congruence.
  Qed.

  Definition compile_ts (ts : @threads_state DeliverListTidRestrictedAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      DeliverListTidAPI.initP s1 ->
      absR s1 s2 ->
      DeliverListTidRestrictedAPI.initP s2.
  Proof.
    eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      follows_protocol ts ->
      no_atomics_ts ts ->
      traces_match_abs absR
        DeliverListTidAPI.initP
        DeliverListTidAPI.step
        DeliverListTidRestrictedAPI.step (compile_ts ts) ts.
  Proof.
    unfold compile_ts, follows_protocol, absR.
    unfold traces_match_abs; intros; subst.
    clear H1.
    specialize (H sm).
    destruct H2.
    induction H1; eauto.
    specialize (H tid _ p) as Htid.
    intuition idtac; repeat deex.

    edestruct IHexec.
      eapply follows_protocol_s_exec_tid_upd; eauto.
      intros; eapply allowed_stable; eauto.
      destruct result; eauto.

    eexists; intuition idtac.
    eapply ExecPrefixOne.
      eauto.
      eapply follows_protocol_preserves_exec_tid'; eauto.
      eauto.
    eauto.
  Qed.

End DeliverListTidImpl'.


Module DeliverListTidImpl :=
  LinkWithRule DeliverListTidAPI DeliverListTidRestrictedAPI DeliverAPI LinkMailRule
               DeliverListTidImpl' DeliverListTidRestrictedImpl.
