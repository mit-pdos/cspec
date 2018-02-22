Require Import POCS.
Require Import String.
Require Import CreateAPI.


Module FindAvailable <: LayerImplFollowsRule RestrictedListAPI MaildirAPI LinkMsgRule.

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

  Definition linkmsg_core (data : string) :=
    files <- Op RL2API.ListRestricted;
    let newname := nextfn files ""%string in
    _ <- Op (RL2API.LinkMsg newname data);
    Ret tt.

  Definition list_core :=
    l <- Op (RL2API.List);
    Ret l.

  Definition readmsg_core fn :=
    r <- Op (RL2API.ReadMsg fn);
    Ret r.

  Definition compile_op T (op : MaildirAPI.opT T) : proc _ T :=
    match op with
    | MaildirAPI.LinkMsg m => linkmsg_core m
    | MaildirAPI.List => list_core
    | MaildirAPI.ReadMsg fn => readmsg_core fn
    end.

  Ltac step_inv :=
    match goal with
    | H : MaildirAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : RestrictedListAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : RestrictedListAPI.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : RL2API.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MaildirAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (RestrictedListAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (RestrictedListAPI.step_allow _ _ _) => econstructor.
  Hint Extern 1 (RL2API.step _ _ _ _ _ _) => econstructor.

  Lemma listrestricted_right_mover :
    right_mover
      RestrictedListAPI.step
      (RL2API.ListRestricted).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.
    eexists; split.
    econstructor; eauto.
    econstructor; intros; eauto.
    econstructor; intros; eauto.
    split; intros.
    - eapply H3 in H0.
      eapply FMap.in_add; eauto.
    - eapply H3.
      eapply FMap.in_add_ne; eauto.
      congruence.
  Qed.

  Hint Resolve listrestricted_right_mover.

  Theorem linkmsg_atomic : forall `(rx : _ -> proc _ T) m,
    trace_incl RestrictedListAPI.step
      (Bind (compile_op (MaildirAPI.LinkMsg m)) rx)
      (Bind (atomize compile_op (MaildirAPI.LinkMsg m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold linkmsg_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl RestrictedListAPI.step
      (Bind (compile_op (MaildirAPI.List)) rx)
      (Bind (atomize compile_op (MaildirAPI.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem readmsg_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl RestrictedListAPI.step
      (Bind (compile_op (MaildirAPI.ReadMsg fn)) rx)
      (Bind (atomize compile_op (MaildirAPI.ReadMsg fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold readmsg_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op RestrictedListAPI.step MaildirAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op RestrictedListAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op.
    + rewrite linkmsg_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite list_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite readmsg_atomic.
      eapply trace_incl_bind_a.
      eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts RestrictedListAPI.step MaildirAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : RestrictedListAPI.State) (s2 : MaildirAPI.State) :=
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
      traces_match_abs absR RestrictedListAPI.initP RestrictedListAPI.step MaildirAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      RestrictedListAPI.initP s1 ->
      absR s1 s2 ->
      MaildirAPI.initP s2.
  Proof.
    eauto.
  Qed.

  Lemma list_follows_protocol : forall tid s,
    follows_protocol_proc RL2API.step RestrictedListAPI.step_allow LinkMsgRule.loopInv tid s list_core.
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.
    constructor; intros.
  Qed.

  Lemma readmsg_follows_protocol : forall tid s fn,
    follows_protocol_proc RL2API.step RestrictedListAPI.step_allow LinkMsgRule.loopInv tid s (readmsg_core fn).
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.
    constructor; intros.
  Qed.

  Lemma linkmsg_follows_protocol : forall tid s data,
    follows_protocol_proc RL2API.step RestrictedListAPI.step_allow LinkMsgRule.loopInv tid s (linkmsg_core data).
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

  Hint Resolve linkmsg_follows_protocol.
  Hint Resolve readmsg_follows_protocol.
  Hint Resolve list_follows_protocol.

  Theorem compile_ts_follows_protocol :
    forall ts,
      no_atomics_ts ts ->
      LinkMsgRule.follows_protocol (compile_ts ts).
  Proof.
    unfold compile_ts.
    unfold LinkMsgRule.follows_protocol.
    unfold follows_protocol_s.
    intros.

    edestruct proc_match_pick with (tid := tid).
      eapply Compile.compile_ts_ok with (compile_op := compile_op); eauto.
    unfold RL2API.opT, RestrictedListAPI.opT in *.
      intuition congruence.
    unfold RL2API.opT, RestrictedListAPI.opT in *.
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

    unfold LinkMsgRule.loopInv.
    econstructor; eauto.
  Qed.

End FindAvailable.


Module RLImpl <: LayerImplRequiresRule RL2API RestrictedListAPI LinkMsgRule.

  Import LinkMsgRule.

  Definition absR (s1 : RL2API.State) (s2 : RestrictedListAPI.State) :=
    s1 = s2.

  Ltac step_inv :=
    match goal with
    | H : RL2API.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : RestrictedListAPI.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : RestrictedListAPI.step _ _ _ _ _ _ |- _ =>
      destruct H; intuition idtac
    end.

  Theorem allowed_stable :
    forall `(op : RestrictedListAPI.opT T) `(op' : RestrictedListAPI.opT T') tid tid' s s' r evs,
      tid <> tid' ->
      RestrictedListAPI.step_allow op tid s ->
      RestrictedListAPI.step op' tid' s r s' evs ->
      RestrictedListAPI.step_allow op tid s'.
  Proof.
    intros.
    destruct op; destruct op'; repeat step_inv; subst; eauto.
    constructor.
    contradict H4.
    eapply FMap.in_add_ne; eauto.
    congruence.
  Qed.

  Definition compile_ts (ts : @threads_state RestrictedListAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      RL2API.initP s1 ->
      absR s1 s2 ->
      RestrictedListAPI.initP s2.
  Proof.
    eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      follows_protocol ts ->
      no_atomics_ts ts ->
      traces_match_abs absR RL2API.initP RL2API.step RestrictedListAPI.step (compile_ts ts) ts.
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

End RLImpl.


Module RL2Impl <: LayerImpl RawDirAPI RL2API.

  Definition same_tid (tid : nat) (fn : nat * string) : bool :=
    if tid == fst fn then
      true
    else
      false.

  Definition linkmsg_core newname data :=
    v <- Op (RawDirAPI.LinkMsg newname data);
    Ret v.

  Definition list_core :=
    l <- Op (RawDirAPI.List);
    Ret l.

  Definition list_restricted_core :=
    tid <- Op (RawDirAPI.GetTID);
    l <- Op (RawDirAPI.List);
    Ret (map snd (filter (same_tid tid) l)).

  Definition readmsg_core fn :=
    r <- Op (RawDirAPI.ReadMsg fn);
    Ret r.

  Definition compile_op T (op : RL2API.opT T) : proc _ T :=
    match op with
    | RL2API.LinkMsg fn m => linkmsg_core fn m
    | RL2API.List => list_core
    | RL2API.ListRestricted => list_restricted_core
    | RL2API.ReadMsg fn => readmsg_core fn
    end.

  Ltac step_inv :=
    match goal with
    | H : RawDirAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : RL2API.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (RawDirAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (RL2API.step _ _ _ _ _ _) => econstructor.

  Lemma gettid_right_mover :
    right_mover
      RawDirAPI.step
      (RawDirAPI.GetTID).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto.
  Qed.

  Hint Resolve gettid_right_mover.

  Theorem linkmsg_atomic : forall `(rx : _ -> proc _ T) fn m,
    trace_incl RawDirAPI.step
      (Bind (compile_op (RL2API.LinkMsg fn m)) rx)
      (Bind (atomize compile_op (RL2API.LinkMsg fn m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold linkmsg_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl RawDirAPI.step
      (Bind (compile_op (RL2API.List)) rx)
      (Bind (atomize compile_op (RL2API.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_restricted_atomic : forall `(rx : _ -> proc _ T),
    trace_incl RawDirAPI.step
      (Bind (compile_op (RL2API.ListRestricted)) rx)
      (Bind (atomize compile_op (RL2API.ListRestricted)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_restricted_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem readmsg_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl RawDirAPI.step
      (Bind (compile_op (RL2API.ReadMsg fn)) rx)
      (Bind (atomize compile_op (RL2API.ReadMsg fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold readmsg_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op RawDirAPI.step RL2API.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
      econstructor; intros.
      split; intros.
      * eapply in_map_iff in H; deex. destruct x.
        eapply filter_In in H0; intuition idtac.
        unfold same_tid in *; simpl in *.
        destruct (v1 == n); try congruence.
        subst; eauto.
      * eapply in_map_iff.
        exists (v1, fn); intuition eauto.
        eapply filter_In; intuition eauto.
        unfold same_tid; simpl.
        destruct (v1 == v1); congruence.
    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op RawDirAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op.
    + rewrite linkmsg_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite list_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite list_restricted_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite readmsg_atomic.
      eapply trace_incl_bind_a.
      eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts RawDirAPI.step RL2API.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : RawDirAPI.State) (s2 : RL2API.State) :=
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
      traces_match_abs absR RawDirAPI.initP RawDirAPI.step RL2API.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      RawDirAPI.initP s1 ->
      absR s1 s2 ->
      RestrictedListAPI.initP s2.
  Proof.
    eauto.
  Qed.

End RL2Impl.
