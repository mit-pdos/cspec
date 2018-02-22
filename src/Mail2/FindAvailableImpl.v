Require Import POCS.
Require Import String.
Require Import CreateAPI.


Module FindAvailable <: LayerImpl RestrictedListAPI MaildirAPI.

  Fixpoint nextfn (files : list string) (r : string) : string :=
    match files with
    | nil => r
    | fn' :: files' =>
      let r' :=
        if (lt_dec (String.length r) (String.length fn')) then
          ("a" ++ fn')%string
        else
          r
        in
      nextfn files' r'
    end.

  Definition linkmsg_core (data : string) :=
    files <- Op RestrictedListAPI.ListRestricted;
    let newname := nextfn files ""%string in
    _ <- Op (RestrictedListAPI.LinkMsg newname data);
    Ret tt.

  Definition list_core :=
    l <- Op (RestrictedListAPI.List);
    Ret l.

  Definition readmsg_core fn :=
    r <- Op (RestrictedListAPI.ReadMsg fn);
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
    end; intuition idtac.

  Hint Extern 1 (MaildirAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (RestrictedListAPI.step _ _ _ _ _ _) => econstructor.

  Lemma listrestricted_right_mover :
    right_mover
      RestrictedListAPI.step
      (RestrictedListAPI.ListRestricted).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto.
    eexists; split.
    econstructor; eauto.
    econstructor; intros.
    split; intros.
    - eapply H1 in H0.
      eapply FMap.in_add; eauto.
    - eapply H1.
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

End FindAvailable.


Module RLImpl <: LayerImpl RawDirAPI RestrictedListAPI.

  Definition same_tid (tid : nat) (fn : nat * string) : bool :=
    if tid == fst fn then
      true
    else
      false.

  Definition linkmsg_core newname data :=
    _ <- Op (RawDirAPI.LinkMsg newname data);
    Ret tt.

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

  Definition compile_op T (op : RestrictedListAPI.opT T) : proc _ T :=
    match op with
    | RestrictedListAPI.LinkMsg fn m => linkmsg_core fn m
    | RestrictedListAPI.List => list_core
    | RestrictedListAPI.ListRestricted => list_restricted_core
    | RestrictedListAPI.ReadMsg fn => readmsg_core fn
    end.

  Ltac step_inv :=
    match goal with
    | H : RawDirAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : RestrictedListAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (RawDirAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (RestrictedListAPI.step _ _ _ _ _ _) => econstructor.

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
      (Bind (compile_op (RestrictedListAPI.LinkMsg fn m)) rx)
      (Bind (atomize compile_op (RestrictedListAPI.LinkMsg fn m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold linkmsg_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_atomic : forall `(rx : _ -> proc _ T),
    trace_incl RawDirAPI.step
      (Bind (compile_op (RestrictedListAPI.List)) rx)
      (Bind (atomize compile_op (RestrictedListAPI.List)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem list_restricted_atomic : forall `(rx : _ -> proc _ T),
    trace_incl RawDirAPI.step
      (Bind (compile_op (RestrictedListAPI.ListRestricted)) rx)
      (Bind (atomize compile_op (RestrictedListAPI.ListRestricted)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold list_restricted_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem readmsg_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl RawDirAPI.step
      (Bind (compile_op (RestrictedListAPI.ReadMsg fn)) rx)
      (Bind (atomize compile_op (RestrictedListAPI.ReadMsg fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold readmsg_core, ysa_movers.
    eauto 20.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op RawDirAPI.step RestrictedListAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      repeat step_inv; eauto.
      admit.
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
  Admitted.

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
      traces_match_ts RawDirAPI.step RestrictedListAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : RawDirAPI.State) (s2 : RestrictedListAPI.State) :=
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
      traces_match_abs absR RawDirAPI.initP RawDirAPI.step RestrictedListAPI.step (compile_ts ts2) ts2.
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

End RLImpl.
