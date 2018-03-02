Require Import POCS.
Require Import String.
Require Import MailboxAPI.
Require Import MailServerAPI.
Require Import MailServerDirAPI.
Require Import FMapFacts.


Module AtomicReader <: LayerImpl MailboxAPI MailServerDirAPI.

  Definition deliver_core (m : string) :=
    _ <- Op (MailboxAPI.Deliver m);
    Ret tt.

  Fixpoint read_list (l : list (nat*nat)) (r : list string) :=
    match l with
    | nil => Ret r
    | fn :: l' =>
      m <- Op (MailboxAPI.Read fn);
      read_list l' (r ++ (m :: nil))
    end.

  Definition readall_core :=
    l <- Op MailboxAPI.List;
    read_list l nil.

  Definition getrequest_core :=
    r <- Op MailboxAPI.GetRequest;
    Ret r.

  Definition respond_core T (r : T) :=
    r <- Op (MailboxAPI.Respond r);
    Ret r.

  Definition compile_op T (op : MailServerAPI.opT T) : proc _ T :=
    match op with
    | MailServerAPI.Deliver m => deliver_core m
    | MailServerAPI.ReadAll => readall_core
    | MailServerAPI.GetRequest => getrequest_core
    | MailServerAPI.Respond r => respond_core r
    end.

  Ltac step_inv :=
    match goal with
    | H : MailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailServerAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailServerDirAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailServerAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailServerDirAPI.step _ _ _ _ _ _) => econstructor.


  Lemma read_left_mover : forall fn,
    left_mover_pred
      MailboxAPI.step
      (MailboxAPI.Read fn)
      (fun tid s => FMap.In fn s).
  Proof.
    split.
(*
    - unfold enabled_stable, enabled_in; intros; repeat deex.
      repeat step_inv; eauto.
      destruct (fn0 == fn); subst; try congruence.
      + exfalso. eapply H11. eexists. eauto.
      + do 3 eexists; econstructor.
        eapply MailServerAPI.Dir.add_2; eauto.
    - intros; repeat step_inv; eauto; repeat deex.
      destruct (fn0 == fn); subst; try congruence.
      eapply MailServerAPI.Dir.add_3 in H2; eauto.
  Qed.
*)
  Admitted.

  Hint Resolve read_left_mover.

  Theorem deliver_atomic : forall `(rx : _ -> proc _ T) m,
    trace_incl MailboxAPI.step
      (Bind (compile_op (MailServerAPI.Deliver m)) rx)
      (Bind (atomize compile_op (MailServerAPI.Deliver m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold deliver_core, ysa_movers.
    eauto.
  Qed.

  Lemma mailbox_fn_monotonic :
    forall s s' tid fn,
      exec_others MailboxAPI.step tid s s' ->
      FMap.In fn s ->
      FMap.In fn s'.
  Proof.
    induction 1; eauto; intros.
    repeat deex.
    eapply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
    clear H0.
    step_inv.
    eapply FMap.add_incr; eauto.
  Qed.

  Theorem readall_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailboxAPI.step
      (Bind (compile_op MailServerAPI.ReadAll) rx)
      (Bind (atomize compile_op MailServerAPI.ReadAll) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold readall_core, ysa_movers.
    eapply RightMoversDone.
    eapply OneNonMover.

    intros.
    eapply left_movers_impl with
      (P1 := fun tid s => Forall (fun fn => FMap.In fn s) r).

    {
      generalize (@nil string).
      induction r; simpl; eauto.
      constructor; eauto.

      - eapply left_mover_pred_impl; eauto.
        intros.
        inversion H; clear H; subst.
        eauto.

      - intros.
        inversion H; clear H; subst.
        eapply FMap.in_mapsto_exists in H2; deex.
        do 2 eexists; econstructor; eauto.

      - intros.
        eapply left_movers_impl; eauto.
        intros; repeat deex.
        inversion H; clear H; subst.

        eapply exec_any_op in H0; repeat deex.
        step_inv.

        eapply Forall_impl; eauto; intros; simpl in *.
        eapply mailbox_fn_monotonic; eauto.
        eapply mailbox_fn_monotonic; eauto.
    }

    intros; repeat deex.
    eapply exec_any_op in H0; repeat deex.
    step_inv.
    eapply Forall_in'; intros.

    eapply mailbox_fn_monotonic; eauto.

    admit.
  Admitted.

  Theorem getrequest_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailboxAPI.step
      (Bind (compile_op (MailServerAPI.GetRequest)) rx)
      (Bind (atomize compile_op (MailServerAPI.GetRequest)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold getrequest_core, ysa_movers.
    eauto.
  Qed.

  Theorem respond_atomic : forall `(rx : _ -> proc _ T) Tr (r : Tr),
    trace_incl MailboxAPI.step
      (Bind (compile_op (MailServerAPI.Respond r)) rx)
      (Bind (atomize compile_op (MailServerAPI.Respond r)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold respond_core, ysa_movers.
    eauto.
  Qed.

  Lemma read_list_exec : forall l l0 r s s' evs v tid,
    List.Forall (fun fn => FMap.In fn s) l ->
    Forall2 (fun fn m => FMap.MapsTo fn m s) l0 r ->
    atomic_exec MailboxAPI.step
      (read_list l r) tid
      s v s' evs ->
    s' = s /\ evs = nil /\
    Forall2 (fun fn m => FMap.MapsTo fn m s) (l0 ++ l) v.
  Proof.
    induction l; intros.
    - atomic_exec_inv.
      rewrite app_nil_r.
      eauto.
    - atomic_exec_inv.
      inversion H11; clear H11; subst; repeat sigT_eq.
      edestruct IHl; [ | | eauto | ]; step_inv.
      + inversion H; subst; eauto.
      + eapply Forall2_app; eauto.
      + rewrite <- app_assoc in H3; simpl in *.
        eauto.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op MailboxAPI.step MailServerDirAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      simpl; intuition eauto.
      repeat step_inv; eauto.

    + atomic_exec_inv.
      eapply read_list_exec with (l0 := nil) in H10.
      {
        simpl in *.
        atomic_exec_inv.
        step_inv; subst; eauto.
        econstructor.

        assert (List.Forall (fun '(k, v) => FMap.MapsTo k v s1)
                  (FMap.elements s1)).
        {
          eapply Forall_forall; intros.
          destruct x.
          admit.
        }

        generalize dependent (FMap.elements s1); intros.
        generalize dependent v.
(*
        induction l; intros.
        - inversion H2; eauto.
        - inversion H2; clear H2; subst.
          inversion H; clear H; subst.
          specialize (IHl H4 _ H5); subst.
          destruct a; simpl in *; f_equal.
          eapply DirFacts.MapsTo_fun; eauto.
*)
        admit.
      }

      clear H10.
      atomic_exec_inv.
      step_inv.

      eapply Forall_forall; intros.
(*
      eapply in_map_iff in H; deex.
      destruct x0.
      eapply DirFacts.elements_in_iff; eexists.
      eapply In_InA; eauto.

      eauto.
*)
      admit.
      admit.

    + repeat atomic_exec_inv.
      simpl; intuition eauto.
      repeat step_inv; eauto.

    + repeat atomic_exec_inv.
      simpl; intuition eauto.
      repeat step_inv; eauto.
  Admitted.

  Theorem my_atomize_correct :
    atomize_correct compile_op MailboxAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op.
    + rewrite deliver_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite readall_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite getrequest_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite respond_atomic.
      eapply trace_incl_bind_a.
      eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts MailboxAPI.step MailServerDirAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : MailboxAPI.State) (s2 : MailServerDirAPI.State) :=
    s1 = s2.

  Definition compile_ts := Compile.compile_ts compile_op.

  Lemma read_list_no_atomics : forall l r,
    no_atomics (read_list l r).
  Proof.
    induction l; simpl; eauto.
  Qed.

  Hint Resolve read_list_no_atomics.

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
      traces_match_abs absR MailboxAPI.initP MailboxAPI.step MailServerDirAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailboxAPI.initP s1 ->
      absR s1 s2 ->
      MailServerDirAPI.initP s2.
  Proof.
    eauto.
  Qed.

End AtomicReader.
