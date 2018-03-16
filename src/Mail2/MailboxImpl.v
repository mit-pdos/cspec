Require Import POCS.
Require Import String.
Require Import MailboxAPI.
Require Import MailServerAPI.
Require Import MailServerLockAbsAPI.
Require Import FMapFacts.


Module AtomicReaderRestricted <: LayerImplFollowsRule MailboxRestrictedAPI MailServerLockAbsAPI MailboxLockingRule.

  Fixpoint read_list (l : list (nat*nat)) (r : list ((nat*nat) * string)) :=
    match l with
    | nil =>
      _ <- Op MailboxAPI.Unlock;
      Ret r
    | fn :: l' =>
      m <- Op (MailboxAPI.Read fn);
      match m with
      | None => read_list l' r  
      | Some s => read_list l' (r ++ ((fn, s) :: nil))
      end
    end.

  Definition pickup_core :=
    _ <- Op MailboxAPI.Lock;
    l <- Op MailboxAPI.List;
    read_list l nil.

  Definition delete_core fn :=
    _ <- Op MailboxAPI.Lock;
    _ <- Op (MailboxAPI.Delete fn);
    _ <- Op MailboxAPI.Unlock;
    Ret tt.

  Definition compile_op T (op : MailServerLockAbsAPI.opT T) : proc _ T :=
    match op with
    | MailServerAPI.Deliver m => Op (MailboxAPI.Deliver m)
    | MailServerAPI.Pickup => pickup_core
    | MailServerAPI.Delete fn => delete_core fn
    | MailServerAPI.GetRequest => Op (MailboxAPI.GetRequest)
    | MailServerAPI.Respond r => Op (MailboxAPI.Respond r)
    end.

  Ltac step_inv :=
    match goal with
    | H : MailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailboxRestrictedAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailboxRestrictedAPI.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailServerLockAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailServerLockAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailboxRestrictedAPI.step _ _ _ _ _ _) => econstructor.
  Hint Constructors MailboxAPI.xstep.
  Hint Constructors MailboxRestrictedAPI.step_allow.

  Hint Resolve FMap.mapsto_in.
  Hint Resolve FMap.mapsto_add_ne'.
  Hint Resolve FMap.mapsto_add_ne.
  Hint Resolve FMap.add_incr.
  Hint Resolve FMap.add_mapsto.
  Hint Resolve FMap.in_add_ne.
  Hint Resolve FMap.remove_not_in.
  Hint Resolve FMap.mapsto_remove_ne.

  Lemma read_left_mover : forall fn,
    left_mover_pred
      MailboxRestrictedAPI.step
      (MailboxAPI.Read fn)
      (fun tid s => FMap.In fn (MailServerLockAbsAPI.maildir s)).
  Proof.
    split.
    - unfold enabled_stable, enabled_in; intros; repeat deex.
      unfold MailboxRestrictedAPI.step, MailboxAPI.step, restricted_step.
      destruct rM; try congruence.
      + repeat step_inv; eauto 10; simpl in *; try congruence.
        destruct (fn == fn0); subst; eauto 10.
      + repeat step_inv; eauto 7; simpl in *; try congruence.
        destruct (fn0 == fn); subst; eauto 10.
    - intros; repeat step_inv; eauto 10; repeat deex; simpl in *; try congruence.
      + destruct (fn0 == fn); subst; try congruence.
        eauto 10.
      + destruct (fn0 == fn); subst; try congruence.
        eauto 15.
  Qed.

  Lemma unlock_left_mover :
    left_mover
      MailboxRestrictedAPI.step
      MailboxAPI.Unlock.
  Proof.
    split.
    - unfold enabled_stable, enabled_in; intros; repeat deex.
      unfold MailboxRestrictedAPI.step, MailboxAPI.step, restricted_step.
      repeat step_inv; eauto 7; simpl in *; try congruence.
    - intros; repeat step_inv; eauto 10; repeat deex; simpl in *; try congruence.
  Qed.

  Lemma lock_right_mover :
    right_mover
      MailboxRestrictedAPI.step
      MailboxAPI.Lock.
  Proof.
    unfold right_mover; intros.
    repeat step_inv; simpl in *; try congruence; eauto 10.
  Qed.

  Hint Resolve read_left_mover.
  Hint Resolve unlock_left_mover.
  Hint Resolve lock_right_mover.

  Hint Resolve FMap.add_incr.

  Lemma lock_monotonic :
    forall s s' tid,
      exec_others MailboxRestrictedAPI.step tid s s' ->
      MailServerLockAbsAPI.locked s = Some tid ->
        MailServerLockAbsAPI.locked s' = Some tid.
  Proof.
    induction 1; eauto; intros.
    repeat deex.
    eapply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
    repeat step_inv; simpl in *; try congruence.
  Qed.

  Lemma mailbox_fn_monotonic :
    forall s s' tid fn,
      exec_others MailboxRestrictedAPI.step tid s s' ->
      MailServerLockAbsAPI.locked s = Some tid ->
      FMap.In fn (MailServerLockAbsAPI.maildir s) ->
        MailServerLockAbsAPI.locked s' = Some tid /\
        FMap.In fn (MailServerLockAbsAPI.maildir s').
  Proof.
    induction 1; eauto; intros.
    repeat deex.
    eapply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
    - repeat step_inv; simpl in *; try congruence.
    - repeat step_inv; simpl in *; try congruence; eauto.
  Qed.

  Hint Resolve FMap.is_permutation_in.

  Theorem pickup_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailboxRestrictedAPI.step
      (Bind (compile_op MailServerAPI.Pickup) rx)
      (Bind (atomize compile_op MailServerAPI.Pickup) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold pickup_core, ysa_movers.

    eapply RightMoversOne; eauto; intros.
    destruct r.

    eapply RightMoversDone.

    eapply OneNonMover; intros.

    eapply left_movers_impl with
      (P1 := fun tid s =>
        MailServerLockAbsAPI.locked s = Some tid /\
        Forall (fun fn => FMap.In fn (MailServerLockAbsAPI.maildir s)) r).

    {
      generalize (@nil ((nat*nat) * string)).
      induction r; simpl; eauto; intros.

      {
        constructor; eauto.
        intuition eauto.
        destruct s; unfold enabled_in.
        eauto 10.
      }

      constructor; intuition idtac.

      - eapply left_mover_pred_impl; eauto.
        intuition idtac.
        inversion H1; clear H1; subst.
        eauto.

      - inversion H1; clear H1; subst.
        eapply FMap.in_mapsto_exists in H3; deex.
        destruct s; simpl in *.
        do 2 eexists; econstructor; eauto.

      - destruct r0; subst; try congruence.
       ++ eapply left_movers_impl; eauto.
          intros; repeat deex.
          inversion H2; clear H2; subst.

          eapply exec_any_op in H0; repeat deex.
          eapply mailbox_fn_monotonic in H0 as H0'; [ | intuition eauto.. ].
          repeat step_inv.

          eapply mailbox_fn_monotonic in H1; intuition eauto.

          eapply Forall_impl; eauto; intros; simpl in *.
          eapply mailbox_fn_monotonic; eauto.
          eapply mailbox_fn_monotonic; eauto.

      ++  eapply left_movers_impl; eauto.
          intros; repeat deex.
          inversion H2; clear H2; subst.

          eapply exec_any_op in H0; repeat deex.
          eapply mailbox_fn_monotonic in H0 as H0'; [ | intuition eauto.. ].
          repeat step_inv.

          eapply mailbox_fn_monotonic in H1; intuition eauto.

          eapply Forall_impl; eauto; intros; simpl in *.
          eapply mailbox_fn_monotonic; eauto.
          eapply mailbox_fn_monotonic; eauto.
    }

    intros; repeat deex.
    eapply exec_any_op in H2; repeat deex.
    eapply exec_any_op in H0; repeat deex.
    repeat step_inv.

    eapply lock_monotonic in H3; simpl in *; subst; [ | congruence ].
    eapply lock_monotonic in H0; simpl in *; subst; [ | congruence ].
    eapply lock_monotonic in H1; simpl in *; subst; [ | congruence ].
    eauto.

    eapply lock_monotonic in H3; simpl in *; subst; [ | congruence ].
    eapply lock_monotonic in H0; simpl in *; subst; [ | congruence ].

    eapply Forall_in'; intros.
    eapply mailbox_fn_monotonic in H1; intuition eauto.
  Qed.

  Theorem delete_atomic : forall `(rx : _ -> proc _ T) fn,
    trace_incl MailboxRestrictedAPI.step
      (Bind (compile_op (MailServerAPI.Delete fn)) rx)
      (Bind (atomize compile_op (MailServerAPI.Delete fn)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold delete_core, ysa_movers.

    eapply RightMoversOne; eauto; intros.
    eapply RightMoversDone.
    eapply OneNonMover; intros.
    eapply LeftMoversOne; eauto.

    intros.
    repeat deex.

    eapply exec_any_op in H2; repeat deex.
    eapply exec_any_op in H0; repeat deex.
    repeat step_inv.

    eapply lock_monotonic in H3; simpl in *; subst; [ | congruence ].
    eapply lock_monotonic in H1; simpl in *; subst; [ | congruence ].

    destruct s.
    do 3 eexists. eauto.
  Qed.

  Lemma read_list_exec : forall l r s s' evs v tid,
    List.Forall (fun fn => FMap.In fn (MailServerLockAbsAPI.maildir s)) l ->
    Forall (fun '(fn, m) => FMap.MapsTo fn m (MailServerLockAbsAPI.maildir s)) r ->
    atomic_exec MailboxRestrictedAPI.step
      (read_list l r) tid
      s v s' evs ->
    MailServerLockAbsAPI.maildir s' = MailServerLockAbsAPI.maildir s /\
    MailServerLockAbsAPI.locked s' = None /\
    evs = nil /\
    Forall (fun '(fn, m) => FMap.MapsTo fn m (MailServerLockAbsAPI.maildir s)) v /\
    map fst r ++ l = map fst v.
  Proof.
    induction l; intros.
    - repeat atomic_exec_inv.
      repeat step_inv.
      rewrite app_nil_r.
      eauto.
    - atomic_exec_inv.
      inversion H11; clear H11; subst; repeat sigT_eq.
      destruct v1; subst; try congruence.
      + edestruct IHl; [ | | eauto | ]; repeat step_inv.
        all: try inversion H7; subst; try congruence.
       -- inversion H; subst; eauto.
       -- eapply Forall_forall; intros.
          eapply in_app_or in H1; intuition idtac.
          * eapply Forall_forall in H0; eauto.
          * repeat match goal with
            | H : In _ _ |- _ => inversion H; clear H; subst
            end; eauto.
            inversion H8; subst; eauto.
       -- rewrite map_app in *.
          rewrite <- app_assoc in *.
          simpl in *.
          eauto.
      + exfalso.
        eapply Forall_inv in H.
        repeat step_inv.
        congruence.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op MailboxRestrictedAPI.step MailServerLockAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      repeat step_inv; eauto 10.

    + atomic_exec_inv.
      atomic_exec_inv.
      eapply read_list_exec in H11.
      {
        simpl in *.
        repeat atomic_exec_inv.
        repeat step_inv; subst; eauto.
        simpl in *; subst.
        destruct s'; simpl in *; subst.
        econstructor.

        eapply FMap.is_permutation_key_to_kv; eauto.
      }

      {
        clear H11.
        repeat atomic_exec_inv.
        repeat step_inv.

        eapply Forall_forall; intros.
        eapply FMap.is_permutation_in; eauto.
      }

      constructor.

    + repeat atomic_exec_inv.
      repeat step_inv; eauto.

    + repeat atomic_exec_inv.
      repeat step_inv.
      destruct s'; eauto.

    + repeat atomic_exec_inv.
      repeat step_inv.
      destruct s'; eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op MailboxRestrictedAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op; try trace_incl_simple.

    rewrite pickup_atomic.
    eapply trace_incl_bind_a; eauto.

    rewrite delete_atomic.
    eapply trace_incl_bind_a; eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts MailboxRestrictedAPI.step MailServerLockAbsAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : MailboxRestrictedAPI.State) (s2 : MailServerLockAbsAPI.State) :=
    s1 = s2.

  Definition compile_ts := Compile.compile_ts compile_op.

  Lemma read_list_no_atomics : forall l r,
    no_atomics (read_list l r).
  Proof.
    induction l; simpl; eauto.
    intros. constructor; eauto.
    intros.
    destruct x; eauto.
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
      traces_match_abs absR MailboxRestrictedAPI.initP MailboxRestrictedAPI.step MailServerLockAbsAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailboxRestrictedAPI.initP s1 ->
      absR s1 s2 ->
      MailServerLockAbsAPI.initP s2.
  Proof.
    eauto.
  Qed.


  Lemma delete_follows_protocol : forall tid s fn,
    follows_protocol_proc
      MailboxAPI.step
      MailboxRestrictedAPI.step_allow
      tid s (delete_core fn).
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.

    eapply exec_any_op in H; repeat deex.
      unfold restricted_step in *; intuition idtac.
      repeat step_inv.

    constructor; intros.
      constructor; intros. eauto.

    eapply exec_any_op in H0; repeat deex.
      eapply lock_monotonic in H0; try reflexivity.
      unfold restricted_step in *; intuition idtac.
      repeat step_inv.
      simpl in *; subst.

    constructor; intros.
      constructor; intros. eauto.

    constructor; intros.
  Qed.

  Lemma pickup_follows_protocol : forall tid s,
    follows_protocol_proc
      MailboxAPI.step
      MailboxRestrictedAPI.step_allow
      tid s (pickup_core).
  Proof.
    intros.
    constructor; intros.
      constructor; intros. eauto.

    eapply exec_any_op in H; repeat deex.
      unfold restricted_step in *; intuition idtac.
      repeat step_inv.

    constructor; intros.
      constructor; intros. eauto.

    eapply exec_any_op in H0; repeat deex.
      eapply lock_monotonic in H0; try reflexivity.
      unfold restricted_step in *; intuition idtac.
      repeat step_inv.
      simpl in *; subst.

    clear.
    generalize dependent mbox0.
    generalize (@nil ((nat*nat) * string)).
    induction r; simpl; intros.

    - constructor; intros.
        constructor; intros. eauto.

      constructor; intros.

    - constructor; intros.
        constructor; intros. eauto.

      eapply exec_any_op in H; repeat deex.
        eapply lock_monotonic in H; try reflexivity.
        unfold restricted_step in *; intuition idtac.
        repeat step_inv; simpl in *; subst; eauto.
  Qed.

  Hint Resolve delete_follows_protocol.
  Hint Resolve pickup_follows_protocol.


  Theorem compile_ts_follows_protocol :
    forall ts,
      no_atomics_ts ts ->
      MailboxLockingRule.follows_protocol (compile_ts ts).
  Proof.
    unfold compile_ts.
    unfold MailboxLockingRule.follows_protocol.
    unfold follows_protocol_s.
    intros.
    eapply compile_ts_follows_protocol_proc; try eassumption.
    intros.

    destruct op; simpl; eauto.
  Qed.

End AtomicReaderRestricted.


Module AtomicReaderRestricted' <: LayerImplRequiresRule MailboxAPI MailboxRestrictedAPI MailboxLockingRule.

  Import MailboxLockingRule.

  Definition absR (s1 : MailboxAPI.State) (s2 : MailboxRestrictedAPI.State) :=
    s1 = s2.

  Ltac step_inv :=
    match goal with
    | H : MailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailboxRestrictedAPI.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailboxRestrictedAPI.step _ _ _ _ _ _ |- _ =>
      destruct H; intuition idtac
    end.

  Theorem allowed_stable :
    forall `(op : MailboxAPI.opT T) `(op' : MailboxAPI.opT T') tid tid' s s' r evs,
      tid <> tid' ->
      MailboxRestrictedAPI.step_allow op tid s ->
      MailboxRestrictedAPI.step op' tid' s r s' evs ->
      MailboxRestrictedAPI.step_allow op tid s'.
  Proof.
    intros.
    destruct op; destruct op'; repeat step_inv; subst; eauto.
    all: simpl in *; try congruence.
  Qed.

  Definition compile_ts (ts : @threads_state MailboxRestrictedAPI.opT) := ts.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold compile_ts; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailboxAPI.initP s1 ->
      absR s1 s2 ->
      MailboxRestrictedAPI.initP s2.
  Proof.
    eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts,
      follows_protocol ts ->
      no_atomics_ts ts ->
      traces_match_abs absR
        MailboxAPI.initP
        MailboxAPI.step
        MailboxRestrictedAPI.step (compile_ts ts) ts.
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

End AtomicReaderRestricted'.


Module AtomicReader :=
  LinkWithRule MailboxAPI MailboxRestrictedAPI MailServerLockAbsAPI MailboxLockingRule
               AtomicReaderRestricted' AtomicReaderRestricted.
