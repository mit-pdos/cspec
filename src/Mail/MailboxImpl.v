Require Import CSPEC.
Require Import MailboxAPI.
Require Import MailServerAPI.
Require Import MailServerLockAbsAPI.
Require Import FMapFacts.


Module AtomicReader' <:
  LayerImplMoversProtocolT
    MailServerLockAbsState
    MailboxOp    MailboxAPI MailboxRestrictedAPI
    MailServerOp MailServerLockAbsAPI
    MailboxProtocol.

  (* START CODE *)

  Fixpoint read_list (l : list (nat*nat)) (r : list ((nat*nat) * string)) :=
    match l with
    | nil =>
      _ <- Call MailboxOp.Unlock;
      Ret r
    | fn :: l' =>
      m <- Call (MailboxOp.Read fn);
      match m with
      | None => read_list l' r  
      | Some s => read_list l' (r ++ ((fn, s) :: nil))
      end
    end.

  Definition pickup_core :=
    _ <- Call MailboxOp.Lock;
    l <- Call MailboxOp.List;
    read_list l nil.

  Definition delete_core fn :=
    _ <- Call MailboxOp.Lock;
    _ <- Call (MailboxOp.Delete fn);
    _ <- Call MailboxOp.Unlock;
    Ret tt.

  Definition compile_op T (op : MailServerOp.Op T) : proc _ T :=
    match op with
    | MailServerOp.Deliver m => Call (MailboxOp.Deliver m)
    | MailServerOp.Pickup => pickup_core
    | MailServerOp.Delete fn => delete_core fn
    | MailServerOp.Ext extop => Call (MailboxOp.Ext extop)
    end.

  (* END CODE *)

  Lemma read_list_no_atomics : forall l r,
    no_atomics (read_list l r).
  Proof.
    induction l; simpl; eauto.
    intros. constructor; eauto.
    intros.
    destruct x; eauto.
  Qed.

  Hint Resolve read_list_no_atomics.

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
  Qed.


  Ltac step_inv :=
    match goal with
    | H : MailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailboxRestrictedAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailboxProtocol.step_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailServerLockAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailServerLockAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailboxRestrictedAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailboxProtocol.step_allow _ _ _) => econstructor.
  Hint Constructors MailboxAPI.xstep.
  Hint Constructors MailboxProtocol.xstep_allow.

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
      (MailboxOp.Read fn)
      (fun tid s => FMap.In fn (MailServerLockAbsState.maildir s)).
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
      MailboxOp.Unlock.
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
      MailboxOp.Lock.
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
      MailServerLockAbsState.locked s = Some tid ->
        MailServerLockAbsState.locked s' = Some tid.
  Proof.
    induction 1; eauto; intros.
    repeat deex.
    eapply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
    repeat step_inv; simpl in *; try congruence.
  Qed.

  Lemma mailbox_fn_monotonic :
    forall s s' tid fn,
      exec_others MailboxRestrictedAPI.step tid s s' ->
      MailServerLockAbsState.locked s = Some tid ->
      FMap.In fn (MailServerLockAbsState.maildir s) ->
        MailServerLockAbsState.locked s' = Some tid /\
        FMap.In fn (MailServerLockAbsState.maildir s').
  Proof.
    induction 1; eauto; intros.
    repeat deex.
    eapply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
    - repeat step_inv; simpl in *; try congruence.
    - repeat step_inv; simpl in *; try congruence; eauto.
  Qed.

  Hint Resolve FMap.is_permutation_in.

  Theorem ysa_movers_pickup_core :
    ysa_movers MailboxRestrictedAPI.step pickup_core.
  Proof.
    eapply RightMoversOne; eauto; intros.
    destruct r.

    eapply RightMoversDone.

    eapply OneNonMover; intros.

    eapply left_movers_impl with
      (P1 := fun tid s =>
        MailServerLockAbsState.locked s = Some tid /\
        Forall (fun fn => FMap.In fn (MailServerLockAbsState.maildir s)) r).

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

  Theorem ysa_movers_delete_core : forall fn,
    ysa_movers MailboxRestrictedAPI.step (delete_core fn).
  Proof.
    intros.

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

  Hint Resolve ysa_movers_pickup_core.
  Hint Resolve ysa_movers_delete_core.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailboxRestrictedAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
  Qed.

  Lemma read_list_exec : forall l r s s' evs v tid,
    List.Forall (fun fn => FMap.In fn (MailServerLockAbsState.maildir s)) l ->
    Forall (fun '(fn, m) => FMap.MapsTo fn m (MailServerLockAbsState.maildir s)) r ->
    atomic_exec MailboxRestrictedAPI.step
      (read_list l r) tid
      s v s' evs ->
    MailServerLockAbsState.maildir s' = MailServerLockAbsState.maildir s /\
    MailServerLockAbsState.locked s' = None /\
    evs = nil /\
    Forall (fun '(fn, m) => FMap.MapsTo fn m (MailServerLockAbsState.maildir s)) v /\
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
       -- eapply List.Forall_forall; intros.
          eapply in_app_or in H1; intuition idtac.
          * eapply List.Forall_forall in H0; eauto.
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

  Theorem compile_correct :
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

        eapply List.Forall_forall; intros.
        eapply FMap.is_permutation_in; eauto.
      }

      constructor.

    + repeat atomic_exec_inv.
      repeat step_inv; eauto.

    + repeat atomic_exec_inv.
      repeat step_inv.
      destruct s'; eauto.
  Qed.

  Lemma delete_follows_protocol : forall tid s fn,
    follows_protocol_proc
      MailboxAPI.step
      MailboxProtocol.step_allow
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
      MailboxProtocol.step_allow
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

  Theorem op_follows_protocol : forall tid s `(op : _ T),
    follows_protocol_proc
      MailboxAPI.step
      MailboxProtocol.step_allow
      tid s (compile_op op).
  Proof.
    destruct op; simpl; eauto.
  Qed.


  Theorem allowed_stable :
    forall `(op : MailboxOp.Op T) `(op' : MailboxOp.Op T') tid tid' s s' r evs,
      tid <> tid' ->
      MailboxProtocol.step_allow op tid s ->
      MailboxRestrictedAPI.step op' tid' s r s' evs ->
      MailboxProtocol.step_allow op tid s'.
  Proof.
    intros.
    destruct op; destruct op'; repeat step_inv; subst; eauto.
    all: simpl in *; try congruence.
  Qed.

  Theorem raw_step_ok :
    forall `(op : _ T) tid s r s' evs,
      restricted_step MailboxAPI.step MailboxProtocol.step_allow op tid s r s' evs ->
      MailboxRestrictedAPI.step op tid s r s' evs.
  Proof.
    eauto.
  Qed.

  Definition initP_compat : forall s, MailboxRestrictedAPI.initP s ->
                                 MailServerLockAbsAPI.initP s :=
    ltac:(auto).

  Definition raw_initP_compat : forall s, MailboxAPI.initP s ->
                                     MailboxRestrictedAPI.initP s :=
    ltac:(auto).

End AtomicReader'.


Module AtomicReader :=
  LayerImplMoversProtocol
    MailServerLockAbsState
    MailboxOp    MailboxAPI MailboxRestrictedAPI
    MailServerOp MailServerLockAbsAPI
    MailboxProtocol
    AtomicReader'.

Module AtomicReaderH' :=
  LayerImplMoversProtocolHT
    MailServerLockAbsState
    MailboxOp    MailboxAPI MailboxRestrictedAPI
    MailServerOp MailServerLockAbsAPI
    MailboxProtocol
    AtomicReader'
    UserIdx.

Module AtomicReaderH :=
  LayerImplMoversProtocol
    MailServerLockAbsHState
    MailboxHOp    MailboxHAPI MailboxRestrictedHAPI
    MailServerHOp MailServerLockAbsHAPI
    MailboxHProtocol
    AtomicReaderH'.
