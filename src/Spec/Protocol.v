Require Import ProofAutomation.
Require Import Helpers.Instances.

Require Import ConcurExec.
Require Import Relation_Operators.
Require Import Compile.
Require Import Equiv ProcMatch.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Section ExecOps.

  Variable State:Type.
  Variable Op:Type -> Type.
  Variable op_step: OpSemantics Op State.

  Definition exec_ops (s s' : State) : Prop :=
    clos_refl_trans_1n _
                       (fun s0 s1 =>
                          exists tid `(op' : Op T') r' evs,
                            op_step op' tid s0 r' s1 evs)
                       s s'.

  Lemma exec_ops_one : forall s s',
      forall T (op: Op T) tid r evs,
        op_step op tid s r s' evs ->
        exec_ops s s'.
  Proof.
    unfold exec_ops; intros.
    econstructor; [ | reflexivity ].
    descend; eauto.
  Qed.

  Global Instance exec_ops_pre : PreOrder exec_ops.
  Proof.
    unfold exec_ops.
    constructor; hnf; intros.
    reflexivity.
    etransitivity; eauto.
  Qed.

  Lemma exec_ops_reflexive : forall s,
      exec_ops s s.
  Proof.
    reflexivity.
  Qed.

End ExecOps.

Hint Resolve exec_ops_one.
Hint Resolve exec_ops_reflexive.

Section Protocol.

  Variable Op : Type -> Type.
  Variable State : Type.

  Definition OpProtocol := forall T, Op T -> nat -> State -> Prop.

  Variable lo_step : OpSemantics Op State.
  Variable op_allow : OpProtocol.

  Definition nilpotent_step : OpSemantics Op State :=
    fun T op tid s r s' evs =>
      ( op_allow op tid s /\
        lo_step op tid s r s' evs ) \/
      ( ~ op_allow op tid s /\
        s' = s /\
        evs = nil ).

  Definition restricted_step : OpSemantics Op State :=
    fun T op tid s r s' evs =>
      op_allow op tid s /\
      lo_step op tid s r s' evs.

  Definition spawn_follows_protocol (follows_protocol_proc: nat -> State -> forall T (p: proc Op T), Prop) tid (s: State) T (p: proc _ T) :=
    (forall tid',
        tid <> tid' ->
        forall s',
          exec_ops restricted_step s s' ->
          follows_protocol_proc tid' s' _ p).

  Theorem spawn_follows_protocol_stable : forall follows_protocol_proc
                                      tid s T (p: proc _ T) s'
                                      tid' T' (op: Op T') r evs,
      tid <> tid' ->
      spawn_follows_protocol follows_protocol_proc tid s p ->
      restricted_step op tid' s r s' evs ->
      spawn_follows_protocol follows_protocol_proc tid s' p.
  Proof.
    unfold spawn_follows_protocol; intros.
    eapply H0; eauto.
    transitivity s'; eauto.
  Qed.

  Theorem follows_protocol_implies_spawn_follows_protocol_subset :
    forall (follows_protocol_proc: nat -> State -> forall T (p: proc Op T), Prop)
      tid s T (p: proc _ T),
      (forall tid s, follows_protocol_proc tid s _ p) ->
      spawn_follows_protocol follows_protocol_proc tid s p.
  Proof.
    unfold spawn_follows_protocol in *; intros.
    eauto.
  Qed.

  Theorem spawn_follows_protocol_at_other_tid :
    forall follows_protocol_proc
      T (p: proc _ T) tid tid' s,
      tid <> tid' ->
      spawn_follows_protocol follows_protocol_proc tid s p ->
      follows_protocol_proc tid' s _ p.
  Proof.
    unfold spawn_follows_protocol; intros.
    eapply H0; eauto.
  Qed.

  Inductive follows_protocol_proc : forall (tid : nat) (s : State),
    forall T (p : proc Op T), Prop :=
  | FollowsProtocolProcOp :
    forall tid s T (op : Op T),
    op_allow op tid s ->
    follows_protocol_proc tid s (Call op)
  | FollowsProtocolProcBind :
    forall tid s T1 T2 (p1 : proc _ T1) (p2 : T1 -> proc _ T2),
    follows_protocol_proc tid s p1 ->
    (forall r s',
      exec_any restricted_step tid s p1 r s' ->
      follows_protocol_proc tid s' (p2 r)) ->
    follows_protocol_proc tid s (Bind p1 p2)
  | FollowsProtocolProcUntil :
    forall tid s T (p : option T -> proc _ T) c v,
    (forall s' v',
      follows_protocol_proc tid s' (p v')) ->
    follows_protocol_proc tid s (Until c p v)
  | FollowsProtocolProcRet :
    forall tid s T (v : T),
    follows_protocol_proc tid s (Ret v)
  | FollowsProtocolProcSpawn :
      forall tid s T (p: proc _ T),
        spawn_follows_protocol follows_protocol_proc tid s p ->
        follows_protocol_proc tid s (Spawn p)
  .

  Definition follows_protocol_s (ts : threads_state Op) (s : State) :=
    forall tid T (p : proc _ T),
      ts [[ tid ]] = Proc p ->
      follows_protocol_proc tid s p.

  Variable allowed_stable :
    forall `(op : Op T) `(op' : Op T') tid tid' s s' r evs,
      tid <> tid' ->
      op_allow op tid s ->
      restricted_step op' tid' s r s' evs ->
      op_allow op tid s'.

  Theorem follows_protocol_preserves_exec_tid' :
    forall tid `(p : proc _ T) s s' result spawned evs,
      follows_protocol_proc tid s p ->
      exec_tid lo_step tid s p s' result spawned evs ->
      exec_tid restricted_step tid s p s' result spawned evs.
  Proof.
    intros.
    induction H0; simpl in *; intros; eauto;
      match goal with
      | H : follows_protocol_proc _ _ _ |- _ =>
        invert H
      end; eauto.
    unfold restricted_step; eauto.
  Qed.

  Theorem atomic_exec_restricted_to_nilpotent :
    forall tid `(p : proc _ T) s s' result evs,
      atomic_exec restricted_step p tid s result s' evs ->
      atomic_exec nilpotent_step p tid s result s' evs.
  Proof.
    induction 1; eauto.
    constructor. firstorder.
  Qed.

  Theorem exec_tid_restricted_to_nilpotent :
    forall tid `(p : proc _ T) s s' result spawned evs,
      exec_tid restricted_step tid s p s' result spawned evs ->
      exec_tid nilpotent_step tid s p s' result spawned evs.
  Proof.
    intros.
    induction H; simpl in *; intros; eauto.
    constructor. firstorder.
    constructor.
    eapply atomic_exec_restricted_to_nilpotent; eauto.
  Qed.

  Theorem follows_protocol_preserves_exec_tid :
    forall tid `(p : proc _ T) s s' result spawned evs,
      follows_protocol_proc tid s p ->
      exec_tid lo_step tid s p s' result spawned evs ->
      exec_tid nilpotent_step tid s p s' result spawned evs.
  Proof.
    intros.
    eapply exec_tid_restricted_to_nilpotent.
    eapply follows_protocol_preserves_exec_tid'; eauto.
  Qed.

  Hint Resolve follows_protocol_preserves_exec_tid'.
  Hint Resolve follows_protocol_preserves_exec_tid.
  Hint Constructors exec_any.
  Hint Constructors follows_protocol_proc.

  Theorem exec_tid_preserves_follows_protocol :
    forall `(p : proc Op T) tid s s' p' spawned evs,
    follows_protocol_proc tid s p ->
    exec_tid lo_step tid s p s' (inr p') spawned evs ->
    follows_protocol_proc tid s' p'.
  Proof.
    intros.
    remember (inr p').
    generalize dependent p'.
    induction H0; intros; simpl in *; try congruence.

    + match goal with
      | H : follows_protocol_proc _ _ _ |- _ =>
        inversion H; clear H; repeat sigT_eq; subst
      end; eauto.

      intuition idtac.
      inversion Heqs0; clear Heqs0; subst.
      destruct result; eauto.

      econstructor; eauto.

    + remember H as H'; clear HeqH'.
      inversion H; clear H; subst; repeat sigT_eq.
      inversion Heqs0; clear Heqs0; subst.
      unfold until1.

      constructor; eauto.
      intros.

      destruct (Bool.bool_dec (c r) true); eauto.
  Qed.

  Theorem follows_protocol_stable :
    forall `(p : proc Op T) `(op' : Op T') tid tid' s s' r evs,
      tid <> tid' ->
      follows_protocol_proc tid s p ->
      restricted_step op' tid' s r s' evs ->
      follows_protocol_proc tid s' p.
  Proof.
    intros.
    generalize dependent tid'.
    induction H0; intros; eauto.
    constructor; intros.
    eauto using spawn_follows_protocol_stable.
  Qed.

  Hint Resolve follows_protocol_stable.

  Theorem exec_tid'_preserves_follows_protocol :
    forall `(p : proc Op T) `(p' : proc Op T') tid tid' s s' r spawned evs,
      tid <> tid' ->
      follows_protocol_proc tid s p ->
      exec_tid restricted_step tid' s p' s' r spawned evs ->
      no_atomics p' ->
      follows_protocol_proc tid s' p.
  Proof.
    intros.
    induction H1; intros; simpl in *; try congruence;
      match goal with
      | H : no_atomics _ |- _ =>
        invert H
      end; eauto.
  Qed.

  Theorem follows_protocol_s_exec_tid_upd :
    forall ts tid `(p : proc _ T) s s' result spawned evs,
      follows_protocol_s ts s ->
      ts [[ tid ]] = Proc p ->
      exec_tid lo_step tid s p s' result spawned evs ->
      no_atomics_ts ts ->
      follows_protocol_s (ts [[ tid := match result with
                                      | inl _ => NoProc
                                      | inr p' => Proc p'
                                      end ]]) s'.
  Proof.
    unfold follows_protocol_s; intros.
    destruct (tid0 == tid); subst.
    - autorewrite with t in *.
      destruct result; try congruence.
      repeat maybe_proc_inv.
      specialize (H _ _ _ H0).
      eapply exec_tid_preserves_follows_protocol; eauto.

    - autorewrite with t in *.
      eapply follows_protocol_preserves_exec_tid' in H1; eauto.
      specialize (H _ _ _ H3).
      eapply exec_tid'_preserves_follows_protocol; eauto.
  Qed.

  Variable opMidT : Type -> Type.
  Variable compile_op : forall T, opMidT T -> proc Op T.
  Variable compile_op_follows_protocol :
    forall tid s T (op : opMidT T), follows_protocol_proc tid s (compile_op op).

  Theorem compile_ts_follows_protocol_proc :
    forall ts tid `(p : proc _ T) s,
      no_atomics_ts ts ->
      (compile_ts compile_op ts) [[ tid ]] = Proc p ->
      follows_protocol_proc tid s p.
  Proof.
    intros.

    edestruct proc_match_pick with (tid := tid).
      eapply Compile.compile_ts_ok with (compile_op := compile_op); eauto.
    intuition congruence.
    repeat deex.
    match goal with
    | H1 : _ [[ tid ]] = Proc _,
      H2 : _ [[ tid ]] = Proc _ |- _ =>
      rewrite H1 in H2; clear H1; inversion H2; clear H2;
        subst; repeat sigT_eq
    end.

    clear dependent ts.
    generalize dependent s.
    generalize dependent tid.

    match goal with
    | H : Compile.compile_ok _ _ _ |- _ =>
      induction H; intros; eauto
    end.

    constructor.
    eapply follows_protocol_implies_spawn_follows_protocol_subset; eauto.
  Qed.

End Protocol.

Hint Constructors follows_protocol_proc.
