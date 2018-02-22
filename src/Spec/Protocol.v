Require Import ConcurProc.
Require Import Helpers.
Require Import Relation_Operators.
Require Import Compile.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Protocol.

  Variable opT : Type -> Type.
  Variable State : Type.

  Definition OpProtocol := forall T, opT T -> nat -> State -> Prop.

  Variable lo_step : OpSemantics opT State.
  Variable op_allow : OpProtocol.

  Definition nilpotent_step : OpSemantics opT State :=
    fun T op tid s r s' evs =>
      ( op_allow op tid s /\
        lo_step op tid s r s' evs ) \/
      ( ~ op_allow op tid s /\
        s' = s /\
        evs = nil ).

  Definition restricted_step : OpSemantics opT State :=
    fun T op tid s r s' evs =>
      op_allow op tid s /\
      lo_step op tid s r s' evs.

  Variable loopInv : forall (s : State) (tid : nat), Prop.

  Inductive follows_protocol_proc (tid : nat) (s : State) :
    forall T (p : proc opT T), Prop :=
  | FollowsProtocolProcOp :
    forall T (op : opT T),
    op_allow op tid s ->
    follows_protocol_proc tid s (Op op)
  | FollowsProtocolProcBind :
    forall T1 T2 (p1 : proc _ T1) (p2 : T1 -> proc _ T2),
    follows_protocol_proc tid s p1 ->
    (forall r s',
      exec_any restricted_step tid s p1 r s' ->
      follows_protocol_proc tid s' (p2 r)) ->
    follows_protocol_proc tid s (Bind p1 p2)
  | FollowsProtocolProcUntil :
    forall T (p : T -> proc _ T) c v,
    loopInv s tid ->
    (forall s' v',
      loopInv s' tid ->
      follows_protocol_proc tid s' (p v')) ->
    (forall s' s'' r v',
      loopInv s' tid ->
      exec_any restricted_step tid s' (p v') r s'' ->
      loopInv s'' tid) ->
    follows_protocol_proc tid s (Until c p v)
  | FollowsProtocolProcRet :
    forall T (v : T),
    follows_protocol_proc tid s (Ret v)
  .


  Definition follows_protocol_s (ts : @threads_state opT) (s : State) :=
    forall tid T (p : proc _ T),
      ts [[ tid ]] = Proc p ->
      follows_protocol_proc tid s p.


  Variable allowed_stable :
    forall `(op : opT T) `(op' : opT T') tid tid' s s' r evs,
      tid <> tid' ->
      op_allow op tid s ->
      restricted_step op' tid' s r s' evs ->
      op_allow op tid s'.

  Variable loopInv_stable :
    forall `(op' : opT T') tid tid' s s' r evs,
      tid <> tid' ->
      loopInv s tid ->
      restricted_step op' tid' s r s' evs ->
      loopInv s' tid.

  Theorem follows_protocol_preserves_exec_tid' :
    forall tid `(p : proc _ T) s s' result evs,
      follows_protocol_proc tid s p ->
      exec_tid lo_step tid s p s' result evs ->
      exec_tid restricted_step tid s p s' result evs.
  Proof.
    intros.
    induction H0; simpl in *; intros; eauto;
      match goal with
      | H : follows_protocol_proc _ _ _ |- _ =>
        inversion H; clear H; repeat sigT_eq; subst
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
    forall tid `(p : proc _ T) s s' result evs,
      exec_tid restricted_step tid s p s' result evs ->
      exec_tid nilpotent_step tid s p s' result evs.
  Proof.
    intros.
    induction H; simpl in *; intros; eauto.
    constructor. firstorder.
    constructor.
    eapply atomic_exec_restricted_to_nilpotent; eauto.
  Qed.

  Theorem follows_protocol_preserves_exec_tid :
    forall tid `(p : proc _ T) s s' result evs,
      follows_protocol_proc tid s p ->
      exec_tid lo_step tid s p s' result evs ->
      exec_tid nilpotent_step tid s p s' result evs.
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
    forall `(p : proc opT T) tid s s' p' evs,
    follows_protocol_proc tid s p ->
    exec_tid lo_step tid s p s' (inr p') evs ->
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
    forall `(p : proc opT T) `(op' : opT T') tid tid' s s' r evs,
      tid <> tid' ->
      follows_protocol_proc tid s p ->
      restricted_step op' tid' s r s' evs ->
      follows_protocol_proc tid s' p.
  Proof.
    intros.
    induction H0; eauto.
  Qed.

  Hint Resolve follows_protocol_stable.

  Theorem exec_tid'_preserves_follows_protocol :
    forall `(p : proc opT T) `(p' : proc opT T') tid tid' s s' r evs,
      tid <> tid' ->
      follows_protocol_proc tid s p ->
      exec_tid restricted_step tid' s p' s' r evs ->
      no_atomics p' ->
      follows_protocol_proc tid s' p.
  Proof.
    intros.
    induction H1; intros; simpl in *; try congruence;
      match goal with
      | H : no_atomics _ |- _ =>
        inversion H; clear H; subst; repeat sigT_eq
      end; eauto.
  Qed.

  Theorem follows_protocol_s_exec_tid_upd :
    forall ts tid `(p : proc _ T) s s' result evs,
      follows_protocol_s ts s ->
      ts [[ tid ]] = Proc p ->
      exec_tid lo_step tid s p s' result evs ->
      no_atomics_ts ts ->
      follows_protocol_s ts [[ tid := match result with
                                      | inl _ => NoProc
                                      | inr p' => Proc p'
                                      end ]] s'.
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

End Protocol.

Hint Constructors follows_protocol_proc.
