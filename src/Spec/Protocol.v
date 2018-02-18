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
    fun T op tid s r s' =>
      ( op_allow op tid s /\
        lo_step op tid s r s' ) \/
      ( ~ op_allow op tid s /\
        s' = s ).

  Definition restricted_step : OpSemantics opT State :=
    fun T op tid s r s' =>
      op_allow op tid s /\
      lo_step op tid s r s'.

  Inductive exec_any (tid : nat) (s : State) :
    forall T (p : proc opT T) (r : T) (s' : State), Prop :=
  | ExecAnyOther :
    forall T (p : proc opT T) (r : T) (s' : State)
           T' (op' : opT T') tid' s0 r0,
    tid <> tid' ->
    restricted_step op' tid' s r0 s0 ->
    exec_any tid s0 p r s' ->
    exec_any tid s p r s'
  | ExecAnyThisDone :
    forall T (p : proc opT T) (r : T) (s' : State) evs,
    exec_tid restricted_step tid s p s' (inl r) evs ->
    exec_any tid s p r s'
  | ExecAnyThisMore :
    forall T (p p' : proc opT T) (s' s0 : State) r evs,
    exec_tid restricted_step tid s p s0 (inr p') evs ->
    exec_any tid s0 p' r s' ->
    exec_any tid s p r s'
  .

  Definition exec_others (tid : nat) (s s' : State) : Prop :=
    clos_refl_trans_1n _
      (fun s0 s1 =>
        exists tid' `(op' : opT T') r',
          tid' <> tid /\
          restricted_step op' tid' s0 r' s1)
      s s'.

  Lemma exec_any_op : forall `(op : opT T) tid r s s',
    exec_any tid s (Op op) r s' ->
      exists s0,
        exec_others tid s s0 /\
        restricted_step op tid s0 r s'.
  Proof.
    intros.
    remember (Op op).
    induction H; subst.
    - edestruct IHexec_any; eauto; intuition idtac.
      eexists; split; eauto.
      econstructor; eauto.
      do 4 eexists; split.
      eauto.
      unfold restricted_step in *; intuition eauto.
    - exists s; split.
      eapply rt1n_refl.
      exec_tid_inv; eauto.
    - exec_tid_inv.
  Qed.

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
      exec_any tid s p1 r s' ->
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
      exec_any tid s' (p v') r s'' ->
      loopInv s'' tid) ->
    follows_protocol_proc tid s (Until c p v)
  | FollowsProtocolProcLog :
    forall T (v : T),
    follows_protocol_proc tid s (Log v)
  | FollowsProtocolProcRet :
    forall T (v : T),
    follows_protocol_proc tid s (Ret v)
  .


  Definition follows_protocol_s (ts : @threads_state opT) (s : State) :=
    forall tid T (p : proc _ T),
      ts [[ tid ]] = Proc p ->
      follows_protocol_proc tid s p.


  Variable allowed_stable :
    forall `(op : opT T) `(op' : opT T') tid tid' s s' r,
      tid <> tid' ->
      op_allow op tid s ->
      restricted_step op' tid' s r s' ->
      op_allow op tid s'.

  Variable loopInv_stable :
    forall `(op' : opT T') tid tid' s s' r,
      tid <> tid' ->
      loopInv s tid ->
      restricted_step op' tid' s r s' ->
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
    forall `(p : proc opT T) `(op' : opT T') tid tid' s s' r,
      tid <> tid' ->
      follows_protocol_proc tid s p ->
      restricted_step op' tid' s r s' ->
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
