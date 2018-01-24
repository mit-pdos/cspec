Require Import ConcurProc.
Require Import Helpers.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Protocol.

  Variable opT : Type -> Type.
  Variable State : Type.
  Variable StateView : Type.
  Variable ViewF : State -> nat -> StateView.

  Variable op_proto : forall {T} (op : opT T), StateView -> StateView -> Prop.

  Inductive follows_protocol_proc (old_state new_state : StateView) :
    forall T (p : proc opT T), Prop :=
  | FollowsProtocolProcOp :
    forall T (op : opT T),
    op_proto op old_state new_state ->
    follows_protocol_proc old_state new_state (Op op)
  | FollowsProtocolProcBind :
    forall T1 T2 (p1 : proc _ T1) (p2 : T1 -> proc _ T2) mid_state,
    follows_protocol_proc old_state mid_state p1 ->
    (forall x, follows_protocol_proc mid_state new_state (p2 x)) ->
    follows_protocol_proc old_state new_state (Bind p1 p2)
  | FollowsProtocolProcUntil :
    forall T (p : proc _ T) c,
    old_state = new_state ->
    follows_protocol_proc old_state new_state p ->
    follows_protocol_proc old_state new_state (Until c p)
  | FollowsProtocolProcAtomic :
    forall T (p : proc _ T),
    follows_protocol_proc old_state new_state p ->
    follows_protocol_proc old_state new_state (Atomic p)
  | FollowsProtocolProcLog :
    forall T (v : T),
    old_state = new_state ->
    follows_protocol_proc old_state new_state (Log v)
  | FollowsProtocolProcRet :
    forall T (v : T),
    old_state = new_state ->
    follows_protocol_proc old_state new_state (Ret v).

  Hint Constructors follows_protocol_proc.


  Definition follows_protocol_s (ts : @threads_state opT) (s : State) :=
    forall tid T (p : proc _ T),
      ts [[ tid ]] = Proc p ->
      exists new_state,
        follows_protocol_proc (ViewF s tid) new_state p.


  Variable lo_step : OpSemantics opT State.
  Variable hi_step : OpSemantics opT State.

  Variable op_proto_view : forall `(op : opT T) tid s v s' b,
    lo_step op tid s v s' ->
    op_proto op (ViewF s tid) b ->
    b = ViewF s' tid.

  Variable op_proto_step : forall `(op : opT T) tid s v s' b,
    lo_step op tid s v s' ->
    op_proto op (ViewF s tid) b ->
    hi_step op tid s v s'.

  Variable view_disjoint : forall `(op : opT T) tid tid' s s' r b,
    lo_step op tid s r s' ->
    op_proto op (ViewF s tid) b ->
    tid <> tid' ->
    ViewF s tid' = ViewF s' tid'.


  Theorem follows_protocol_atomic_view :
    forall `(p : proc opT T) tid s0 r s1 evs b,
    atomic_exec lo_step p tid s0 r s1 evs ->
    follows_protocol_proc (ViewF s0 tid) b p ->
    b = ViewF s1 tid.
  Proof.
    intros.
    generalize dependent b.
    induction H; simpl in *; intros; eauto;
      match goal with
      | H : follows_protocol_proc _ _ _ |- _ =>
        inversion H; clear H; repeat sigT_eq; subst
      end; eauto.
    - repeat deex.
      eapply IHatomic_exec1 in H5; subst.
      specialize (H7 v1); eauto.
    - erewrite <- IHatomic_exec. reflexivity.
      econstructor; eauto; intros.
      destruct (Bool.bool_dec (c x)).
      constructor; eauto.
      constructor; eauto.
  Qed.

  Theorem follows_protocol_atomic_exec : forall `(p : proc opT T) tid s v s' evs b,
    atomic_exec lo_step p tid s v s' evs ->
    follows_protocol_proc (ViewF s tid) b p ->
    atomic_exec hi_step p tid s v s' evs.
  Proof.
    intros.
    erewrite follows_protocol_atomic_view with (b0 := b) in H0; eauto.
    induction H; intros; eauto;
      match goal with
      | H : follows_protocol_proc _ _ _ |- _ =>
        inversion H; clear H; repeat sigT_eq; subst
      end; eauto.

    eapply follows_protocol_atomic_view in H5 as H5'; eauto; subst.
    eauto.

    constructor.
    eapply IHatomic_exec.
    econstructor; eauto; intros.
    destruct (Bool.bool_dec (c x)).
    constructor; eauto.
    constructor; eauto.
    congruence.
  Qed.

  Hint Resolve follows_protocol_atomic_exec.


  Theorem follows_protocol_exec_tid :
    forall ts tid `(p : proc _ T) s s' result evs,
      follows_protocol_s ts s ->
      ts [[ tid ]] = Proc p ->
      exec_tid lo_step tid s p s' result evs ->
      exec_tid hi_step tid s p s' result evs.
  Proof.
    intros.
    specialize (H tid _ p); intuition idtac; deex.
    generalize dependent ts.
    generalize dependent new_state.
    induction H1; simpl in *; intros; eauto;
      match goal with
      | H : follows_protocol_proc _ _ _ |- _ =>
        inversion H; clear H; repeat sigT_eq; subst
      end; eauto.

    constructor.
    eapply IHexec_tid.
    eauto.
    rewrite thread_upd_eq with (ts := ts). reflexivity.
  Qed.


  Theorem view_disjoint_atomic_exec : forall `(p : proc opT T) tid tid' s s' r evs b,
    atomic_exec lo_step p tid s r s' evs ->
    follows_protocol_proc (ViewF s tid) b p ->
    tid <> tid' ->
    ViewF s tid' = ViewF s' tid'.
  Proof.
    intros.
    generalize dependent b.
    induction H; simpl in *; intros; eauto;
      match goal with
      | H : follows_protocol_proc _ _ _ |- _ =>
        inversion H; clear H; repeat sigT_eq; subst
      end; eauto.

    intuition idtac.
    eapply follows_protocol_atomic_view in H6 as H6'; eauto; subst.
    erewrite H2; eauto.

    intuition idtac.
    eapply H0.
    econstructor; eauto; intros.
    destruct (Bool.bool_dec (c x)).
    constructor; eauto.
    constructor; eauto.
  Qed.

  Hint Resolve view_disjoint_atomic_exec.


  Theorem view_disjoint_exec_tid : forall `(p : proc opT T) tid tid' s s' r evs b,
    exec_tid lo_step tid s p s' r evs ->
    follows_protocol_proc (ViewF s tid) b p ->
    tid <> tid' ->
    ViewF s tid' = ViewF s' tid'.
  Proof.
    intros.
    generalize dependent b.
    induction H; simpl in *; intros; eauto;
      match goal with
      | H : follows_protocol_proc _ _ _ |- _ =>
        inversion H; clear H; repeat sigT_eq; subst
      end; eauto.
  Qed.


  Theorem follows_protocol_proc_exec_tid :
    forall `(p : proc opT T) tid s s' p' evs b,
    follows_protocol_proc (ViewF s tid) b p ->
    exec_tid lo_step tid s p s' (inr p') evs ->
    follows_protocol_proc (ViewF s' tid) b p'.
  Proof.
    intros.
    remember (inr p').
    generalize dependent p'.
    generalize dependent b.
    induction H0; intros; simpl in *; try congruence.

    match goal with
    | H : follows_protocol_proc _ _ _ |- _ =>
      inversion H; clear H; repeat sigT_eq; subst
    end; eauto.

    inversion Heqs0; clear Heqs0; subst.
    destruct result.
    - inversion H0; repeat sigT_eq; simpl in *; subst;
                    repeat sigT_eq; simpl in *; subst; eauto;
        match goal with
        | H : follows_protocol_proc _ _ _ |- _ =>
          inversion H; clear H; repeat sigT_eq; subst
        end; eauto.
      eapply op_proto_view in H2; eauto; subst; eauto.
      eapply follows_protocol_atomic_view in H2; eauto; subst; eauto.
    - specialize (IHexec_tid _ H4 _ eq_refl).
      simpl. eauto.
    - inversion Heqs0; clear Heqs0; subst.
      inversion H; clear H; repeat sigT_eq; subst.
      econstructor; eauto; intros.
      destruct (Bool.bool_dec (c x)).
      constructor; eauto.
      constructor; eauto.
  Qed.

  Theorem follows_protocol_s_exec_tid_upd :
    forall ts tid `(p : proc _ T) s s' result evs,
      follows_protocol_s ts s ->
      ts [[ tid ]] = Proc p ->
      exec_tid lo_step tid s p s' result evs ->
      follows_protocol_s ts [[ tid := match result with
                                      | inl _ => NoProc
                                      | inr p' => Proc p'
                                      end ]] s'.
  Proof.
    unfold follows_protocol_s; intros.
    destruct (tid == tid0); subst.
    - autorewrite with t in *.
      destruct result; try congruence.
      repeat maybe_proc_inv.
      specialize (H _ _ _ H0); deex.

      eexists.
      eapply follows_protocol_proc_exec_tid; eauto.

    - autorewrite with t in *.
      specialize (H _ _ _ H2) as Ha; deex.
      specialize (H _ _ _ H0) as Hb; deex.
      erewrite <- view_disjoint_exec_tid; eauto.
  Qed.

End Protocol.
