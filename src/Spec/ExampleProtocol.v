Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import ConcurProc.
Require Import Equiv.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import List.
Require Import Compile.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Opcodes *)

Inductive opT : Type -> Type :=
| Acquire : opT unit
| Release : opT unit
| Read : opT nat
| Write : nat -> opT unit.


(** State *)

Record State := mkState {
  Value : nat;
  Lock : option nat;
}.


(** Semantics *)

Inductive raw_step : forall T, opT T -> nat -> State -> T -> State -> Prop :=
| RawStepAcquire : forall tid v,
  raw_step Acquire tid (mkState v None) tt (mkState v (Some tid))
| RawStepRelease : forall tid v l,
  raw_step Release tid (mkState v l) tt (mkState v None)
| RawStepRead : forall tid v l,
  raw_step Read tid (mkState v l) v (mkState v l)
| RawStepWrite : forall tid v0 v l,
  raw_step (Write v) tid (mkState v0 l) tt (mkState v l).

Inductive proto_step : forall T, opT T -> nat -> State -> T -> State -> Prop :=
| ProtoStepAcquire : forall tid v,
  proto_step Acquire tid (mkState v None) tt (mkState v (Some tid))
| ProtoStepRelease : forall tid v,
  proto_step Release tid (mkState v (Some tid)) tt (mkState v None)
| ProtoStepReleaseHack0 : forall tid v,
  proto_step Release tid (mkState v None) tt (mkState v None)
| ProtoStepReleaseHack1 : forall tid tid' v,
  tid <> tid' ->
  proto_step Release tid (mkState v (Some tid')) tt (mkState v (Some tid'))
| ProtoStepRead : forall tid v,
  proto_step Read tid (mkState v (Some tid)) v (mkState v (Some tid))
| ProtoStepWrite : forall tid v0 v,
  proto_step (Write v) tid (mkState v0 (Some tid)) tt (mkState v (Some tid)).

Hint Extern 1 (raw_step _ _ _ _ _) => econstructor.
Hint Extern 1 (proto_step _ _ _ _ _) => econstructor.

Ltac step_inv :=
  match goal with
  | H : raw_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : proto_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.


(** Rules for following the protocol *)

Definition follows_protocol_op `(op : opT T) (tid : nat)
                                (old_owner : bool) (new_owner : bool) :=
  match op with
  | Acquire => old_owner = false /\ new_owner = true
  | Release => old_owner = true /\ new_owner = false
  | Read => old_owner = true /\ new_owner = true
  | Write _ => old_owner = true /\ new_owner = true
  end.

Definition lock_match s tid :=
  match Lock s with
  | Some tid' =>
    if tid' == tid then true else false
  | None => false
  end.


Theorem follows_protocol_step : forall `(op : opT T) tid s v s' b,
  raw_step op tid s v s' ->
  follows_protocol_op op tid (lock_match s tid) b ->
  proto_step op tid s v s'.
Proof.
  intros.
  destruct s.
  step_inv; unfold lock_match in *; simpl in *.
  - eauto.
  - destruct Lock0; [ destruct (n == tid) | ]; subst; simpl in *;
      intuition eauto; congruence.
  - destruct Lock0; [ destruct (n == tid) | ]; subst; simpl in *;
      intuition eauto; congruence.
  - destruct Lock0; [ destruct (n == tid) | ]; subst; simpl in *;
      intuition eauto; congruence.
Qed.

Hint Resolve follows_protocol_step.


Inductive follows_protocol_proc (tid : nat) (old_owner : bool) (new_owner : bool) :
  forall T (p : proc opT T), Prop :=
| FollowsProtocolProcOp :
  forall T (op : opT T),
  follows_protocol_op op tid old_owner new_owner ->
  follows_protocol_proc tid old_owner new_owner (Op op)
| FollowsProtocolProcBind :
  forall T1 T2 (p1 : proc opT T1) (p2 : T1 -> proc opT T2) mid_owner,
  follows_protocol_proc tid old_owner mid_owner p1 ->
  (forall x, follows_protocol_proc tid mid_owner new_owner (p2 x)) ->
  follows_protocol_proc tid old_owner new_owner (Bind p1 p2)
| FollowsProtocolProcUntil :
  forall T (p : proc opT T) c,
  old_owner = new_owner ->
  follows_protocol_proc tid old_owner new_owner p ->
  follows_protocol_proc tid old_owner new_owner (Until c p)
| FollowsProtocolProcAtomic :
  forall T (p : proc opT T),
  follows_protocol_proc tid old_owner new_owner p ->
  follows_protocol_proc tid old_owner new_owner (Atomic p)
| FollowsProtocolProcLog :
  forall T (v : T),
  old_owner = new_owner ->
  follows_protocol_proc tid old_owner new_owner (Log v)
| FollowsProtocolProcRet :
  forall T (v : T),
  old_owner = new_owner ->
  follows_protocol_proc tid old_owner new_owner (Ret v).

Hint Constructors follows_protocol_proc.


Lemma follows_protocol_op_owner : forall `(op : opT T) tid s v s' b,
  raw_step op tid s v s' ->
  follows_protocol_op op tid (lock_match s tid) b ->
  b = lock_match s' tid.
Proof.
  intros; step_inv; unfold lock_match in *; simpl in *;
    intuition try congruence.
  destruct (tid == tid); congruence.
Qed.

Theorem follows_protocol_atomic_owner :
  forall `(p : proc opT T) tid s0 r s1 evs b,
  atomic_exec raw_step p tid s0 r s1 evs ->
  follows_protocol_proc tid (lock_match s0 tid) b p ->
  b = lock_match s1 tid.
Proof.
  intros.
  generalize dependent b.
  induction H; simpl in *; intros; eauto;
    match goal with
    | H : follows_protocol_proc _ _ _ _ |- _ =>
      inversion H; clear H; repeat sigT_eq; subst
    end; eauto.
  - repeat deex.
    eapply IHatomic_exec1 in H5; subst.
    specialize (H7 v1); eauto.
  - eapply follows_protocol_op_owner; eauto.
  - erewrite <- IHatomic_exec. reflexivity.
    econstructor; eauto; intros.
    destruct (Bool.bool_dec (c x)).
    constructor; eauto.
    constructor; eauto.
Qed.


Theorem follows_protocol_atomic : forall `(p : proc opT T) tid s v s' evs b,
  atomic_exec raw_step p tid s v s' evs ->
  follows_protocol_proc tid (lock_match s tid) b p ->
  atomic_exec proto_step p tid s v s' evs.
Proof.
  intros.
  erewrite follows_protocol_atomic_owner with (b0 := b) in H0; eauto.
  induction H; intros; eauto;
    match goal with
    | H : follows_protocol_proc _ _ _ _ |- _ =>
      inversion H; clear H; repeat sigT_eq; subst
    end; eauto.

  eapply follows_protocol_atomic_owner in H5 as H5'; eauto; subst.
  eauto.

  constructor.
  eapply IHatomic_exec.
  econstructor; eauto; intros.
  destruct (Bool.bool_dec (c x)).
  constructor; eauto.
  constructor; eauto.
  congruence.
Qed.

Hint Resolve follows_protocol_atomic.


Definition follows_protocol (ts : @threads_state opT) (s : State) :=
  forall tid T (p : proc _ T),
    ts [[ tid ]] = Proc p ->
    exists b,
      follows_protocol_proc tid (lock_match s tid) b p.

Lemma follows_protocol_exec_tid :
  forall ts tid `(p : proc _ T) s s' result evs,
    follows_protocol ts s ->
    ts [[ tid ]] = Proc p ->
    exec_tid raw_step tid s p s' result evs ->
    exec_tid proto_step tid s p s' result evs.
Proof.
  intros.
  specialize (H tid _ p); intuition idtac; deex.
  generalize dependent ts.
  generalize dependent b.
  induction H1; simpl in *; intros; eauto;
    match goal with
    | H : follows_protocol_proc _ _ _ _ |- _ =>
      inversion H; clear H; repeat sigT_eq; subst
    end; eauto.

  constructor.
  eapply IHexec_tid.
  eauto.
  rewrite thread_upd_eq with (ts := ts). reflexivity.
Qed.


Lemma lock_match_op_ne : forall `(op : opT T) tid tid' s s' r b,
  raw_step op tid s r s' ->
  follows_protocol_op op tid (lock_match s tid) b ->
  tid <> tid' ->
  lock_match s tid' = lock_match s' tid'.
Proof.
  intros.
  step_inv; unfold lock_match in *; simpl in *.
  destruct (tid == tid'); congruence.
  all: destruct l; eauto.
  destruct (n == tid); destruct (n == tid'); subst; intuition congruence.
Qed.

Hint Resolve lock_match_op_ne.


Lemma lock_match_atomic_ne : forall `(p : proc opT T) tid tid' s s' r evs b,
  atomic_exec raw_step p tid s r s' evs ->
  follows_protocol_proc tid (lock_match s tid) b p ->
  tid <> tid' ->
  lock_match s tid' = lock_match s' tid'.
Proof.
  intros.
  generalize dependent b.
  induction H; simpl in *; intros; eauto;
    match goal with
    | H : follows_protocol_proc _ _ _ _ |- _ =>
      inversion H; clear H; repeat sigT_eq; subst
    end; eauto.

  intuition idtac.
  eapply follows_protocol_atomic_owner in H6 as H6'; eauto; subst.
  erewrite H2; eauto.

  intuition idtac.
  eapply H0.
  econstructor; eauto; intros.
  destruct (Bool.bool_dec (c x)).
  constructor; eauto.
  constructor; eauto.
Qed.

Hint Resolve lock_match_atomic_ne.


Lemma lock_match_exec_tid_ne : forall `(p : proc opT T) tid tid' s s' r evs b,
  exec_tid raw_step tid s p s' r evs ->
  follows_protocol_proc tid (lock_match s tid) b p ->
  tid <> tid' ->
  lock_match s tid' = lock_match s' tid'.
Proof.
  intros.
  generalize dependent b.
  induction H; simpl in *; intros; eauto;
    match goal with
    | H : follows_protocol_proc _ _ _ _ |- _ =>
      inversion H; clear H; repeat sigT_eq; subst
    end; eauto.
Qed.

Lemma follows_protocol_proc_exec_tid :
  forall `(p : proc opT T) tid s s' p' evs b,
  follows_protocol_proc tid (lock_match s tid) b p ->
  exec_tid raw_step tid s p s' (inr p') evs ->
  follows_protocol_proc tid (lock_match s' tid) b p'.
Proof.
  intros.
  remember (inr p').
  generalize dependent p'.
  generalize dependent b.
  induction H0; intros; simpl in *; try congruence.

  match goal with
  | H : follows_protocol_proc _ _ _ _ |- _ =>
    inversion H; clear H; repeat sigT_eq; subst
  end; eauto.

  inversion Heqs0; clear Heqs0; subst.
  destruct result.
  - inversion H0; repeat sigT_eq; simpl in *; subst;
                  repeat sigT_eq; simpl in *; subst; eauto;
      match goal with
      | H : follows_protocol_proc _ _ _ _ |- _ =>
        inversion H; clear H; repeat sigT_eq; subst
      end; eauto.
    eapply follows_protocol_op_owner in H2; eauto; subst; eauto.
    eapply follows_protocol_atomic_owner in H2; eauto; subst; eauto.
  - specialize (IHexec_tid _ H4 _ eq_refl).
    simpl. eauto.
  - inversion Heqs0; clear Heqs0; subst.
    inversion H; clear H; repeat sigT_eq; subst.
    econstructor; eauto; intros.
    destruct (Bool.bool_dec (c x)).
    constructor; eauto.
    constructor; eauto.
Qed.

Lemma follows_protocol_exec_tid_upd :
  forall ts tid `(p : proc _ T) s s' result evs,
    follows_protocol ts s ->
    ts [[ tid ]] = Proc p ->
    exec_tid raw_step tid s p s' result evs ->
    follows_protocol ts [[ tid := match result with
                                  | inl _ => NoProc
                                  | inr p' => Proc p'
                                  end ]] s'.
Proof.
  unfold follows_protocol; intros.
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
    erewrite <- lock_match_exec_tid_ne; eauto.
Qed.

Hint Resolve follows_protocol_exec_tid.
Hint Resolve follows_protocol_exec_tid_upd.


(** Protocol establishment *)

Hint Constructors exec.

Theorem protocol_ok :
  forall s ts tr,
    follows_protocol ts s ->
    exec_prefix raw_step s ts tr ->
    exec_prefix proto_step s ts tr.
Proof.
  intros.
  destruct H0.
  induction H0; eauto.
  specialize (H tid _ p) as Htid.
  intuition idtac; repeat deex.
  eapply ExecPrefixOne; eauto.
Qed.
