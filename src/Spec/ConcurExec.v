Require Export Trace.
Require Export ConcurProc.
Require Export FinMap.
Require Import ProofAutomation.
Require Import Helpers.ListStuff.
Require Import Helpers.FinMap.
Require Import Helpers.Instances.

Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import List.
Require Import Bool.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Section Proc.

  Variable Op: Type -> Type.
  Variable State : Type.

  Definition OpSemantics := forall T, Op T -> nat -> State -> T -> State -> list event -> Prop.
  Variable op_step : OpSemantics.

  Definition until1 T (c : T -> bool)
                      (p : option T -> proc Op T)
                      (v : option T) :=
    Bind (p v) (fun x => if bool_dec (c x) true then Ret x else Until c p (Some x)).


  Inductive atomic_exec : forall T, proc Op T -> nat -> State ->
                                    T -> State -> list event -> Prop :=

  | AtomicRet : forall T tid (v : T) s,
    atomic_exec (Ret v) tid s v s nil

  | AtomicBind : forall T1 T2 tid (p1 : proc Op T1) (p2 : T1 -> proc Op T2)
                        s0 s1 s2 ev1 ev2 (v1 : T1) (v2 : T2),
    atomic_exec p1 tid s0 v1 s1 ev1 ->
    atomic_exec (p2 v1) tid s1 v2 s2 ev2 ->
    atomic_exec (Bind p1 p2) tid s0 v2 s2 (ev1 ++ ev2)

  | AtomicOp : forall T tid (v : T) s s' op evs,
    op_step op tid s v s' evs ->
    atomic_exec (Prim op) tid s v s' evs

  | AtomicUntil : forall T (p : option T -> proc Op T) (c : T -> bool) v tid s r s' ev',
    atomic_exec (until1 c p v) tid s r s' ev' ->
    atomic_exec (Until c p v) tid s r s' ev'
  .


  Inductive exec_tid : forall T (tid : nat),
    State -> proc Op T ->
    State -> T + proc Op T -> maybe_proc Op -> list event -> Prop :=

  | ExecTidRet : forall tid T (v : T) s,
    exec_tid tid s (Ret v)
                 s (inl v)
                 NoProc nil

  | ExecTidOp : forall tid T (v : T) s s' op evs,
    op_step op tid s v s' evs ->
    exec_tid tid s (Prim op)
                 s' (inl v)
                 NoProc evs

  | ExecTidAtomic : forall tid T (v : T) ap s s' evs,
    atomic_exec ap tid s v s' evs ->
    exec_tid tid s (Atomic ap)
                 s' (inl v)
                 NoProc evs

  | ExecTidBind : forall tid T1 (p1 : proc Op T1) T2 (p2 : T1 -> proc Op T2) s s' result spawned evs,
    exec_tid tid s p1
                 s' result spawned evs ->
    exec_tid tid s (Bind p1 p2)
                 s' (inr
                     match result with
                     | inl r => p2 r
                     | inr p1' => Bind p1' p2
                     end
                    ) spawned evs

  | ExecTidUntil : forall tid T (p : option T -> proc Op T) (c : T -> bool) v s,
    exec_tid tid s (Until c p v)
                 s (inr (until1 c p v))
                 NoProc nil

  | ExecTidSpawn : forall tid T (p: proc Op T) s,
    exec_tid tid s (Spawn p)
                 s (inl tt)
                 (Proc p) nil
  .


  Inductive exec : State -> threads_state Op -> trace -> nat -> Prop :=

  | ExecOne : forall T tid tid' (ts : threads_state Op) trace p s s' evs result ctr spawned,
    ts tid = @Proc Op T p ->
    ts tid' = NoProc ->
    exec_tid tid s p s' result spawned evs ->
    exec s' (thread_upd (thread_upd ts tid' spawned) tid
              match result with
              | inl _ => NoProc
              | inr p' => Proc p'
              end) trace ctr ->
    exec s ts (prepend tid evs trace) (S ctr)

  | ExecExpired : forall (ts : threads_state Op) s,
    exec s ts TraceEmpty 0.


  Definition exec_prefix (s : State) (ts : threads_state Op) (tr : trace) : Prop :=
    exists n,
      exec s ts tr n.

  Theorem ExecPrefixOne
       : forall (T : Type)
           (tid : nat) (ts : threads_state Op) (tr : trace)
           (p : proc Op T) (s s' : State)
           (evs : list event) (result : T + proc Op T)
           (tid' : nat) spawned,
         thread_get ts tid = Proc p ->
         thread_get ts tid' = NoProc ->
         exec_tid tid s p s' result spawned evs ->
         exec_prefix s'
           (thread_upd (thread_upd ts tid' spawned) tid
             (match result with
              | inl _ => NoProc
              | inr p' => Proc p'
              end)) tr ->
         exec_prefix s ts (prepend tid evs tr).
  Proof.
    unfold exec_prefix; intros; deex.
    eexists; eapply ExecOne; eauto.
  Qed.


  Theorem exec_to_exec_prefix : forall s ts tr ctr,
    exec s ts tr ctr ->
    exec_prefix s ts tr.
  Proof.
    unfold exec_prefix; eauto.
  Qed.


  Inductive exec_any (tid : nat) (s : State) :
    forall T (p : proc Op T) (r : T) (s' : State), Prop :=
  | ExecAnyOther :
    forall T (p : proc Op T) (r : T) (s' : State)
           T' (op' : Op T') tid' s0 r0 evs,
    tid <> tid' ->
    op_step op' tid' s r0 s0 evs ->
    exec_any tid s0 p r s' ->
    exec_any tid s p r s'
  | ExecAnyThisDone :
    forall T (p : proc Op T) (r : T) (s' : State) spawned evs,
    exec_tid tid s p s' (inl r) spawned evs ->
    exec_any tid s p r s'
  | ExecAnyThisMore :
    forall T (p p' : proc Op T) (s' s0 : State) r spawned evs,
    exec_tid tid s p s0 (inr p') spawned evs ->
    exec_any tid s0 p' r s' ->
    exec_any tid s p r s'
  .

  Definition exec_others (tid : nat) (s s' : State) : Prop :=
    clos_refl_trans_1n _
      (fun s0 s1 =>
        exists tid' `(op' : Op T') r' evs,
          tid' <> tid /\
          op_step op' tid' s0 r' s1 evs)
      s s'.

  Global Instance exec_others_pre tid : PreOrder (exec_others tid).
  Proof.
    unfold exec_others.
    constructor; hnf; intros.
    reflexivity.
    etransitivity; eauto.
  Qed.

  Lemma exec_others_one : forall tid s s' tid' T (op: Op T) r evs,
      tid <> tid' ->
      op_step op tid' s r s' evs ->
      exec_others tid s s'.
  Proof.
    unfold exec_others; intros.
    econstructor; [ | reflexivity ].
    eauto 10.
  Qed.

  Lemma exec_any_op : forall `(op : Op T) tid r s s',
    exec_any tid s (Prim op) r s' ->
      exists s0 evs,
        exec_others tid s s0 /\
        op_step op tid s0 r s' evs.
  Proof.
    intros.
    remember (Prim op).
    induct H;
      repeat match goal with
             | [ H: forall _, Prim _ = Prim _ -> _ |- _ ] =>
               specialize (H _ eq_refl)
             end;
      propositional.
    - descend; split; [ | eauto ].
      etransitivity; eauto using exec_others_one.
    - invert H.
      descend; split; [ reflexivity | eauto ].
    - invert H.
  Qed.

  Lemma exec_others_trans :
    forall tid s0 s1 s2,
      exec_others tid s0 s1 ->
      exec_others tid s1 s2 ->
      exec_others tid s0 s2.
  Proof.
    etransitivity; eauto.
  Qed.

  Lemma exec_tid_exec_others :
    forall tid tid' `(p : proc Op T) s s' result spawned evs,
      tid <> tid' ->
      exec_tid tid' s p s' result spawned evs ->
      exec_others tid s s'.
  Proof.
    induction 2; propositional; eauto;
      try reflexivity.
    - econstructor; eauto 10.
      reflexivity.
    - induct H0; eauto 10; try reflexivity.
      eapply exec_others_trans; eauto.
      econstructor; eauto 10.
      constructor.
  Qed.

  Lemma exec_others_exec_any :
    forall tid s s' s'' `(p : proc Op T) v,
      exec_others tid s s' ->
      exec_any tid s' p v s'' ->
      exec_any tid s p v s''.
  Proof.
    induction 1; propositional; eauto using ExecAnyOther.
  Qed.

End Proc.

Hint Constructors exec.
Hint Constructors exec_any.
Hint Resolve exec_to_exec_prefix.
Hint Resolve exec_tid_exec_others.
Hint Resolve exec_others_exec_any.
Hint Resolve exec_others_trans.


Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 60, right associativity).

Notation "ts [[ tid ]]" := (thread_get ts tid)
  (at level 12, left associativity).

Notation "ts [[ tid := p ]]" := (thread_upd ts tid p)
                                  (at level 12, left associativity).

Section StepImpl.

  Hint Constructors exec_tid.
  Hint Constructors atomic_exec.

  Variable Op : Type -> Type.
  Variable State : Type.
  Variable op_step1 : OpSemantics Op State.
  Variable op_step2 : OpSemantics Op State.

  Variable StepImpl :
    forall `(op : Op TT) tid s r s' evs,
      op_step1 op tid s r s' evs ->
      op_step2 op tid s r s' evs.

  Theorem atomic_exec_step_impl :
    forall tid s `(p : proc _ T) s' r evs,
      atomic_exec op_step1 p tid s s' r evs ->
      atomic_exec op_step2 p tid s s' r evs.
  Proof.
    intros.
    induction H; eauto.
  Qed.

  Theorem exec_tid_step_impl :
    forall tid s `(p : proc _ T) s' r spawned evs,
      exec_tid op_step1 tid s p s' r spawned evs ->
      exec_tid op_step2 tid s p s' r spawned evs.
  Proof.
    intros.
    induct H; eauto.
    eapply atomic_exec_step_impl in H; eauto.
  Qed.

  Theorem exec_any_impl :
    forall tid s `(p : proc _ T) s' r,
      exec_any op_step1 tid s p r s' ->
      exec_any op_step2 tid s p r s'.
  Proof.
    intros.
    induct H; eauto.
    eapply exec_tid_step_impl in H; eauto.
    eapply exec_tid_step_impl in H; eauto.
  Unshelve.
    all: intros; eauto.
    exact (Ret r0).
  Qed.

End StepImpl.


Lemma thread_empty_inv : forall Op T (p' : proc Op T) tid,
  thread_empty [[ tid ]] = Proc p' ->
  False.
Proof.
  intros.
  rewrite empty_is_empty in H; congruence.
Qed.

Hint Extern 1 (exec_tid _ _ _ _ _ _ _) => econstructor.
Hint Extern 1 (atomic_exec _ _ _ _ _ _ _) => econstructor.

Ltac maybe_proc_inv := match goal with
  | H : Proc _ = NoProc |- _ =>
    solve [ exfalso; inversion H ]
  | H : NoProc = Proc _ |- _ =>
    solve [ exfalso; inversion H ]
  | H : ?a = ?a |- _ =>
    clear H
  | H : Proc _ = Proc _ |- _ =>
    inversion H; clear H; subst
  | H : existT _ _ _ = existT _ _ _ |- _ =>
    sigT_eq
  | H : existT _ _ _ = existT _ _ _ |- _ =>
    inversion H; clear H; subst
  end.

Ltac exec_tid_inv :=
  match goal with
  | H : exec_tid _ _ _ _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat maybe_proc_inv
  end;
  autorewrite with t in *.

Ltac atomic_exec_inv :=
  match goal with
  | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat maybe_proc_inv
  end;
  autorewrite with t in *.

(* compare thread ids and perform cleanup *)
Ltac cmp_ts tid1 tid2 :=
  destruct (tid1 == tid2); subst;
  try congruence;
  autorewrite with t in *.

Local Lemma exec_prefix_ts_eq : forall Op State (op_step: OpSemantics Op State) s ts ts' tr,
    exec_prefix op_step s ts' tr ->
    ts = ts' ->
    exec_prefix op_step s ts tr.
Proof.
  propositional.
Qed.

Local Lemma exec_ts_eq : forall Op State (op_step: OpSemantics Op State) s ts ts' tr ctr,
    exec op_step s ts' tr ctr ->
    ts = ts' ->
    exec op_step s ts tr ctr.
Proof.
  propositional.
Qed.

(* abstract the thread state in an exec goal (to deal with different update
forms) *)
Ltac abstract_ts :=
  match goal with
  | |- exec_prefix _ _ ?ts _ => eapply exec_prefix_ts_eq
  | |- exec _ _ ?ts _ _ => eapply exec_ts_eq
  end.

Local Lemma exec_prefix_tr_eq : forall Op State (op_step: OpSemantics Op State) s ts tr tr',
    exec_prefix op_step s ts tr' ->
    tr = tr' ->
    exec_prefix op_step s ts tr.
Proof.
  propositional.
Qed.

(* abstract the trace in an exec goal (to deal with different calls to
prepend/list append) *)
Ltac abstract_tr :=
  match goal with
  | |- exec_prefix _ _ _ ?tr => eapply exec_prefix_tr_eq
  end.
