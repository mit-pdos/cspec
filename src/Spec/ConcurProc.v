Require Export Trace.
Require Import Helpers.Helpers.
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

  Variable opT : Type -> Type.
  Variable State : Type.

  Inductive proc : Type -> Type :=
  | Op : forall T (op : opT T), proc T
  | Ret : forall T (v : T), proc T
  | Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T
  | Until : forall T (c : T -> bool) (p : option T -> proc T) (v : option T), proc T
  | Atomic : forall T (p : proc T), proc T
  | Spawn : forall T (p: proc T), proc unit
  .


  Definition OpSemantics := forall T, opT T -> nat -> State -> T -> State -> list event -> Prop.
  Variable op_step : OpSemantics.


  Inductive maybe_proc :=
  | Proc : forall T, proc T -> maybe_proc
  | NoProc.

  Definition threads_state := Map.t {T & proc T}.
  Definition thread_get (ts:threads_state) (tid:nat) : maybe_proc :=
    match Map.get ts tid with
    | Some (existT _ _ p) => Proc p
    | None => NoProc
    end.
  Definition thread_upd (ts:threads_state) (tid:nat) (mp:maybe_proc) : threads_state :=
    match mp with
    | Proc p => Map.upd ts tid (Some (existT _ _ p))
    | NoProc => Map.upd ts tid None
    end.
  Coercion thread_get : threads_state >-> Funclass.

  Definition thread_Forall (P: forall T, proc T -> Prop) (ts:threads_state) :=
    Map.Forall (fun '(existT _ _ p) => P _ p) ts.

  Section ThreadState.

    Ltac t := unfold thread_get, thread_upd, thread_Forall;
              intros;
              repeat match goal with
                     | [ p: maybe_proc |- _ ] => destruct p
                     end;
              autorewrite with upd;
              auto.

    (* reproduce FinMap library *)
    Theorem thread_upd_eq : forall ts tid p,
        thread_upd ts tid p tid = p.
    Proof.
      t.
    Qed.

    Theorem thread_upd_ne : forall ts tid tid' p,
        tid <> tid' ->
        thread_upd ts tid p tid' = ts tid'.
    Proof.
      t.
    Qed.

    Theorem thread_upd_upd_eq : forall ts tid p p',
        thread_upd (thread_upd ts tid p) tid p' = thread_upd ts tid p'.
    Proof.
      t.
    Qed.

    Theorem thread_upd_ne_comm : forall ts tid tid' p p',
        tid <> tid' ->
        thread_upd (thread_upd ts tid p) tid' p' =
        thread_upd (thread_upd ts tid' p') tid p.
    Proof.
      t; apply Map.upd_ne_comm; auto.
    Qed.

    Theorem thread_upd_same_eq : forall (ts:threads_state) tid p,
        ts tid = p ->
        thread_upd ts tid p = ts.
    Proof.
      t; apply Map.upd_same_eq.
      destruct_with_eqn (Map.get ts tid); simpl in *; try congruence.
      destruct s; simpl in *.
      invert H; auto.

      destruct_with_eqn (Map.get ts tid); simpl in *; auto.
      destruct s; congruence.
    Qed.

    Definition threads_empty : threads_state := Map.empty _.

    Theorem threads_empty_get : forall tid,
        threads_empty tid = NoProc.
    Proof.
      t.
    Qed.

    Theorem thread_Forall_some : forall P (ts: threads_state) a T (p: proc T),
        thread_Forall P ts ->
        ts a = Proc p ->
        P _ p.
    Proof.
      t.
      destruct_with_eqn (Map.get ts a); try congruence.
      eapply Map.Forall_some in H; eauto.
      destruct s.
      invert H0.
    Qed.

    Theorem thread_Forall_upd_some : forall P ts tid T (v: proc T),
        thread_Forall P ts ->
        P _ v ->
        thread_Forall P (thread_upd ts tid (Proc v)).
    Proof.
      t; eauto using Map.Forall_upd_some.
    Qed.

    Theorem thread_Forall_upd_none : forall P ts tid,
        thread_Forall P ts ->
        thread_Forall P (thread_upd ts tid NoProc).
    Proof.
      t; eauto using Map.Forall_upd_none.
    Qed.

    Theorem Forall_forall : forall (P: forall T, proc T -> Prop) (ts: threads_state),
        (forall tid T (p: proc T), ts tid = Proc p -> P T p) ->
        thread_Forall P ts.
    Proof.
      t.
      eapply Map.Forall_forall; intros.
      destruct v.
      specialize (H a _ p); simpl_match; eauto.
    Qed.

    Theorem thread_Forall_forall : forall (P: forall T, proc T -> Prop)
                                     (ts: threads_state),
        (forall tid T (p: proc T), ts tid = Proc p -> P _ p) ->
        thread_Forall P ts.
    Proof.
      t.
      eapply Map.Forall_forall; intros.
      destruct v; eauto.
      eapply H.
      rewrite H0; eauto.
    Qed.

    Theorem thread_mapping_finite : forall (ts: threads_state) tid,
        tid > Map.max ts ->
        ts tid = NoProc.
    Proof.
      t.
      rewrite Map.mapping_finite by auto; auto.
    Qed.

    Theorem thread_ext_eq : forall (ts1 ts2: threads_state),
        (forall tid, ts1 tid = ts2 tid) ->
        ts1 = ts2.
    Proof.
      t.
      apply Map.t_ext_eq; intros.
      specialize (H a).
      destruct (Map.get ts1 a), (Map.get ts2 a);
        repeat match goal with
               | [ s: {_ & _} |- _ ] => destruct s
               end;
        try congruence.
      invert H; auto.
    Qed.

    Theorem thread_upd_max_bound : forall (ts:threads_state) tid p,
        tid <= Map.max ts ->
        Map.max (thread_upd ts tid p) <= Map.max ts.
    Proof.
      t.
      rewrite Map.upd_max_bound; auto.
      rewrite Map.upd_max_bound; auto.
    Qed.

    Theorem thread_upd_max_extend_bound : forall (ts:threads_state) tid p,
        tid >= Map.max ts ->
        Map.max (thread_upd ts tid p) <= tid.
    Proof.
      t.
      rewrite Map.upd_max_extend_bound; auto.
      rewrite Map.upd_max_extend_bound; auto.
    Qed.

    Theorem threads_empty_max :
      Map.max threads_empty = 0.
    Proof.
      t.
    Qed.

    Definition threads_from_list (l: list {T & proc T}) : threads_state :=
      Map.from_list l.

    Theorem threads_from_list_get : forall l tid,
        threads_from_list l tid = match List.nth_error l tid with
                                  | Some (existT _ _ p) => Proc p
                                  | None => NoProc
                                  end.
    Proof.
      t.
    Qed.

    Definition threads_to_list (ts: threads_state) : list maybe_proc :=
      List.map (fun mp => match mp with
                       | Some (existT _ _ p) => Proc p
                       | None => NoProc
                       end) (Map.to_list ts).

  End ThreadState.


  Definition until1 T (c : T -> bool)
                      (p : option T -> proc T)
                      (v : option T) :=
    Bind (p v) (fun x => if bool_dec (c x) true then Ret x else Until c p (Some x)).


  Inductive atomic_exec : forall T, proc T -> nat -> State ->
                                    T -> State -> list event -> Prop :=

  | AtomicRet : forall T tid (v : T) s,
    atomic_exec (Ret v) tid s v s nil

  | AtomicBind : forall T1 T2 tid (p1 : proc T1) (p2 : T1 -> proc T2)
                        s0 s1 s2 ev1 ev2 (v1 : T1) (v2 : T2),
    atomic_exec p1 tid s0 v1 s1 ev1 ->
    atomic_exec (p2 v1) tid s1 v2 s2 ev2 ->
    atomic_exec (Bind p1 p2) tid s0 v2 s2 (ev1 ++ ev2)

  | AtomicOp : forall T tid (v : T) s s' op evs,
    op_step op tid s v s' evs ->
    atomic_exec (Op op) tid s v s' evs

  | AtomicUntil : forall T (p : option T -> proc T) (c : T -> bool) v tid s r s' ev',
    atomic_exec (until1 c p v) tid s r s' ev' ->
    atomic_exec (Until c p v) tid s r s' ev'
  .


  Inductive exec_tid : forall T (tid : nat),
    State -> proc T ->
    State -> T + proc T -> maybe_proc -> list event -> Prop :=

  | ExecTidRet : forall tid T (v : T) s,
    exec_tid tid s (Ret v)
                 s (inl v)
                 NoProc nil

  | ExecTidOp : forall tid T (v : T) s s' op evs,
    op_step op tid s v s' evs ->
    exec_tid tid s (Op op)
                 s' (inl v)
                 NoProc evs

  | ExecTidAtomic : forall tid T (v : T) ap s s' evs,
    atomic_exec ap tid s v s' evs ->
    exec_tid tid s (Atomic ap)
                 s' (inl v)
                 NoProc evs

  | ExecTidBind : forall tid T1 (p1 : proc T1) T2 (p2 : T1 -> proc T2) s s' result spawned evs,
    exec_tid tid s p1
                 s' result spawned evs ->
    exec_tid tid s (Bind p1 p2)
                 s' (inr
                     match result with
                     | inl r => p2 r
                     | inr p1' => Bind p1' p2
                     end
                    ) spawned evs

  | ExecTidUntil : forall tid T (p : option T -> proc T) (c : T -> bool) v s,
    exec_tid tid s (Until c p v)
                 s (inr (until1 c p v))
                 NoProc nil

  | ExecTidSpawn : forall tid T (p: proc T) s,
    exec_tid tid s (Spawn p)
                 s (inl tt)
                 (Proc p) nil
  .


  Inductive exec : State -> threads_state -> trace -> nat -> Prop :=

  | ExecOne : forall T tid tid' (ts : threads_state) trace p s s' evs result ctr spawned,
    ts tid = @Proc T p ->
    ts tid' = NoProc ->
    exec_tid tid s p s' result spawned evs ->
    exec s' (thread_upd (thread_upd ts tid' spawned) tid
              match result with
              | inl _ => NoProc
              | inr p' => Proc p'
              end) trace ctr ->
    exec s ts (prepend tid evs trace) (S ctr)

  | ExecExpired : forall (ts : threads_state) s,
    exec s ts TraceEmpty 0.


  Definition exec_prefix (s : State) (ts : threads_state) (tr : trace) : Prop :=
    exists n,
      exec s ts tr n.

  Theorem ExecPrefixOne
       : forall (T : Type) 
           (tid : nat) (ts : threads_state) (tr : trace)
           (p : proc T) (s s' : State)
           (evs : list event) (result : T + proc T)
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
    forall T (p : proc T) (r : T) (s' : State), Prop :=
  | ExecAnyOther :
    forall T (p : proc T) (r : T) (s' : State)
           T' (op' : opT T') tid' s0 r0 evs,
    tid <> tid' ->
    op_step op' tid' s r0 s0 evs ->
    exec_any tid s0 p r s' ->
    exec_any tid s p r s'
  | ExecAnyThisDone :
    forall T (p : proc T) (r : T) (s' : State) spawned evs,
    exec_tid tid s p s' (inl r) spawned evs ->
    exec_any tid s p r s'
  | ExecAnyThisMore :
    forall T (p p' : proc T) (s' s0 : State) r spawned evs,
    exec_tid tid s p s0 (inr p') spawned evs ->
    exec_any tid s0 p' r s' ->
    exec_any tid s p r s'
  .

  Definition exec_others (tid : nat) (s s' : State) : Prop :=
    clos_refl_trans_1n _
      (fun s0 s1 =>
        exists tid' `(op' : opT T') r' evs,
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

  Lemma exec_others_one : forall tid s s' tid' T (op: opT T) r evs,
      tid <> tid' ->
      op_step op tid' s r s' evs ->
      exec_others tid s s'.
  Proof.
    unfold exec_others; intros.
    econstructor; [ | reflexivity ].
    eauto 10.
  Qed.

  Lemma exec_any_op : forall `(op : opT T) tid r s s',
    exec_any tid s (Op op) r s' ->
      exists s0 evs,
        exec_others tid s s0 /\
        op_step op tid s0 r s' evs.
  Proof.
    intros.
    remember (Op op).
    induct H;
      repeat match goal with
             | [ H: forall _, Op _ = Op _ -> _ |- _ ] =>
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
    forall tid tid' `(p : proc T) s s' result spawned evs,
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
    forall tid s s' s'' `(p : proc T) v,
      exec_others tid s s' ->
      exec_any tid s' p v s'' ->
      exec_any tid s p v s''.
  Proof.
    induction 1; propositional; eauto using ExecAnyOther.
  Qed.

End Proc.

Arguments Op {opT T}.
Arguments Ret {opT T}.
Arguments Bind {opT T T1}.
Arguments Until {opT T}.
Arguments Atomic {opT T}.

Arguments Proc {opT T}.
Arguments NoProc {opT}.

Arguments threads_state {opT}.

Hint Constructors exec.
Hint Constructors exec_any.
Hint Resolve exec_to_exec_prefix.
Hint Resolve exec_tid_exec_others.
Hint Resolve exec_others_exec_any.
Hint Resolve exec_others_trans.


Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 60, right associativity).

Notation "ts [[ tid ]]" := (thread_get ts tid)
  (at level 8, left associativity).

Notation "ts [[ tid := p ]]" := (thread_upd ts tid p)
  (at level 8, left associativity).


Section StepImpl.

  Hint Constructors exec_tid.
  Hint Constructors atomic_exec.

  Variable opT : Type -> Type.
  Variable State : Type.
  Variable op_step1 : OpSemantics opT State.
  Variable op_step2 : OpSemantics opT State.

  Variable StepImpl :
    forall `(op : opT TT) tid s r s' evs,
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


Lemma thread_empty_inv : forall opT tid `(p' : proc _ T),
  (@threads_empty opT) [[ tid ]] = Proc p' ->
  False.
Proof.
  intros.
  rewrite threads_empty_get in H; congruence.
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

Definition thread_map opT1 opT2
           (f: forall T, proc opT1 T -> proc opT2 T)
           (ts:@threads_state opT1) : @threads_state opT2 :=
  Map.map (fun '(existT _ _ p) => existT _ _ (f _ p)) ts.

Theorem thread_map_get : forall `(f: forall T, proc opT1 T -> proc opT2 T) ts tid,
    thread_map f ts tid = match ts tid with
                          | Proc p => Proc (f _ p)
                          | NoProc => NoProc
                          end.
Proof.
  unfold thread_map, thread_get; simpl; intros.
  destruct_with_eqn (Map.get ts tid); autorewrite with upd; auto.
  destruct s; autorewrite with upd; eauto.
  rewrite Map.map_get_match; simpl_match; auto.
Qed.

Theorem thread_map_Forall : forall `(f: forall T, proc opT1 T -> proc opT2 T)
                              (P: forall T, proc opT1 T -> Prop)
                              (Q: forall T, proc opT2 T -> Prop)
                              ts,
    thread_Forall P ts ->
    (forall T (p: proc opT1 T), P _ p -> Q _ (f _ p)) ->
    thread_Forall Q (thread_map f ts).
Proof.
  unfold thread_map, thread_Forall; intros.
  eapply Map.map_Forall; eauto; intros.
  destruct v; eauto.
Qed.

Theorem thread_max_eq : forall opT1 opT2
                          (ts1: @threads_state opT1) (ts2: @threads_state opT2),
    (forall tid, ts1 tid = NoProc <-> ts2 tid = NoProc) ->
    Map.max ts1 = Map.max ts2.
Proof.
  unfold thread_get; intros.
  apply Map.max_eq; intros.
  specialize (H a); destruct H.
  destruct (Map.get ts1 a), (Map.get ts2 a);
    repeat match goal with
           | [ s: {_ & _} |- _ ] => destruct s
           end;
    (intuition auto);
    congruence.
Qed.

Arguments threads_empty {opT}.
Global Opaque thread_get thread_upd threads_empty.
(* reproduce upd database from FinMap *)
Hint Rewrite thread_upd_eq : t.
Hint Rewrite thread_upd_ne using congruence : t.
Hint Rewrite thread_upd_upd_eq : t.
Hint Rewrite thread_upd_same_eq using congruence : t.
Hint Rewrite thread_mapping_finite using congruence : t.
Hint Rewrite threads_empty_max : t.

(* compare thread ids and perform cleanup *)
Ltac cmp_ts tid1 tid2 :=
  destruct (tid1 == tid2); subst;
  try congruence;
  autorewrite with t in *.

(* abstract the thread state in an exec goal (to deal with different update
forms) *)
Ltac abstract_ts :=
  match goal with
    |- exec_prefix _ _ ?ts _ => abstract_term ts
  end.

(* abstract the trace in an exec goal (to deal with different calls to
prepend/list append) *)
Ltac abstract_tr :=
  match goal with
  | |- exec_prefix _ _ _ ?tr => abstract_term tr
  end.
