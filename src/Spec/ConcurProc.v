Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import List.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.



Section Event.

  Variable opT : Type -> Type.

  Inductive callret :=
  | EvCall : forall T (op : opT T), callret
  | EvRet : forall T (result : T), callret.

End Event.

Arguments EvCall {opT T}.
Arguments EvRet {opT T}.


Section Trace.

  Variable opT : Type -> Type.
  Variable opHiT : Type -> Type.

  Inductive event :=
  | EvLow : callret opT -> event
  | EvHigh : callret opHiT -> event.

  Inductive trace :=
  | TraceEvent : forall (tid : nat) (ev : event), trace -> trace
  | TraceEmpty : trace.


  Fixpoint prepend tid (evs : list event) (tr : trace) : trace :=
    match evs with
    | nil => tr
    | e :: evs' =>
      TraceEvent tid e (prepend tid evs' tr)
    end.

End Trace.

Arguments EvLow {opT opHiT}.
Arguments EvHigh {opT opHiT}.
Arguments TraceEvent {opT opHiT}.
Arguments TraceEmpty {opT opHiT}.


Section Proc.

  Variable opT : Type -> Type.
  Variable opHiT : Type -> Type.
  Variable State : Type.

  Inductive proc : Type -> Type :=
  | OpCall : forall T (op : opT T), proc unit
  | OpExec : forall T (op : opT T), proc T
  | OpRet : forall T (v : T), proc T
  | Ret : forall T (v : T), proc T
  | Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T
  | OpCallHi : forall T' (op : opHiT T'), proc unit
  | OpRetHi : forall T (result : T), proc T
  | Atomic : forall T (p : proc T), proc T.


  Definition OpSemantics := forall T, opT T -> nat -> State -> T -> State -> Prop.
  Variable op_step : OpSemantics.


  Inductive maybe_proc :=
  | Proc : forall T, proc T -> maybe_proc
  | NoProc.

  Definition threads_state := list maybe_proc.

  Definition thread_get (ts : threads_state) (tid : nat) :=
    match nth_error ts tid with
    | Some x => x
    | None => NoProc
    end.

  Definition thread_upd (ts : threads_state) (tid : nat) (s : maybe_proc) : threads_state :=
    list_upd (pad ts (S tid) NoProc) tid s.

  Definition no_runnable_threads (ts : threads_state) :=
    forall tid, thread_get ts tid = NoProc.


  Inductive atomic_exec : forall T, proc T -> nat -> State ->
                                    T -> State -> list (event opT opHiT) -> Prop :=

  | AtomicRet : forall T tid (v : T) s,
    atomic_exec (Ret v) tid s v s nil

  | AtomicBind : forall T1 T2 tid (p1 : proc T1) (p2 : T1 -> proc T2)
                        s0 s1 s2 ev1 ev2 (v1 : T1) (v2 : T2),
    atomic_exec p1 tid s0 v1 s1 ev1 ->
    atomic_exec (p2 v1) tid s1 v2 s2 ev2 ->
    atomic_exec (Bind p1 p2) tid s0 v2 s2 (ev1 ++ ev2)

  | AtomicOpCall : forall T tid s (op : opT T),
    atomic_exec (OpCall op) tid s tt s
      [EvLow (EvCall op)]

  | AtomicOpExec : forall T tid (v : T) s s' op,
    op_step op tid s v s' ->
    atomic_exec (OpExec op) tid s v s' nil

  | AtomicOpRet : forall T tid (v : T) s,
    atomic_exec (OpRet v) tid s v s
      [EvLow (EvRet v)]

  | AtomicInvokeHi : forall T (op : opHiT T) tid s,
    atomic_exec (OpCallHi op) tid s tt s
      [EvHigh (EvCall op)]

  | AtomicReturnHi : forall T (r : T) tid s,
    atomic_exec (OpRetHi r) tid s r s
      [EvHigh (EvRet r)]

  | AtomicAtomic : forall T (p : proc T) tid s r s' ev',
    atomic_exec p tid s r s' ev' ->
    atomic_exec (Atomic p) tid s r s' ev'.


  Inductive exec_tid : forall T (tid : nat),
    State -> proc T ->
    State -> T + proc T -> list (event opT opHiT) -> Prop :=

  | ExecTidRet : forall tid T (v : T) s,
    exec_tid tid s (Ret v)
                 s (inl v)
                 nil

  | ExecTidOpCall : forall tid T s (op : opT T),
    exec_tid tid s (OpCall op)
                 s (inl tt)
                 [EvLow (EvCall op)]

  | ExecTidOpRun : forall tid T (v : T) s s' op,
    op_step op tid s v s' ->
    exec_tid tid s (OpExec op)
                 s' (inl v)
                 nil

  | ExecTidOpRet : forall tid T (v : T) s,
    exec_tid tid s (OpRet v)
                 s (inl v)
                 [EvLow (EvRet v)]

  | ExecTidAtomic : forall tid T (v : T) ap s s' evs,
    atomic_exec ap tid s v s' evs ->
    exec_tid tid s (Atomic ap)
                 s' (inl v)
                 evs

  | ExecTidInvokeHi : forall tid s T' (op : opHiT T'),
    exec_tid tid s (OpCallHi op)
                 s (inl tt)
                 [EvHigh (EvCall op)]

  | ExecTidReturnHi : forall tid s T' (r : T'),
    exec_tid tid s (OpRetHi r)
                 s (inl r)
                 [EvHigh (EvRet r)]

  | ExecTidBind : forall tid T1 (p1 : proc T1) T2 (p2 : T1 -> proc T2) s s' result evs,
    exec_tid tid s p1
                 s' result evs ->
    exec_tid tid s (Bind p1 p2)
                 s' (inr
                     match result with
                     | inl r => p2 r
                     | inr p1' => Bind p1' p2
                     end
                    ) evs.


  Inductive exec : State -> threads_state -> trace opT opHiT -> Prop :=

  | ExecOne : forall T tid (ts : threads_state) trace p s s' evs result,
    thread_get ts tid = @Proc T p ->
    exec_tid tid s p s' result evs ->
    exec s' (thread_upd ts tid
              match result with
              | inl _ => NoProc
              | inr p' => Proc p'
              end) trace ->
    exec s ts (prepend tid evs trace)

  | ExecEmpty : forall (ts : threads_state) s,
    no_runnable_threads ts ->
    exec s ts TraceEmpty.

End Proc.

Arguments OpCall {opT opHiT T}.
Arguments OpExec {opT opHiT T}.
Arguments OpRet {opT opHiT T}.
Arguments Ret {opT opHiT T}.
Arguments Bind {opT opHiT T T1}.
Arguments OpCallHi {opT opHiT T'}.
Arguments OpRetHi {opT opHiT T}.
Arguments Atomic {opT opHiT T}.

Arguments Proc {opT opHiT T}.
Arguments NoProc {opT opHiT}.

Arguments threads_state {opT opHiT}.


Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 60, right associativity).

Notation "ts [[ tid ]]" := (thread_get ts tid)
  (at level 8, left associativity).

Notation "ts [[ tid := p ]]" := (thread_upd ts tid p)
  (at level 8, left associativity).


Definition Op {opT opHiT T} (op : opT T) : proc opT opHiT T :=
  _ <- OpCall op;
  r <- OpExec op;
  OpRet r.


Definition threads_empty {opT opHiT} : @threads_state opT opHiT := nil.


Lemma nth_error_nil : forall T x,
  nth_error (@nil T) x = None.
Proof.
  induction x; simpl; eauto.
Qed.

Lemma pad_eq : forall n `(ts : @threads_state opT opHiT) tid,
  ts [[ tid ]] = (pad ts n NoProc) [[ tid ]].
Proof.
  unfold thread_get.
  induction n; simpl; eauto.
  destruct ts.
  - destruct tid; simpl; eauto.
    rewrite <- IHn. rewrite nth_error_nil. auto.
  - destruct tid; simpl; eauto.
Qed.

Lemma pad_length_noshrink : forall n `(l : list T) v,
  length l <= length (pad l n v).
Proof.
  intros.
  generalize dependent l.
  induction n; simpl; eauto.
  destruct l; simpl; eauto.
  - specialize (IHn []). omega.
  - specialize (IHn l). omega.
Qed.

Lemma pad_length_grow : forall n `(l : list T) v,
  n <= length (pad l n v).
Proof.
  intros.
  generalize dependent l.
  induction n; simpl; intros; try omega.
  destruct l; simpl; eauto.
  - specialize (IHn []). omega.
  - specialize (IHn l). omega.
Qed.

Lemma pad_length_noshrink' : forall x n `(l : list T) v,
  x <= length l ->
  x <= length (pad l n v).
Proof.
  intros.
  pose proof (pad_length_noshrink n l v).
  omega.
Qed.

Lemma pad_noop : forall n T (l : list T) v,
  n <= length l ->
  pad l n v = l.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl in *.
  omega.
  rewrite IHn; eauto.
  omega.
Qed.

Lemma thread_get_Some_length : forall tid `(ts : @threads_state opT opHiT) `(p : proc _ _ T),
  ts [[ tid ]] = Proc p ->
  tid < length ts.
Proof.
  unfold thread_get.
  induction tid; simpl; intros.
  - destruct ts; try congruence. simpl. omega.
  - destruct ts; try congruence. simpl.
    specialize (IHtid _ _ _ _ _ H).
    omega.
Qed.

Lemma length_hint_lt_le : forall n m,
  S n <= m ->
  n < m.
Proof.
  intros; omega.
Qed.

Hint Resolve pad_length_noshrink.
Hint Resolve pad_length_grow.
Hint Resolve length_hint_lt_le.
Hint Resolve pad_length_noshrink'.
Hint Resolve thread_get_Some_length.
Hint Resolve lt_le_S.


Lemma prepend_app : forall `(evs1 : list (event opT opHiT)) evs2 tr tid,
  prepend tid (evs1 ++ evs2) tr = prepend tid evs1 (prepend tid evs2 tr).
Proof.
  induction evs1; simpl; intros; eauto.
  rewrite IHevs1; eauto.
Qed.

Lemma list_upd_eq : forall tid `(ts : @threads_state opT opHiT) p,
  tid < length ts ->
  (list_upd ts tid p) [[ tid ]] = p.
Proof.
  unfold thread_get.
  induction tid; simpl; intros; eauto.
  - destruct ts; simpl in *; eauto. omega.
  - destruct ts; simpl in *. omega.
    eapply IHtid. omega.
Qed.

Lemma list_upd_ne : forall tid' tid `(ts : @threads_state opT opHiT) p,
  tid < length ts ->
  tid' <> tid ->
  (list_upd ts tid p) [[ tid' ]] = ts [[ tid' ]].
Proof.
  unfold thread_get.
  induction tid'; simpl; intros; eauto.
  - destruct tid; try congruence.
    destruct ts; simpl in *. congruence.
    auto.
  - destruct ts; simpl in *. congruence.
    destruct tid; auto.
    eapply IHtid'. omega. omega.
Qed.

Lemma list_upd_noop : forall tid `(ts : @threads_state opT opHiT) `(p : proc _ _ T),
  ts [[ tid ]] = Proc p ->
  list_upd ts tid (Proc p) = ts.
Proof.
  unfold thread_get.
  induction tid; simpl; intros.
  - destruct ts; try congruence. simpl. congruence.
  - destruct ts; try congruence. simpl. f_equal. eauto.
Qed.

Lemma list_upd_noop_NoProc : forall tid `(ts : @threads_state opT opHiT),
  ts [[ tid ]] = NoProc ->
  tid < length ts ->
  list_upd ts tid NoProc = ts.
Proof.
  unfold thread_get.
  induction tid; simpl; intros.
  - destruct ts; try congruence. simpl. congruence.
    simpl. subst. congruence.
  - destruct ts; try congruence. simpl. congruence.
    simpl. f_equal. eapply IHtid. 2: simpl in *; omega.
    eauto.
Qed.

Lemma thread_upd_same : forall tid `(ts : @threads_state opT opHiT) `(p : proc _ _ T),
  ts [[ tid ]] = Proc p ->
  ts [[ tid := Proc p ]] = ts.
Proof.
  unfold thread_upd; intros.
  rewrite pad_noop by eauto.
  rewrite list_upd_noop; eauto.
Qed.

Lemma thread_upd_same' : forall tid `(ts : @threads_state opT opHiT),
  tid < length ts ->
  ts [[ tid ]] = NoProc ->
  ts [[ tid := NoProc ]] = ts.
Proof.
  unfold thread_upd; intros.
  rewrite pad_noop by eauto.
  rewrite list_upd_noop_NoProc; eauto.
Qed.

Lemma thread_upd_eq : forall tid `(ts : @threads_state opT opHiT) p,
  ts [[ tid := p ]] [[ tid ]] = p.
Proof.
  unfold thread_upd; intros.
  apply list_upd_eq.
  pose proof (pad_length_grow (S tid) ts NoProc).
  omega.
Qed.

Lemma thread_get_pad : forall tid `(ts : @threads_state opT opHiT) n,
  (pad ts n NoProc) [[ tid ]] = ts [[ tid ]].
Proof.
  unfold thread_get.
  induction tid; simpl.
  - destruct ts; simpl.
    destruct n; simpl; eauto.
    destruct n; simpl; eauto.
  - destruct ts; simpl; eauto.
    + destruct n; simpl; eauto. rewrite IHtid. rewrite nth_error_nil. auto.
    + destruct n; simpl; eauto.
Qed.

Lemma thread_upd_ne : forall tid `(ts : @threads_state opT opHiT) p tid',
  tid <> tid' ->
  ts [[ tid := p ]] [[ tid' ]] = ts [[ tid' ]].
Proof.
  unfold thread_upd.
  intros.
  rewrite list_upd_ne; auto.
  rewrite thread_get_pad. eauto.
Qed.

Lemma list_upd_pad : forall `(ts : @threads_state opT opHiT) tid n p,
  tid < length ts ->
  pad (list_upd ts tid p) n NoProc = list_upd (pad ts n NoProc) tid p.
Proof.
  induction ts; simpl; intros.
  - omega.
  - destruct tid; simpl.
    + destruct n; simpl; eauto.
    + destruct n; simpl; eauto.
      f_equal.
      eapply IHts.
      omega.
Qed.

Lemma list_upd_comm : forall `(ts : @threads_state opT opHiT) tid1 p1 tid2 p2,
  tid1 < length ts ->
  tid2 < length ts ->
  tid1 <> tid2 ->
  list_upd (list_upd ts tid1 p1) tid2 p2 = list_upd (list_upd ts tid2 p2) tid1 p1.
Proof.
  induction ts; simpl; intros; eauto.
  - destruct tid1; destruct tid2; try omega; simpl; eauto.
    f_equal. apply IHts; omega.
Qed.

Lemma list_upd_upd_eq : forall `(ts : @threads_state opT opHiT) tid p1 p2,
  tid < length ts ->
  list_upd (list_upd ts tid p1) tid p2 = list_upd ts tid p2.
Proof.
  induction ts; simpl; eauto; intros.
  destruct tid; simpl; eauto.
  f_equal.
  eapply IHts.
  omega.
Qed.

Lemma pad_comm : forall T n m (l : list T) v,
  pad (pad l n v) m v = pad (pad l m v) n v.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl; eauto.
  - destruct m; simpl; eauto. rewrite IHn. eauto.
  - destruct m; simpl; eauto. rewrite IHn; eauto.
Qed.

Lemma pad_idem : forall T n (l : list T) v,
  pad (pad l n v) n v = pad l n v.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl; eauto.
  - rewrite IHn. eauto.
  - rewrite IHn. eauto.
Qed.

Lemma thread_upd_upd_ne : forall tid tid' `(ts : @threads_state opT opHiT) p p',
  tid <> tid' ->
  ts [[ tid := p ]] [[ tid' := p' ]] =
  ts [[ tid' := p' ]] [[ tid := p ]].
Proof.
  unfold thread_upd.
  intros.
  repeat rewrite list_upd_pad by eauto.
  rewrite list_upd_comm by eauto.
  f_equal.
  f_equal.
  apply pad_comm.
Qed.

Lemma thread_upd_upd_eq : forall tid `(ts : @threads_state opT opHiT) p1 p2,
  ts [[ tid := p1 ]] [[ tid := p2 ]] =
  ts [[ tid := p2 ]].
Proof.
  unfold thread_upd; intros.
  rewrite list_upd_pad by eauto.
  rewrite pad_idem.
  rewrite list_upd_upd_eq by eauto.
  reflexivity.
Qed.

Lemma thread_upd_inv : forall `(ts : @threads_state opT opHiT) tid1 `(p : proc _ _ T) tid2 `(p' : proc _ _ T'),
  ts [[ tid1 := Proc p ]] [[ tid2 ]] = Proc p' ->
  tid1 = tid2 /\ Proc p = Proc p' \/
  tid1 <> tid2 /\ ts [[ tid2 ]] = Proc p'.
Proof.
  intros.
  destruct (tid1 == tid2).
  - left; intuition eauto; subst.
    rewrite thread_upd_eq in H. congruence.
  - right; intuition eauto.
    rewrite thread_upd_ne in H; eauto.
Qed.

Lemma thread_empty_inv : forall opT opHiT tid `(p' : proc _ _ T),
  (@threads_empty opT opHiT) [[ tid ]] = Proc p' ->
  False.
Proof.
  unfold threads_empty; intros.
  destruct tid; compute in H; congruence.
Qed.

Lemma thread_get_S : forall `(ts : @threads_state opT opHiT) tid a,
  (a :: ts) [[ S tid ]] = ts [[ tid ]].
Proof.
  reflexivity.
Qed.

Lemma thread_get_0 : forall `(ts : @threads_state opT opHiT) a,
  (a :: ts) [[ 0 ]] = a.
Proof.
  reflexivity.
Qed.

Lemma thread_upd_S : forall `(ts : @threads_state opT opHiT) tid a p,
  (a :: ts) [[ S tid := p ]] = a :: (ts [[ tid := p ]]).
Proof.
  reflexivity.
Qed.

Lemma thread_upd_0 : forall `(ts : @threads_state opT opHiT) a p,
  (a :: ts) [[ 0 := p ]] = p :: ts.
Proof.
  reflexivity.
Qed.

Lemma thread_get_nil : forall opT opHiT tid,
  @thread_get opT opHiT nil tid = NoProc.
Proof.
  unfold thread_get; intros.
  rewrite nth_error_nil.
  reflexivity.
Qed.

Lemma thread_upd_nil_S : forall opT opHiT tid p,
  @thread_upd opT opHiT nil (S tid) p = NoProc :: (nil [[ tid := p ]]).
Proof.
  reflexivity.
Qed.

Lemma length_thread_upd : forall tid `(ts : @threads_state opT opHiT) p,
  length (ts [[ tid := p ]]) = Nat.max (S tid) (length ts).
Proof.
  induction tid; simpl; intros.
  - destruct ts; cbn; eauto.
  - destruct ts.
    + rewrite thread_upd_nil_S.
      simpl length. rewrite IHtid.
      simpl. omega.
    + rewrite thread_upd_S.
      simpl length. rewrite IHtid.
      simpl. omega.
Qed.

Lemma thread_get_repeat_NoProc : forall opT opHiT n tid,
  (repeat (@NoProc opT opHiT) n) [[ tid ]] = NoProc.
Proof.
  induction n; simpl; intros.
  - rewrite thread_get_nil. eauto.
  - destruct tid.
    + rewrite thread_get_0. eauto.
    + rewrite thread_get_S. eauto.
Qed.

Lemma thread_upd_same'' : forall tid `(ts : @threads_state opT opHiT),
  tid >= length ts ->
  ts [[ tid := NoProc ]] = pad ts (S tid) NoProc.
Proof.
  unfold thread_upd; intros.
  rewrite list_upd_noop_NoProc; eauto.
  rewrite pad_is_append.

  generalize dependent tid.
  induction ts; intros.
  - rewrite app_nil_l.
    rewrite thread_get_repeat_NoProc. eauto.
  - destruct tid.
    + simpl in *. omega.
    + simpl app. rewrite thread_get_S. eapply IHts. simpl in *. omega.
Qed.

Lemma thread_get_oob : forall tid `(ts : @threads_state opT opHiT),
  tid >= length ts ->
  ts [[ tid ]] = NoProc.
Proof.
  induction tid; simpl; intros.
  - destruct ts; simpl in *; eauto.
    omega.
  - destruct ts.
    rewrite thread_get_nil; eauto.
    rewrite thread_get_S. eapply IHtid.
    simpl in *; omega.
Qed.

Theorem threads_empty_no_runnable : forall opT opHiT,
  no_runnable_threads (@threads_empty opT opHiT).
Proof.
  unfold no_runnable_threads, threads_empty, thread_get.
  intros.
  rewrite nth_error_nil.
  auto.
Qed.

Lemma no_runnable_threads_pad : forall n `(ts : @threads_state opT opHiT),
  no_runnable_threads ts ->
  no_runnable_threads (pad ts n NoProc).
Proof.
  unfold no_runnable_threads, thread_get.
  induction n; simpl; eauto; intros.
  destruct ts; simpl.
  - destruct tid; simpl; eauto.
  - destruct tid; simpl; eauto.
    destruct m; eauto.
    specialize (H 0); compute in H; congruence.
    eapply IHn; intros.
    specialize (H (S tid0)).
    eapply H.
Qed.

Lemma no_runnable_threads_list_upd : forall `(ts : @threads_state opT opHiT) tid,
  no_runnable_threads ts ->
  no_runnable_threads (list_upd ts tid NoProc).
Proof.
  unfold no_runnable_threads, thread_get.
  induction ts; simpl; eauto; intros.
  destruct tid; simpl; eauto.
  - destruct tid0; simpl; eauto. specialize (H (S tid0)). apply H.
  - destruct tid0; simpl; eauto. specialize (H 0); simpl in H. eauto.
    eapply IHts; intros. specialize (H (S tid1)). apply H.
Qed.

Lemma no_runnable_threads_upd_NoProc : forall tid `(ts : @threads_state opT opHiT),
  no_runnable_threads ts ->
  no_runnable_threads (ts [[ tid := NoProc ]]).
Proof.
  unfold thread_upd; intros.
  eapply no_runnable_threads_list_upd.
  eapply no_runnable_threads_pad.
  eauto.
Qed.

Lemma thread_upd_not_empty : forall tid `(ts : @threads_state opT opHiT) `(p : proc _ _ T),
  no_runnable_threads (ts [[ tid := Proc p ]]) ->
  False.
Proof.
  unfold no_runnable_threads; intros.
  specialize (H tid).
  rewrite thread_upd_eq in H.
  congruence.
Qed.

Lemma no_runnable_threads_some :
  forall `(ts : @threads_state opT opHiT) tid `(p : proc _ _ T),
  ts [[ tid ]] = Proc p ->
  no_runnable_threads ts ->
  False.
Proof.
  unfold no_runnable_threads; intros.
  specialize (H0 tid). congruence.
Qed.

Lemma no_runnable_threads_nil : forall opT opHiT,
  @no_runnable_threads opT opHiT nil.
Proof.
  apply threads_empty_no_runnable.
Qed.

Lemma no_runnable_threads_cons : forall `(ts : @threads_state opT opHiT),
  no_runnable_threads ts ->
  no_runnable_threads (NoProc :: ts).
Proof.
  intros.
  unfold no_runnable_threads; intros.
  destruct tid.
  - rewrite thread_get_0; auto.
  - rewrite thread_get_S; auto.
Qed.

Lemma no_runnable_threads_cons' : forall `(ts : @threads_state opT opHiT),
  no_runnable_threads (NoProc :: ts) ->
  no_runnable_threads ts.
Proof.
  intros.
  unfold no_runnable_threads; intros.
  specialize (H (S tid)).
  rewrite thread_get_S in H; auto.
Qed.

Hint Resolve no_runnable_threads_upd_NoProc.
Hint Resolve threads_empty_no_runnable.
Hint Resolve no_runnable_threads_nil.
Hint Resolve no_runnable_threads_cons.
Hint Resolve no_runnable_threads_some.
Hint Resolve thread_upd_not_empty.

Hint Rewrite thread_upd_upd_eq : t.
Hint Rewrite thread_upd_eq : t.
Hint Rewrite thread_upd_ne using (solve [ auto ]) : t.

Hint Extern 1 (exec_tid _ _ _ _ _ _ _) => econstructor.
Hint Extern 1 (atomic_exec _ _ _ _ _ _ _) => econstructor.


Lemma thread_get_app_NoProc : forall `(ts : @threads_state opT opHiT) tid `(p : proc _ _ T),
  ts [[ tid ]] = Proc p <->
  (ts ++ [NoProc]) [[ tid ]] = Proc p.
Proof.
  split; intros.
  - generalize dependent tid.
    induction ts; simpl; intros.
    + exfalso. eapply no_runnable_threads_some; eauto.
    + destruct tid; cbn in *; eauto.
  - generalize dependent tid.
    induction ts; simpl; intros.
    + destruct tid; cbn in *.
      congruence.
      rewrite thread_get_S in H.
      exfalso. eapply no_runnable_threads_some; eauto.
    + destruct tid; cbn in *; eauto.
Qed.

Lemma thread_upd_app_NoProc : forall `(ts : @threads_state opT opHiT) tid p,
  tid < length ts ->
  ts [[ tid := p ]] ++ [NoProc] = (ts ++ [NoProc]) [[ tid := p ]].
Proof.
  induction ts; simpl; intros; try omega.
  destruct tid.
  - repeat rewrite thread_upd_0.
    reflexivity.
  - repeat rewrite thread_upd_S.
    simpl; f_equal.
    rewrite IHts; auto.
    omega.
Qed.

Lemma no_runnable_threads_app_NoProc : forall `(ts : @threads_state opT opHiT),
  no_runnable_threads ts <->
  no_runnable_threads (ts ++ [NoProc]).
Proof.
  split; intros; unfold no_runnable_threads; intros.
  - generalize dependent tid.
    induction ts.
    + rewrite app_nil_l.
      destruct tid. rewrite thread_get_0; eauto. rewrite thread_get_S.
      rewrite thread_get_nil; auto.
    + destruct tid; simpl.
      * specialize (H 0).
        rewrite thread_get_0.
        rewrite thread_get_0 in H.
        auto.
      * rewrite thread_get_S.
        eapply IHts.
        unfold no_runnable_threads; intros.
        specialize (H (S tid0)). rewrite thread_get_S in H. auto.
  - generalize dependent tid.
    induction ts.
    + intros. apply thread_get_nil.
    + destruct tid; simpl in *.
      * specialize (H 0).
        rewrite thread_get_0.
        rewrite thread_get_0 in H.
        auto.
      * rewrite thread_get_S. apply IHts.
        intros tid'.
        specialize (H (S tid')). rewrite thread_get_S in H. auto.
Qed.


Ltac maybe_proc_inv := match goal with
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
  | H : exec_tid _ _ _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat maybe_proc_inv
  end;
  autorewrite with t in *.

Ltac atomic_exec_inv :=
  match goal with
  | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat maybe_proc_inv
  end;
  autorewrite with t in *.
