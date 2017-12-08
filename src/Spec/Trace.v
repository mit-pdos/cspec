Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import ClassicalFacts.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Helpers.Helpers.
Require Import List.

Import ListNotations.

Axiom EM : excluded_middle.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Proc.

Variable opT : Type -> Type.
Variable opHiT : Type -> Type.

Inductive proc : Type -> Type :=
| OpCall : forall T (op : opT T), proc unit
| OpExec : forall T (op : opT T), proc T
| OpRet : forall T (v : T), proc T
| Ret : forall T (v : T), proc T
| Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T
| InvokeOpHi : forall T' (op : opHiT T'), proc unit
| ReturnOpHi : forall T (result : T), proc T
| Atomic : forall T (p : proc T), proc T.


Variable State : Type.

Variable op_step : forall T, opT T -> nat -> State -> T -> State -> Prop.


Inductive event :=
| InvokeLo : forall (tid : nat) T (op : opT T), event
| ReturnLo : forall (tid : nat) T (result : T), event
| InvokeHi : forall (tid : nat) T (op : opHiT T), event
| ReturnHi : forall (tid : nat) T (result : T), event.

Inductive trace :=
| TraceEvent : event -> trace -> trace
| TraceEmpty : trace.


Definition threads_state := list (option {T : Type & proc T}).

Definition thread_get (ts : threads_state) (tid : nat) :=
  match nth_error ts tid with
  | Some x => x
  | None => None
  end.

Fixpoint pad T (l : list (option T)) len : list (option T) :=
  match len with
  | O => l
  | S len' =>
    match l with
    | x :: l' =>
      x :: pad l' len'
    | nil =>
      None :: pad nil len'
    end
  end.

Fixpoint list_upd T (l : list (option T)) (idx : nat) (v : option T) : list (option T) :=
  match l with
  | nil => nil
  | x :: l' =>
    match idx with
    | O => v :: l'
    | S idx' => x :: list_upd l' idx' v
    end
  end.

Definition thread_upd (ts : threads_state) (tid : nat) (s : option {T : Type & proc T}) : threads_state :=
  list_upd (pad ts (S tid)) tid s.

Definition thread_updS {T} (ts : threads_state) (tid : nat) (p : proc T) :=
  thread_upd ts tid (Some (existT _ _ p)).

Coercion thread_get : threads_state >-> Funclass.


Inductive atomic_exec : forall T, proc T -> nat -> State -> T -> State -> list event -> Prop :=

| AtomicRet : forall T tid (v : T) s,
  atomic_exec (Ret v) tid s v s nil

| AtomicBind : forall T1 T2 tid (p1 : proc T1) (p2 : T1 -> proc T2)
                      s0 s1 s2 ev1 ev2 (v1 : T1) (v2 : T2),
  atomic_exec p1 tid s0 v1 s1 ev1 ->
  atomic_exec (p2 v1) tid s1 v2 s2 ev2 ->
  atomic_exec (Bind p1 p2) tid s0 v2 s2 (ev1 ++ ev2)

| AtomicOpCall : forall T tid s (op : opT T),
  atomic_exec (OpCall op) tid s tt s
    (InvokeLo tid op :: nil)

| AtomicOpExec : forall T tid (v : T) s s' op,
  op_step op tid s v s' ->
  atomic_exec (OpExec op) tid s v s' nil

| AtomicOpRet : forall T tid (v : T) s,
  atomic_exec (OpRet v) tid s v s
    (ReturnLo tid v :: nil)

| AtomicInvokeHi : forall T (op : opHiT T) tid s,
  atomic_exec (InvokeOpHi op) tid s tt s (InvokeHi tid op :: nil)

| AtomicReturnHi : forall T (r : T) tid s,
  atomic_exec (ReturnOpHi r) tid s r s (ReturnHi tid r :: nil)

| AtomicAtomic : forall T (p : proc T) tid s r s' ev',
  atomic_exec p tid s r s' ev' ->
  atomic_exec (Atomic p) tid s r s' ev'.


Fixpoint prepend (evs : list event) (tr : trace) : trace :=
  match evs with
  | nil => tr
  | e :: evs' =>
    TraceEvent e (prepend evs' tr)
  end.


Inductive exec_tid : forall T (tid : nat),
  State -> proc T ->
  State -> T + proc T -> list event -> Prop :=

| ExecTidRet : forall tid T (v : T) s,
  exec_tid tid s (Ret v)
               s (inl v)
               nil

| ExecTidOpCall : forall tid T s (op : opT T),
  exec_tid tid s (OpCall op)
               s (inl tt)
               [InvokeLo tid op]

| ExecTidOpRun : forall tid T (v : T) s s' op,
  op_step op tid s v s' ->
  exec_tid tid s (OpExec op)
               s' (inl v)
               nil

| ExecTidOpRet : forall tid T (v : T) s,
  exec_tid tid s (OpRet v)
               s (inl v)
               [ReturnLo tid v]

| ExecTidAtomic : forall tid T (v : T) ap s s' evs,
  atomic_exec ap tid s v s' evs ->
  exec_tid tid s (Atomic ap)
               s' (inl v)
               evs

| ExecTidInvokeHi : forall tid s T' (op : opHiT T'),
  exec_tid tid s (InvokeOpHi op)
               s (inl tt)
               [InvokeHi tid op]

| ExecTidReturnHi : forall tid s T' (r : T'),
  exec_tid tid s (ReturnOpHi r)
               s (inl r)
               [ReturnHi tid r]

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


Definition no_runnable_threads (ts : threads_state) :=
  forall tid, ts tid = None.

Inductive exec : State -> threads_state -> trace -> Prop :=

| ExecOne : forall T tid (ts : threads_state) trace p s s' evs result,
  ts tid = Some (existT _ T p) ->
  exec_tid tid s p s' result evs ->
  exec s' (thread_upd ts tid
            match result with
            | inl _ => None
            | inr p' => Some (existT _ T p')
            end) trace ->
  exec s ts (prepend evs trace)

| ExecEmpty : forall (ts : threads_state) s,
  no_runnable_threads ts ->
  exec s ts TraceEmpty.

End Proc.


Arguments OpCall {opT opHiT T}.
Arguments OpExec {opT opHiT T}.
Arguments OpRet {opT opHiT T}.
Arguments Ret {opT opHiT T}.
Arguments Bind {opT opHiT T T1}.
Arguments InvokeOpHi {opT opHiT T'}.
Arguments ReturnOpHi {opT opHiT T}.
Arguments Atomic {opT opHiT T}.

Arguments threads_state {opT opHiT}.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

Definition Op {opT opHiT T} (op : opT T) : proc opT opHiT T :=
  _ <- OpCall op;
  r <- OpExec op;
  OpRet r.


Inductive opT : Type -> Type :=
| Inc : opT nat
| Noop : opT unit.

Inductive opHiT : Type -> Type :=
| IncTwice : opHiT nat
| Noop2 : opHiT unit.

Inductive opHi2T : Type -> Type :=
.

Definition State := forall (tid : nat), nat.

Inductive op_step : forall T, opT T -> nat -> State -> T -> State -> Prop :=
| StepInc : forall tid s,
  op_step Inc tid s (s tid + 1) (fun tid' => if tid' == tid then (s tid' + 1) else (s tid'))
| StepNoop : forall tid s,
  op_step Noop tid s tt s.

Inductive opHi_step : forall T, opHiT T -> nat -> State -> T -> State -> Prop :=
| StepIncTwice : forall tid s,
  opHi_step IncTwice tid s (s tid + 2) (fun tid' => if tid' == tid then (s tid' + 2) else (s tid'))
| StepNoop2 : forall tid s,
  opHi_step Noop2 tid s tt s.


Definition threads_empty {opT opHiT} : @threads_state opT opHiT := nil.

Definition inc_twice_impl :=
  _ <- InvokeOpHi IncTwice;
  _ <- Op Inc;
  i2 <- Op Inc;
  ReturnOpHi i2.

Definition p1 :=
  _ <- inc_twice_impl;
  Ret tt.

Definition ts := thread_upd threads_empty 1 (Some (existT _ _ p1)).


Lemma nth_error_nil : forall T x,
  nth_error (@nil T) x = None.
Proof.
  induction x; simpl; eauto.
Qed.

Lemma pad_eq : forall opT opHiT n (ts : @threads_state opT opHiT) tid,
  thread_get ts tid = thread_get (pad ts n) tid.
Proof.
  unfold thread_get.
  induction n; simpl; eauto.
  destruct ts0.
  - destruct tid; simpl; eauto.
    rewrite <- IHn. rewrite nth_error_nil. auto.
  - destruct tid; simpl; eauto.
Qed.

Lemma pad_length_noshrink : forall opT opHiT n (ts : @threads_state opT opHiT),
  length ts <= length (pad ts n).
Proof.
  induction n; simpl; eauto.
  destruct ts0; simpl; eauto.
  - specialize (IHn []). omega.
  - specialize (IHn ts0). omega.
Qed.

Lemma pad_length_grow : forall opT opHiT n (ts : @threads_state opT opHiT),
  n <= length (pad ts n).
Proof.
  induction n; simpl; intros; try omega.
  destruct ts0; simpl; eauto.
  - specialize (IHn []). omega.
  - specialize (IHn ts0). omega.
Qed.

Lemma pad_length_noshrink' : forall opT opHiT x n (ts : @threads_state opT opHiT),
  x <= length ts ->
  x <= length (pad ts n).
Proof.
  intros.
  pose proof (pad_length_noshrink n ts0).
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

Lemma list_upd_eq : forall opT opHiT tid (ts : @threads_state opT opHiT) p,
  tid < length ts ->
  thread_get (list_upd ts tid p) tid = p.
Proof.
  unfold thread_get.
  induction tid; simpl; intros; eauto.
  - destruct ts0; simpl in *; eauto. omega.
  - destruct ts0; simpl in *. omega.
    eapply IHtid. omega.
Qed.

Lemma list_upd_ne : forall opT opHiT tid' tid (ts : @threads_state opT opHiT) p,
  tid < length ts ->
  tid' <> tid ->
  thread_get (list_upd ts tid p) tid' = thread_get ts tid'.
Proof.
  unfold thread_get.
  induction tid'; simpl; intros; eauto.
  - destruct tid; try congruence.
    destruct ts0; simpl in *. congruence.
    auto.
  - destruct ts0; simpl in *. congruence.
    destruct tid; auto.
    eapply IHtid'. omega. omega.
Qed.

Lemma thread_upd_eq : forall opT opHiT tid ts p,
  @thread_upd opT opHiT ts tid p tid = p.
Proof.
  unfold thread_upd; intros.
  apply list_upd_eq.
  pose proof (pad_length_grow (S tid) ts0).
  omega.
Qed.

Lemma thread_get_pad : forall opT opHiT tid (ts : @threads_state opT opHiT) n,
  thread_get (pad ts n) tid = thread_get ts tid.
Proof.
  unfold thread_get.
  induction tid; simpl.
  - destruct ts0; simpl.
    destruct n; simpl; eauto.
    destruct n; simpl; eauto.
  - destruct ts0; simpl; eauto.
    + destruct n; simpl; eauto. rewrite IHtid. rewrite nth_error_nil. auto.
    + destruct n; simpl; eauto.
Qed.

Lemma thread_upd_ne : forall opT opHiT tid ts p tid',
  tid <> tid' ->
  @thread_upd opT opHiT ts tid p tid' = ts tid'.
Proof.
  unfold thread_upd.
  intros.
  rewrite list_upd_ne; auto.
  rewrite thread_get_pad. eauto.
Qed.

Lemma list_upd_pad : forall opT opHiT (ts : @threads_state opT opHiT) tid n p,
  tid < length ts ->
  pad (list_upd ts tid p) n = list_upd (pad ts n) tid p.
Proof.
  induction ts0; simpl; intros.
  - omega.
  - destruct tid; simpl.
    + destruct n; simpl; eauto.
    + destruct n; simpl; eauto.
      f_equal.
      eapply IHts0.
      omega.
Qed.

Lemma list_upd_comm : forall opT opHiT (ts : @threads_state opT opHiT) tid1 p1 tid2 p2,
  tid1 < length ts ->
  tid2 < length ts ->
  tid1 <> tid2 ->
  list_upd (list_upd ts tid1 p1) tid2 p2 = list_upd (list_upd ts tid2 p2) tid1 p1.
Proof.
  induction ts0; simpl; intros; eauto.
  - destruct tid1; destruct tid2; try omega; simpl; eauto.
    f_equal. apply IHts0; omega.
Qed.

Lemma list_upd_upd_eq : forall opT opHiT (ts : @threads_state opT opHiT) tid p1 p2,
  tid < length ts ->
  list_upd (list_upd ts tid p1) tid p2 = list_upd ts tid p2.
Proof.
  induction ts0; simpl; eauto; intros.
  destruct tid; simpl; eauto.
  f_equal.
  eapply IHts0.
  omega.
Qed.

Lemma pad_comm : forall T n m (l : list (option T)),
  pad (pad l n) m = pad (pad l m) n.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl; eauto.
  - destruct m; simpl; eauto. rewrite IHn. eauto.
  - destruct m; simpl; eauto. rewrite IHn; eauto.
Qed.

Lemma pad_idem : forall T n (l : list (option T)),
  pad (pad l n) n = pad l n.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl; eauto.
  - rewrite IHn. eauto.
  - rewrite IHn. eauto.
Qed.

Lemma thread_upd_upd_ne : forall opT opHiT tid tid' ts p p',
  tid <> tid' ->
  @thread_upd opT opHiT (@thread_upd opT opHiT ts tid p) tid' p' =
  @thread_upd opT opHiT (@thread_upd opT opHiT ts tid' p') tid p.
Proof.
  unfold thread_upd.
  intros.
  repeat rewrite list_upd_pad by eauto.
  rewrite list_upd_comm by eauto.
  f_equal.
  f_equal.
  apply pad_comm.
Qed.

Lemma thread_upd_upd_eq : forall opT opHiT tid ts p1 p2,
  @thread_upd opT opHiT (thread_upd ts tid p1) tid p2 =
  thread_upd ts tid p2.
Proof.
  unfold thread_upd; intros.
  rewrite list_upd_pad by eauto.
  rewrite pad_idem.
  rewrite list_upd_upd_eq by eauto.
  reflexivity.
Qed.

Theorem threads_empty_no_runnable : forall opT opHiT,
  no_runnable_threads (@threads_empty opT opHiT).
Proof.
  unfold no_runnable_threads, threads_empty, thread_get.
  intros.
  rewrite nth_error_nil.
  auto.
Qed.

Lemma no_runnable_threads_pad : forall opT opHiT n (ts : @threads_state opT opHiT),
  no_runnable_threads ts ->
  no_runnable_threads (pad ts n).
Proof.
  unfold no_runnable_threads, thread_get.
  induction n; simpl; eauto; intros.
  destruct ts0; simpl.
  - destruct tid; simpl; eauto.
  - destruct tid; simpl; eauto.
    destruct o; eauto.
    specialize (H 0); compute in H; congruence.
    eapply IHn; intros.
    specialize (H (S tid0)).
    eapply H.
Qed.

Lemma no_runnable_threads_list_upd : forall opT opHiT (ts : @threads_state opT opHiT) tid,
  no_runnable_threads ts ->
  no_runnable_threads (list_upd ts tid None).
Proof.
  unfold no_runnable_threads, thread_get.
  induction ts0; simpl; eauto; intros.
  destruct tid; simpl; eauto.
  - destruct tid0; simpl; eauto. specialize (H (S tid0)). apply H.
  - destruct tid0; simpl; eauto. specialize (H 0); simpl in H. eauto.
    eapply IHts0; intros. specialize (H (S tid1)). apply H.
Qed.

Lemma no_runnable_threads_upd_None : forall opT opHiT tid (ts : @threads_state opT opHiT),
  no_runnable_threads ts ->
  no_runnable_threads (thread_upd ts tid None).
Proof.
  unfold thread_upd; intros.
  eapply no_runnable_threads_list_upd.
  eapply no_runnable_threads_pad.
  eauto.
Qed.

Hint Resolve no_runnable_threads_upd_None.
Hint Resolve threads_empty_no_runnable.

Hint Rewrite thread_upd_upd_eq : t.


Definition init_state : State := fun tid' => 4.

Ltac exec_one tid' :=
  eapply ExecOne with (tid := tid');
    [ rewrite thread_upd_eq; reflexivity | | autorewrite with t ].

Hint Constructors exec_tid.

Definition ex_trace :
  { t : trace opT opHiT | exec op_step init_state ts t }.
Proof.
  eexists.
  unfold ts.
  unfold init_state.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    constructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    constructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  eapply ExecEmpty.
    eauto.
Defined.

Eval compute in (proj1_sig ex_trace).


Definition p2 : proc opHiT opHi2T _ :=
  _ <- Op IncTwice;
  Ret tt.

Definition ts2 := thread_upd threads_empty 1 (Some (existT _ _ p2)).

Definition ex_trace2 :
  { t : trace opHiT opHi2T | exec opHi_step init_state ts2 t }.
Proof.
  eexists.
  unfold ts2.
  unfold init_state.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    constructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind.
    econstructor.
    simpl; autorewrite with t.
  eapply ExecEmpty.
    eauto.
Defined.

Eval compute in (proj1_sig ex_trace2).


Inductive traces_match {opLoT opMidT opHiT} :
  forall (t1 : trace opLoT opMidT)
         (t2 : trace opMidT opHiT), Prop :=

| MatchInvokeLo : forall t1 t2 tid T (op : opLoT T),
  traces_match t1 t2 ->
  traces_match (TraceEvent (@InvokeLo opLoT opMidT tid _ op) t1) t2
| MatchReturnLo : forall t1 t2 tid T (r : T),
  traces_match t1 t2 ->
  traces_match (TraceEvent (@ReturnLo opLoT opMidT tid _ r) t1) t2

| MatchInvokeMid : forall t1 t2 tid T (op : opMidT T),
  traces_match t1 t2 ->
  traces_match (TraceEvent (@InvokeHi opLoT opMidT tid _ op) t1)
               (TraceEvent (@InvokeLo opMidT opHiT tid _ op) t2)
| MatchReturnMid : forall t1 t2 tid T (r : T),
  traces_match t1 t2 ->
  traces_match (TraceEvent (@ReturnHi opLoT opMidT tid _ r) t1)
               (TraceEvent (@ReturnLo opMidT opHiT tid _ r) t2)

| MatchInvokeHi : forall t1 t2 tid T (op : opHiT T),
  traces_match t1 t2 ->
  traces_match t1 (TraceEvent (@InvokeHi opMidT opHiT tid _ op) t2)
| MatchReturnHi : forall t1 t2 tid T (r : T),
  traces_match t1 t2 ->
  traces_match t1 (TraceEvent (@ReturnHi opMidT opHiT tid _ r) t2)

| MatchEmpty :
  traces_match (TraceEmpty opLoT opMidT) (TraceEmpty opMidT opHiT).

Hint Constructors traces_match.


Theorem ex_trace_ex_trace2 :
  traces_match (proj1_sig ex_trace) (proj1_sig ex_trace2).
Proof.
  simpl.
  eauto 20.
Qed.


Inductive compile_ok : forall T (p1 : proc opT opHiT T) (p2 : proc opHiT opHi2T T), Prop :=
| CompileIncTwice :
  compile_ok (inc_twice_impl) (@Op opHiT opHi2T _ IncTwice)
| CompileRet : forall T (x : T),
  compile_ok (@Ret opT opHiT T x) (@Ret opHiT opHi2T T x)
| CompileBind : forall T1 T2 (p1a : proc opT opHiT T1) (p2a : proc opHiT opHi2T T1)
                             (p1b : T1 -> proc opT opHiT T2) (p2b : T1 -> proc opHiT opHi2T T2),
  compile_ok p1a p2a ->
  (forall x, compile_ok (p1b x) (p2b x)) ->
  compile_ok (Bind p1a p1b) (Bind p2a p2b).

Theorem ex_compile_ok : compile_ok p1 p2.
Proof.
  unfold p1, p2.
  econstructor.
  econstructor.
  intros. econstructor.
Qed.

Hint Resolve ex_compile_ok.

Definition threads_compile_ok (ts1 : @threads_state opT opHiT) (ts2 : @threads_state opHiT opHi2T) :=
  forall tid,
    ts1 tid = None /\ ts2 tid = None \/
  (exists T p1 p2,
    ts1 tid = Some (existT _ T p1) /\ ts2 tid = Some (existT _ T p2) /\ compile_ok p1 p2).

Theorem ex_ts_compile_ok : threads_compile_ok ts ts2.
Proof.
  unfold threads_compile_ok, ts, ts2, thread_upd, threads_empty; intros.
  destruct tid; subst; compute; eauto.
  destruct tid; subst; compute; eauto.
  {
    right. do 3 eexists. intuition eauto.
  }
  destruct tid; subst; compute; eauto.
Qed.

Lemma thread_upd_inv : forall opT opHiT ts tid1 p tid2 p',
  @thread_upd opT opHiT ts tid1 (Some p) tid2 = Some p' ->
  tid1 = tid2 /\ p = p' \/
  tid1 <> tid2 /\ ts tid2 = Some p'.
Proof.
  intros.
  destruct (tid1 == tid2).
  - left; intuition eauto; subst.
    rewrite thread_upd_eq in H. congruence.
  - right; intuition eauto.
    rewrite thread_upd_ne in H; eauto.
Qed.

Lemma thread_empty_inv : forall opT opHiT tid p',
  @threads_empty opT opHiT tid = Some p' ->
  False.
Proof.
  unfold threads_empty; intros.
  destruct tid; compute in H; congruence.
Qed.

Lemma thread_upd_not_empty : forall opT opHiT tid ts p,
  no_runnable_threads (@thread_upd opT opHiT ts tid (Some p))
    -> False.
Proof.
  unfold no_runnable_threads; intros.
  specialize (H tid).
  rewrite thread_upd_eq in H.
  congruence.
Qed.

Lemma no_runnable_threads_some :
  forall opT opHiT (ts : @threads_state opT opHiT) tid p,
  ts tid = Some p ->
  no_runnable_threads ts ->
  False.
Proof.
  unfold no_runnable_threads; intros.
  specialize (H0 tid). congruence.
Qed.


Ltac sigT_eq' := match goal with
  | H : ?a = ?a |- _ =>
    clear H
  | H : existT _ _ _ = existT _ _ _ |- _ =>
    sigT_eq
  | H : existT _ _ _ = existT _ _ _ |- _ =>
    inversion H; clear H; subst
  end.

Ltac thread_inv :=
  match goal with
  | H : thread_get (thread_upd _ _ _) _ = Some _ |- _ =>
    eapply thread_upd_inv in H; destruct H; (intuition idtac); subst
  | H : thread_get threads_empty _ = Some _ |- _ =>
    eapply thread_empty_inv in H; exfalso; apply H
  | H : (_, _) = (_, _) |- _ =>
    inversion H; clear H; subst; repeat sigT_eq'
  | H : _ = Bind _ _ |- _ =>
    solve [ inversion H ]
  | H : _ = Ret _ _ _|- _ =>
    solve [ inversion H ]
  | H : no_runnable_threads (thread_upd _ _ _) |- _ =>
    solve [ eapply thread_upd_not_empty in H; exfalso; eauto ]
  | H : _ _ = Some _ |- _ =>
    solve [ exfalso; eapply no_runnable_threads_some; eauto ]
  | H : _ = _ |- _ =>
    congruence
  | H : _ = _ \/ _ = _ |- _ =>
    solve [ intuition congruence ]
  | H : ?a = ?a |- _ =>
    clear H
  end.

Ltac bind_inv :=
  match goal with
  | H : _ = Bind _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq'
  end.

Ltac exec_inv :=
  match goal with
  | H : exec _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq'
  end;
  autorewrite with t in *.

Ltac exec_tid_inv :=
  match goal with
  | H : exec_tid _ _ _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq'
  end;
  autorewrite with t in *.


Ltac empty_inv :=
  try solve [ exfalso; eapply thread_empty_inv; eauto ].

Ltac step_inv :=
  match goal with
  | H : op_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq'
  | H : opHi_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq'
  end.

Theorem ex_all_traces_match :
  forall s tr1 tr2,
  exec op_step s ts tr1 ->
  exec opHi_step s ts2 tr2 ->
  traces_match tr1 tr2.
Proof.
  intros.
  unfold ts, ts2 in *.

  repeat ( exec_inv; repeat thread_inv;
    try ( repeat exec_tid_inv; repeat thread_inv ) ).
  repeat step_inv.

  simpl.
  replace (s' 1 + 1 + 1) with (s' 1 + 2) by omega.
  eauto 20.
Qed.


(* [same_traces] ignores differences in low-level invoke/return events
 * and compares only high-level invoke/return events.  this is because
 * we intend to use [same_traces] for proving equivalence of atomic
 * brackets, and atomic brackets do change the possible low-level events
 * that can occur.  However, atomic brackets should not change the possible
 * high-level events.
 *)

Inductive low_event {opLoT opHiT} : event opLoT opHiT -> Prop :=
| LowEventInvoke : forall tid T op,
  low_event (@InvokeLo opLoT opHiT tid T op)
| LowEventReturn : forall tid T r,
  low_event (@ReturnLo opLoT opHiT tid T r).

Hint Constructors low_event.

Inductive high_event {opLoT opHiT} : event opLoT opHiT -> Prop :=
| HighEventInvoke : forall tid T op,
  high_event (@InvokeHi opLoT opHiT tid T op)
| HighEventReturn : forall tid T r,
  high_event (@ReturnHi opLoT opHiT tid T r).

Hint Constructors high_event.


Definition is_high_event {opLoT opHiT} (e : event opLoT opHiT) : {high_event e} + {low_event e}.
  destruct e; eauto.
Defined.

Fixpoint trace_filter_hi {opLoT opHiT} (t : trace opLoT opHiT) : trace opLoT opHiT :=
  match t with
  | TraceEmpty _ _ => TraceEmpty _ _
  | TraceEvent e t' =>
    match is_high_event e with
    | left _ => TraceEvent e (trace_filter_hi t')
    | right _ => trace_filter_hi t'
    end
  end.


Definition trace_match_hi {opLoT opHiT} (t1 t2 : trace opLoT opHiT) :=
  trace_filter_hi t1 = trace_filter_hi t2.


Theorem trace_match_hi_refl :
  forall opLoT opHiT (tr : trace opLoT opHiT),
    trace_match_hi tr tr.
Proof.
  unfold trace_match_hi; eauto.
Qed.

Hint Resolve trace_match_hi_refl.


Lemma trace_event_hi_lo : forall opLoT opHiT (e : event opLoT opHiT),
  low_event e \/ high_event e.
Proof.
  destruct e; eauto.
Qed.

Theorem trace_match_hi_trans :
  forall opLoT opHiT (tr1 tr2 tr3 : trace opLoT opHiT),
    trace_match_hi tr1 tr2 ->
    trace_match_hi tr2 tr3 ->
    trace_match_hi tr1 tr3.
Proof.
  unfold trace_match_hi; intros; congruence.
Qed.


Definition same_traces_s {opLo opHi State} op_step (s s' : State) (ts1 ts2 : @threads_state opLo opHi) :=
  forall tr,
    exec op_step s ts1 tr ->
    exists tr', exec op_step s' ts2 tr' /\
      trace_match_hi tr tr'.

Definition same_traces {opLo opHi State} op_step (s : State) (ts1 ts2 : @threads_state opLo opHi) :=
  forall tr,
    exec op_step s ts1 tr ->
    exists tr', exec op_step s ts2 tr' /\
      trace_match_hi tr tr'.


Definition p1_a :=
  _ <- Atomic inc_twice_impl;
  Ret tt.


Definition ts_a := thread_upd threads_empty 1 (Some (existT _ _ p1_a)).


Lemma exec_trace_eq : forall opLo opHi State op_step (s : State) (ts : @threads_state opLo opHi) tr1 tr2,
  exec op_step s ts tr1 ->
  tr1 = tr2 ->
  exec op_step s ts tr2.
Proof.
  intros; subst; eauto.
Qed.


Theorem ts_equiv_ts_a : forall s,
  same_traces op_step s ts ts_a.
Proof.
  unfold same_traces.
  intros.
  unfold ts, ts_a in *.

  repeat ( exec_inv; repeat thread_inv;
    try ( repeat exec_tid_inv; repeat thread_inv ) ).

  repeat match goal with
  | H : ?a = ?a |- _ => clear H
  end.

  repeat step_inv.
  unfold p1_a.

  eexists; split.

  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    eapply AtomicBind.
      eapply AtomicInvokeHi.
    eapply AtomicBind.
      eapply AtomicBind.
      eapply AtomicOpCall.
    eapply AtomicBind.
      eapply AtomicOpExec.
      constructor.
    eapply AtomicOpRet.
    eapply AtomicBind.
      eapply AtomicBind.
      eapply AtomicOpCall.
    eapply AtomicBind.
      eapply AtomicOpExec.
      constructor.
    eapply AtomicOpRet.
    eapply AtomicReturnHi.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
  eapply ExecEmpty.
    eauto.

  simpl.
  intros.
  eauto 20.
Qed.


Lemma trace_match_hi_prepend : forall opLo opMid evs (tr0 tr1 : trace opLo opMid),
  trace_match_hi tr0 tr1 ->
  trace_match_hi (prepend evs tr0) (prepend evs tr1).
Proof.
  unfold trace_match_hi.
  induction evs; simpl; intros.
  eauto.
  destruct (is_high_event a); eauto.
  erewrite IHevs; eauto.
Qed.

Lemma prepend_app : forall opT opHiT evs1 evs2 (tr : trace opT opHiT),
  prepend (evs1 ++ evs2) tr = prepend evs1 (prepend evs2 tr).
Proof.
  induction evs1; simpl; intros; eauto.
  rewrite IHevs1; eauto.
Qed.

Hint Resolve trace_match_hi_prepend.


Lemma low_high_event : forall opLoT opHiT (e : event opLoT opHiT),
  low_event e -> high_event e -> False.
Proof.
  destruct e; intros; inversion H; inversion H0.
Qed.

Hint Resolve low_high_event.

Lemma trace_match_hi_drop_lo_l : forall opLoT opHiT (e : event opLoT opHiT) tr1 tr2,
  low_event e ->
  trace_match_hi tr1 tr2 ->
  trace_match_hi (TraceEvent e tr1) tr2.
Proof.
  unfold trace_match_hi; intros.
  simpl.
  destruct (is_high_event e); eauto.
  exfalso; eauto.
Qed.

Lemma trace_match_hi_drop_lo_r : forall opLoT opHiT (e : event opLoT opHiT) tr1 tr2,
  low_event e ->
  trace_match_hi tr1 tr2 ->
  trace_match_hi tr1 (TraceEvent e tr2).
Proof.
  unfold trace_match_hi; intros.
  simpl.
  destruct (is_high_event e); eauto.
  exfalso; eauto.
Qed.

Hint Resolve trace_match_hi_drop_lo_l.
Hint Resolve trace_match_hi_drop_lo_r.


Instance same_traces_preorder {opT opHiT State op_step s} :
  PreOrder (@same_traces opT opHiT State op_step s).
Proof.
  split.
  - unfold Reflexive.
    unfold same_traces.
    eauto.
  - unfold Transitive.
    unfold same_traces.
    intros.
    eapply H in H1. deex.
    eapply H0 in H1. deex.
    eexists; intuition eauto.
    etransitivity; eauto.
Qed.


Definition trace_equiv_s {T} (s s' : State) tid (p1 p2 : proc opT opHiT T) :=
  forall (ts1 : threads_state),
  ts1 tid = Some (existT _ _ p1) ->
  same_traces_s op_step s s'
    ts1 (thread_upd ts1 tid (Some (existT _ _ p2))).

Definition trace_equiv {T} (p1 p2 : proc opT opHiT T) :=
  forall (ts1 : threads_state) tid s,
  ts1 tid = Some (existT _ _ p1) ->
  same_traces op_step s
    ts1 (thread_upd ts1 tid (Some (existT _ _ p2))).


Instance trace_match_hi_preorder {opLoT opHiT} :
  PreOrder (@trace_match_hi opLoT opHiT).
Proof.
  split.
  - intro t.
    eapply trace_match_hi_refl.
  - intros t1 t2 t3.
    eapply trace_match_hi_trans.
Qed.

Lemma pad_noop : forall n T (l : list (option T)),
  n <= length l ->
  pad l n = l.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl in *.
  omega.
  rewrite IHn; eauto.
  omega.
Qed.

Lemma thread_get_Some_length : forall tid opT opHiT (ts : @threads_state opT opHiT) t,
  thread_get ts tid = Some t ->
  tid < length ts.
Proof.
  unfold thread_get.
  induction tid; simpl; intros.
  - destruct ts0; try congruence. simpl. omega.
  - destruct ts0; try congruence. simpl.
    specialize (IHtid _ _ _ _ H).
    omega.
Qed.

Hint Resolve thread_get_Some_length.
Hint Resolve lt_le_S.

Lemma list_upd_noop : forall tid opT opHiT (ts : @threads_state opT opHiT) t,
  thread_get ts tid = Some t ->
  list_upd ts tid (Some t) = ts.
Proof.
  unfold thread_get.
  induction tid; simpl; intros.
  - destruct ts0; try congruence. simpl. congruence.
  - destruct ts0; try congruence. simpl. f_equal. eauto.
Qed.

Lemma list_upd_noop_None : forall tid opT opHiT (ts : @threads_state opT opHiT),
  thread_get ts tid = None ->
  tid < length ts ->
  list_upd ts tid None = ts.
Proof.
  unfold thread_get.
  induction tid; simpl; intros.
  - destruct ts0; try congruence. simpl. congruence.
    simpl. subst. congruence.
  - destruct ts0; try congruence. simpl. congruence.
    simpl. f_equal. eapply IHtid. 2: simpl in *; omega.
    eauto.
Qed.

Lemma thread_upd_same : forall tid opT opHiT (ts : @threads_state opT opHiT) T (p : proc _ _ T),
  ts tid = Some (existT _ _ p) ->
  thread_upd ts tid (Some (existT _ _ p)) = ts.
Proof.
  unfold thread_upd; intros.
  rewrite pad_noop by eauto.
  rewrite list_upd_noop; eauto.
Qed.

Instance trace_equiv_preorder {T} :
  PreOrder (@trace_equiv T).
Proof.
  split.
  - unfold Reflexive; intros.
    unfold trace_equiv; intros.
    rewrite thread_upd_same by eauto.
    reflexivity.
  - unfold Transitive; intros.
    unfold trace_equiv, same_traces; intros.
    eapply H in H2; try eassumption.
    deex.
    eapply H0 in H2.
    2: rewrite thread_upd_eq; reflexivity.
    deex.
    rewrite thread_upd_upd_eq in *.
    eexists; intuition eauto.
    etransitivity; eauto.
Qed.

Instance trace_equiv_proper {T} :
  Proper (Basics.flip trace_equiv ==> trace_equiv ==> Basics.impl) (@trace_equiv T).
Proof.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  repeat (etransitivity; eauto).
Qed.

Instance trace_equiv_proper_flip {T} :
  Proper (trace_equiv ==> Basics.flip trace_equiv ==> Basics.flip Basics.impl) (@trace_equiv T).
Proof.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  repeat (etransitivity; eauto).
Qed.


Definition exec_equiv_ts {opT opHiT} (ts1 ts2 : @threads_state opT opHiT) :=
  forall State op_step (s : State) tr,
    exec op_step s ts1 tr <->
    exec op_step s ts2 tr.

Definition exec_equiv_opt {opT opHiT} (p1 p2 : option {T : Type & proc opT opHiT T}) :=
  forall (ts : threads_state) tid,
    ts tid = p1 ->
    exec_equiv_ts ts (thread_upd ts tid p2).

Definition exec_equiv {opT opHiT T} (p1 p2 : proc opT opHiT T) :=
  exec_equiv_opt (Some (existT _ _ p1)) (Some (existT _ _ p2)).

Instance exec_equiv_ts_preorder {opLoT opHiT} :
  PreOrder (@exec_equiv_ts opLoT opHiT).
Proof.
  split.
  - firstorder.
  - unfold Transitive, exec_equiv_ts; intros.
    split; intros.
    + apply H0. apply H. eauto.
    + apply H. apply H0. eauto.
Qed.

Lemma thread_get_app_None : forall opT opHiT (ts : @threads_state opT opHiT) tid p,
  thread_get ts tid = Some p <->
  thread_get (ts ++ [None]) tid = Some p.
Admitted.

Lemma thread_upd_app_None : forall opT opHiT (ts : @threads_state opT opHiT) tid p0 p,
  thread_get ts tid = Some p0 ->
  thread_upd ts tid p ++ [None] =
  thread_upd (ts ++ [None]) tid p.
Admitted.

Lemma no_runnable_threads_app_None : forall opT opHiT (ts : @threads_state opT opHiT),
  no_runnable_threads ts <->
  no_runnable_threads (ts ++ [None]).
Admitted.


Theorem exec_equiv_ts_app_None : forall opT opHiT (ts : @threads_state opT opHiT),
  exec_equiv_ts ts (ts ++ [None]).
Proof.
  split; intros.
  - induction H.
    + eapply ExecOne with (tid := tid); eauto.
      eapply thread_get_app_None in H; eauto.
      erewrite thread_upd_app_None in *; eauto.
    + eapply ExecEmpty.
      eapply no_runnable_threads_app_None in H; eauto.
  - remember (ts0 ++ [None]); generalize dependent ts0;
      induction H; intros; subst.
    + eapply ExecOne with (tid := tid); eauto.
      eapply thread_get_app_None; eauto.
      eapply IHexec.
      erewrite thread_upd_app_None; eauto.
      eapply thread_get_app_None; eauto.
    + eapply ExecEmpty.
      eapply no_runnable_threads_app_None; eauto.
Qed.

Lemma pad_is_append : forall n T (l : list (option T)),
  pad l n = l ++ repeat None (n - length l).
Proof.
  induction n; simpl; intros.
  - rewrite app_nil_r; eauto.
  - destruct l; simpl.
    + rewrite IHn; simpl. replace (n - 0) with n by omega. reflexivity.
    + rewrite IHn. eauto.
Qed.

Lemma rev_repeat : forall n T (x : T),
  rev (repeat x n) = repeat x n.
Proof.
  induction n; simpl; eauto; intros.
  rewrite IHn.
Admitted.

Theorem exec_equiv_ts_pad : forall n opT opHiT (ts : @threads_state opT opHiT),
  exec_equiv_ts ts (pad ts n).
Proof.
  intros.
  rewrite pad_is_append.
  generalize (n - length ts0); intros.
  rewrite <- rev_repeat.
  induction n0; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc.
    etransitivity.
    2: eapply exec_equiv_ts_app_None.
    eauto.
Qed.

Instance exec_equiv_opt_preorder {opLoT opHiT} :
  PreOrder (@exec_equiv_opt opLoT opHiT).
Proof.
  split.
  - unfold exec_equiv_opt, Reflexive; intros.
    destruct x.
    + destruct s.
      rewrite thread_upd_same; eauto.
      reflexivity.
    + unfold thread_upd.
      rewrite list_upd_noop_None; eauto.
      eapply exec_equiv_ts_pad.
      rewrite thread_get_pad; eauto.
  - intros t1 t2 t3.
    unfold exec_equiv; split; intros.
    + eapply H in H2; eauto.
      eapply H0 in H2.
      2: rewrite thread_upd_eq; eauto.
      autorewrite with t in *. eauto.
    + eapply H; eauto.
      replace (thread_upd ts0 tid t3) with
              (thread_upd (thread_upd ts0 tid t2) tid t3) in H2.
      eapply H0 in H2; eauto.
      rewrite thread_upd_eq; eauto.
      rewrite thread_upd_upd_eq; eauto.
Qed.

Instance exec_equiv_preorder {opLoT opHiT T} :
  PreOrder (@exec_equiv opLoT opHiT T).
Proof.
  unfold exec_equiv.
  split.
  - intro t.
    reflexivity.
  - unfold Transitive; intros.
    etransitivity; eauto.
Qed.

Instance thread_upd_proper {opT opHiT} :
  Proper (eq ==> eq ==> exec_equiv_opt ==> exec_equiv_ts) (@thread_upd opT opHiT).
Proof.
  intros ts0 ts1 H; subst.
  intros tid tid' H'; subst.
  intros o0 o1 H'.

  unfold exec_equiv_ts; split; intros.
  - replace (thread_upd ts1 tid' o1) with
            (thread_upd (thread_upd ts1 tid' o0) tid' o1).
    apply H'; eauto.
    rewrite thread_upd_eq; eauto.
    autorewrite with t; eauto.
  - replace (thread_upd ts1 tid' o1) with
            (thread_upd (thread_upd ts1 tid' o0) tid' o1) in H.
    apply H' in H; eauto.
    rewrite thread_upd_eq; eauto.
    autorewrite with t; eauto.
Qed.

Instance thread_updS_proper {opT opHiT T} :
  Proper (eq ==> eq ==> exec_equiv ==> exec_equiv_ts) (@thread_updS opT opHiT T).
Proof.
  intros ts ts' H; subst.
  intros tid tid' H; subst.
  intros p p' H.
  eapply thread_upd_proper; eauto.
Qed.

Instance thread_updS_properTrace {T} :
  Proper (eq ==> eq ==> trace_equiv ==> same_traces op_step s) (@thread_updS opT opHiT T).
Proof.
  intros.
  intros ts0 ts1 H; subst.
  intros tid tid' H; subst.
  intros p1 p2 H.

  unfold trace_equiv in H.
  replace (thread_updS ts1 tid' p2) with
          (thread_updS (thread_updS ts1 tid' p1) tid' p2).
  2: unfold thread_updS; rewrite thread_upd_upd_eq; eauto.
  eapply H.
  unfold thread_updS; rewrite thread_upd_eq; eauto.
Qed.

Theorem exec_equiv_ret_bind : forall opT opHiT T T' (v : T) (p : T -> proc opT opHiT T'),
  exec_equiv (Bind (Ret v) p) (p v).
Proof.
  split; intros.
  - induction H0.
    + destruct (tid0 == tid); subst.
      * rewrite H0 in H. inversion H; clear H; subst.
        repeat sigT_eq'.
        repeat exec_tid_inv.
        simpl. eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        eapply IHexec.
        rewrite thread_upd_ne; eauto.
    + specialize (H0 tid). congruence.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Some ?p)) _ |- _ =>
      remember (thread_upd ts tid (Some p));
      generalize dependent ts;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * rewrite thread_upd_eq in H. inversion H; clear H. subst.
        rewrite <- app_nil_l with (l := evs).
        rewrite prepend_app.
        repeat sigT_eq'.
        eapply ExecOne with (tid := tid).
          eauto.
          constructor. constructor.
          autorewrite with t.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
          eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        eapply IHexec.
        rewrite thread_upd_ne by auto. auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.
Qed.

Theorem exec_equiv_ret_None : forall opT opHiT T (v : T),
  @exec_equiv_opt opT opHiT (Some (existT _ _ (Ret v))) None.
Proof.
  split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Some ?p)) _ |- _ =>
      remember (thread_upd ts tid (Some p));
      generalize dependent ts;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * rewrite thread_upd_eq in H. inversion H; clear H. subst.
        repeat sigT_eq'.
        repeat exec_tid_inv.
        simpl. eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.

  - replace tr with (prepend nil tr) by reflexivity.
    eapply ExecOne with (tid := tid).
      rewrite thread_upd_eq. eauto.
      eauto.
    autorewrite with t.
    eauto.
Qed.

Theorem exec_equiv_bind_ret : forall opT opHiT T (p : proc opT opHiT T),
  exec_equiv (Bind p Ret) p.
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Some ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Some pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * rewrite thread_upd_eq in H. inversion H; clear H. subst.
        repeat sigT_eq'.
        exec_tid_inv.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq in * by auto. eauto.
          eauto.
        autorewrite with t.

        destruct result0; eauto.

        eapply exec_equiv_ret_None in H1.
        eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Some ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Some pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * rewrite thread_upd_eq in H. inversion H; clear H. subst.
        repeat sigT_eq'.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t in *.
        destruct result; eauto.
        apply exec_equiv_ret_None; eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.
Qed.

Theorem exec_equiv_bind_bind : forall opT opHiT T1 T2 T3 (p1 : proc opT opHiT T1) (p2 : T1 -> proc opT opHiT T2) (p3 : T2 -> proc opT opHiT T3),
  exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Some ?p)) _ |- _ =>
      remember (thread_upd ts tid (Some p));
      generalize dependent ts;
      generalize dependent p3;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * rewrite thread_upd_eq in H. inversion H; clear H. subst.
        repeat sigT_eq'.
        exec_tid_inv.
        exec_tid_inv; try intuition congruence.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.

        destruct result; eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Some ?p)) _ |- _ =>
      remember (thread_upd ts tid (Some p));
      generalize dependent ts;
      generalize dependent p3;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * rewrite thread_upd_eq in H. inversion H; clear H. subst.
        repeat sigT_eq'.
        exec_tid_inv.

        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.

        destruct result0; eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.
Qed.


Instance trace_equiv_exec_equiv_proper {T} :
  Proper (exec_equiv ==> exec_equiv ==> iff) (@trace_equiv T).
Proof.
  intros p1 p1' ?.
  intros p2 p2' ?.
  split; intros.
  - unfold trace_equiv, same_traces; intros.
    pose proof (thread_upd_same _ _ H2).
    rewrite <- H4 in H3.
    apply H in H3.
    eapply H1 in H3.
    2: rewrite thread_upd_eq; reflexivity.
    rewrite thread_upd_upd_eq in *; deex.
    apply H0 in H3.
    eexists; intuition eauto.
  - unfold trace_equiv, same_traces; intros.
    pose proof (thread_upd_same _ _ H2).
    rewrite <- H4 in H3.
    apply H in H3.
    eapply H1 in H3.
    2: rewrite thread_upd_eq; reflexivity.
    rewrite thread_upd_upd_eq in *; deex.
    apply H0 in H3.
    eexists; intuition eauto.
Qed.


Hint Constructors exec_tid.
Hint Constructors atomic_exec.

Hint Resolve no_runnable_threads_some.


Lemma trace_equiv_opret :
  forall T T' (p : T -> proc opT opHiT T') (v : T),
  trace_equiv (Bind (OpRet v) p)
              (p v).
Proof.
  unfold trace_equiv, same_traces. intros.

  induction H0.

  - destruct (tid == tid0); subst.
    + rewrite H0 in H.
      inversion H; clear H; subst.
      repeat sigT_eq'.
      exec_tid_inv.
      exec_tid_inv.

      eexists; split.
      eauto.
      constructor.

    + edestruct IHexec; intuition idtac.
      rewrite thread_upd_ne; eauto.

      eexists; split.

      eapply ExecOne with (tid := tid0).
      rewrite thread_upd_ne by assumption.
      eauto.

      eauto.

      rewrite thread_upd_upd_ne by assumption.
      eauto.
      eauto.

  - exfalso; eauto.
Qed.


Lemma trace_equiv_opcall :
  forall T T' (p : unit -> proc opT opHiT T') (op : opT T),
  trace_equiv (Bind (OpCall op) p)
              (p tt).
Proof.
  unfold trace_equiv, same_traces; intros.

  induction H0.

  - destruct (tid == tid0); subst.
    + rewrite H0 in H.
      inversion H; clear H; subst.
      repeat sigT_eq'.
      exec_tid_inv.
      exec_tid_inv.

      eexists; intuition eauto.
      constructor.

    + edestruct IHexec; intuition idtac.
      rewrite thread_upd_ne; eauto.

      eexists; split.

      eapply ExecOne with (tid := tid0).
      rewrite thread_upd_ne by assumption.
      eauto.

      eauto.

      rewrite thread_upd_upd_ne by assumption.
      eauto.
      eauto.

  - exfalso; eauto.
Qed.

Theorem trace_equiv_opexec :
  forall T T' op (p : T -> proc opT opHiT T'),
  trace_equiv (Bind (OpExec op) p)
              (Bind (Atomic (Op op)) p).
Proof.
  unfold trace_equiv, same_traces; intros.

  induction H0.

  - destruct (tid == tid0).
    + subst.
      rewrite H0 in H.
      inversion H; clear H; subst.
      repeat sigT_eq'.
      repeat exec_tid_inv.

      eexists; split.

      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_eq. reflexivity.
        eapply ExecTidBind; eauto.
        eapply ExecTidAtomic.
        eapply AtomicBind.
        eapply AtomicOpCall.
        eapply AtomicBind.
        eapply AtomicOpExec.
        eauto.
        eapply AtomicOpRet.
        autorewrite with t.
        eauto.

      simpl.
      eauto.

    + edestruct IHexec; intuition idtac.
      rewrite thread_upd_ne; eauto.

      eexists; split.

      eapply ExecOne with (tid := tid0).
      rewrite thread_upd_ne by assumption.
      eauto.

      eauto.

      rewrite thread_upd_upd_ne by assumption.
      eauto.
      eauto.

  - exfalso; eauto.
Qed.

Theorem trace_equiv_bind_a : forall T T' (p : proc _ _ T) (p2 p2' : T -> proc _ _ T'),
  (forall x, trace_equiv (p2 x) (p2' x)) ->
  trace_equiv (Bind p p2) (Bind p p2').
Proof.
  intros.
  unfold trace_equiv, same_traces; intros.

  generalize dependent p.
  induction H1; intros.

  - destruct (tid0 == tid); subst.
    + rewrite H3 in H0.
      inversion H0; clear H0; subst.
      repeat sigT_eq'.
      exec_tid_inv.
      destruct result0.

      * edestruct H; eauto.
        rewrite thread_upd_eq; eauto.
        intuition idtac.

        autorewrite with t in *.
        eexists; split.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
          autorewrite with t.
          eauto.

        eauto.

      * edestruct IHexec.
        rewrite thread_upd_eq; eauto.
        intuition idtac.

        autorewrite with t in *.
        eexists; split.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.
        eauto.

        intuition eauto.

    + edestruct IHexec.
      rewrite thread_upd_ne; eauto.

      eexists; split.
      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_upd_ne by auto.
      intuition eauto.
      intuition eauto.
  - exfalso; eauto.
Qed.


Theorem trace_equiv_op :
  forall T T' op (p : T -> proc opT opHiT T'),
  trace_equiv (Bind (Op op) p)
              (Bind (Atomic (Op op)) p).
Proof.
  intros.
  unfold Op at 1.
  rewrite exec_equiv_bind_bind.
  rewrite trace_equiv_opcall.
  rewrite exec_equiv_bind_bind.
  rewrite trace_equiv_opexec.
  eapply trace_equiv_bind_a.

  intros.
  rewrite trace_equiv_opret.
  reflexivity.
Qed.


Lemma inc_commutes_op_step : forall T (op : opT T) tid s v s',
  op_step op tid s v s' ->
  forall tid0,
  tid0 <> tid ->
  op_step op tid
    (fun tid' => if tid' == tid0 then s tid' + 1 else s tid')
    v
    (fun tid' => if tid' == tid0 then s' tid' + 1 else s' tid').
Proof.
  intros.
  inversion H; clear H; subst; repeat sigT_eq.
  + match goal with
    | |- op_step _ _ ?s0 _ _ =>
      remember s0
    end.
    match goal with
    | |- op_step _ _ ?s0 _ ?s1 =>
      replace s1 with (fun tid' => if tid' == tid then s0 tid' + 1 else s0 tid')
    end.
    match goal with
    | |- op_step _ ?tid ?s0 ?r _ =>
      replace r with (s0 tid + 1)
    end.
    constructor.
    subst. destruct (tid == tid0); congruence.
    subst. apply functional_extensionality; intros.
      destruct (x == tid0); destruct (x == tid); congruence.
  + constructor.
Qed.

Lemma inc_commutes_op_step' : forall T (op : opT T) tid s v s',
  op_step op tid s v s' ->
  forall tid0,
  tid0 <> tid ->
  s tid0 = s' tid0.
Proof.
  intros.
  inversion H; clear H; subst; repeat sigT_eq.
  + destruct (tid0 == tid); congruence.
  + congruence.
Qed.

Lemma inc_commutes_exec_tid : forall tid0 tid1 T s p s' result' evs,
  tid0 <> tid1 ->
  @exec_tid opT opHiT State op_step T tid1 s p s' result' evs ->
  @exec_tid opT opHiT State op_step T tid1 (fun tid => if tid == tid0 then s tid + 1 else s tid) p
                        (fun tid => if tid == tid0 then s' tid + 1 else s' tid) result' evs.
Proof.
  intros.
  induction H0; simpl; eauto.
  - constructor.
    eapply inc_commutes_op_step; eauto.
  - constructor.
    induction H0; eauto.
    constructor.
    eapply inc_commutes_op_step; eauto.
Qed.

Lemma inc_commutes_exec_tid' : forall T tid0 s p s' result' evs,
  @exec_tid opT opHiT State op_step T tid0 s p s' result' evs ->
  forall tid1, tid0 <> tid1 ->
  s tid1 = s' tid1.
Proof.
  intros.
  induction H; eauto.
  - eapply inc_commutes_op_step'; eauto.
  - induction H; eauto.
    + eapply eq_trans.
      apply IHatomic_exec1; eauto.
      apply IHatomic_exec2; eauto.
    + eapply inc_commutes_op_step'; eauto.
Qed.


Theorem inc_commutes_0 :
  forall T s tid (p1 p2 : _ -> proc opT opHiT T),
  (forall r, trace_equiv (p1 r) (p2 r)) ->
  trace_equiv_s s (fun tid' => if tid' == tid then s tid' + 1 else s tid')
                tid (r <- OpExec Inc; p1 r) (p2 (s tid + 1)).
Proof.
  unfold trace_equiv_s, same_traces_s; intros.

  induction H1.

  - destruct (tid0 == tid); subst.
    + rewrite H1 in H0. inversion H0; clear H0; subst.
      repeat sigT_eq'.
      repeat exec_tid_inv.
      step_inv.
      edestruct H. 2: eauto. rewrite thread_upd_eq; eauto.
      intuition idtac. autorewrite with t in *.
      eexists; split; eauto.

    + edestruct IHexec.
      rewrite thread_upd_ne; eauto.
      intuition idtac.

      eexists; split.
      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eapply inc_commutes_exec_tid; eauto.
        rewrite thread_upd_upd_ne by auto.
        eapply inc_commutes_exec_tid' in H2.
        rewrite H2.
        eauto.
        eauto.
      auto.

  - exfalso; eauto.
Qed.


Theorem inc_commutes_1 :
  forall TA T' (ap : proc _ _ TA)
            (p1 : proc opT opHiT T')
            (p2 : _ -> proc opT opHiT T'),
  (forall s tid,
    trace_equiv_s s (fun tid' => if tid' == tid then s tid' + 1 else s tid')
                  tid p1 (p2 (s tid + 1))) ->
  trace_equiv (_ <- Atomic ap; p1)
              (r <- Atomic (_ <- ap; Op Inc); p2 r).
Proof.
  unfold trace_equiv, same_traces; intros.

  induction H1.

  - destruct (tid0 == tid); subst.
    + rewrite H1 in H0. inversion H0; clear H0; subst.
      repeat sigT_eq'.
      repeat exec_tid_inv.

      eapply H in H3. deex.
      2: rewrite thread_upd_eq; eauto.

      eexists; split.

      eapply ExecOne with (tid := tid).
        rewrite thread_upd_eq; reflexivity.
        eapply ExecTidBind.
        eapply ExecTidAtomic.
        eapply AtomicBind.
        eauto.
        eapply AtomicBind.
        eapply AtomicOpCall.
        eapply AtomicBind.
        eapply AtomicOpExec.
        constructor. (* INC semantics *)
        eapply AtomicOpRet.
      simpl. autorewrite with t in *.
      eauto.

      rewrite prepend_app. simpl. eauto.

    + edestruct IHexec.
      rewrite thread_upd_ne; eauto.

      eexists; split.
      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_upd_ne by auto.
      intuition eauto.
      intuition eauto.

  - exfalso; eauto.
Qed.


Theorem trace_equiv_s_trans : forall T s s' tid p0 p1 p2,
  trace_equiv p0 p1 ->
  trace_equiv_s s s' tid p1 p2 ->
  (@trace_equiv_s T s s' tid p0 p2).
Proof.
  intros.
  unfold trace_equiv_s, same_traces_s; intros.
  edestruct H; eauto. intuition idtac.
  edestruct H0; eauto. rewrite thread_upd_eq; eauto. intuition idtac.
  autorewrite with t in *.
  eexists. intuition eauto.
  etransitivity; eauto.
Qed.


Theorem inc_commutes_final :
  forall TA T' (ap : proc _ _ TA) (p : _ -> proc opT opHiT T'),
  trace_equiv (_ <- Atomic ap; r <- Op Inc; p r)
              (r <- Atomic (_ <- ap; Op Inc); p r).
Proof.
  intros.
  eapply inc_commutes_1.

  intros; unfold Op.

  eapply trace_equiv_s_trans.
  rewrite exec_equiv_bind_bind.
  apply trace_equiv_opcall.

  eapply trace_equiv_s_trans.
  rewrite exec_equiv_bind_bind.
  reflexivity.

  eapply inc_commutes_0.

  intros.
  eapply trace_equiv_opret.
Qed.


Definition inc_twice_impl_atomic :=
  _ <- InvokeOpHi IncTwice;
  r <- Atomic (_ <- Op Inc; Op Inc);
  ReturnOpHi r.


Theorem trace_equiv_bind : forall T1 T2 (p1 p1' : proc _ _ T1) (p2 p2' : T1 -> proc _ _ T2),
  (forall T (rx : _ -> proc _ _ T), trace_equiv (Bind p1 rx) (Bind p1' rx)) ->
  (forall T (rx : _ -> proc _ _ T), (forall x, trace_equiv (Bind (p2 x) rx) (Bind (p2' x) rx))) ->
  (forall T (rx : _ -> proc _ _ T), trace_equiv (Bind (Bind p1 p2) rx) (Bind (Bind p1' p2') rx)).
Proof.
  intros.
  repeat rewrite exec_equiv_bind_bind.
  rewrite H.
  eapply trace_equiv_bind_a.
  eauto.
Qed.


Theorem trace_equiv_bind_swap' : forall T1 T2 T3 (p1 : proc _ _ T1) (p2 : T1 -> proc _ _ T2) (p3 : T2 -> proc _ _ T3),
  trace_equiv (Bind (Bind p1 p2) p3)
              (Bind p1 (fun x => Bind (p2 x) p3)).
Proof.
  intros.
  rewrite exec_equiv_bind_bind.
  reflexivity.
Qed.

Theorem trace_equiv_bind_swap'' : forall T1 T2 T3 (p1 : proc _ _ T1) (p2 : T1 -> proc _ _ T2) (p3 : T2 -> proc _ _ T3),
  trace_equiv (Bind p1 (fun x => Bind (p2 x) p3))
              (Bind (Bind p1 p2) p3).
Proof.
  intros.
  rewrite exec_equiv_bind_bind.
  reflexivity.
Qed.


Theorem trace_equiv_bind_swap : forall T1 T2 T3 (p1 : proc _ _ T1) (p2 : T1 -> proc _ _ T2) (p3 : T1 -> T2 -> proc _ _ T3),
  trace_equiv (Bind p1 (fun x => Bind (p2 x) (p3 x)))
              (Bind (Bind p1 (fun x => Bind (p2 x) (fun y => Ret (x, y))))
                    (fun p => p3 (fst p) (snd p))).
Proof.
  intros.
  rewrite <- trace_equiv_bind_swap''.
  eapply trace_equiv_bind_a; intros.
  rewrite exec_equiv_bind_bind.
  eapply trace_equiv_bind_a; intros.
  rewrite exec_equiv_ret_bind.
  simpl.
  reflexivity.
Qed.


Theorem inc_twice_atomic : forall T (rx : _ -> proc _ _ T),
  trace_equiv (Bind inc_twice_impl rx) (Bind inc_twice_impl_atomic rx).
Proof.
  unfold inc_twice_impl, inc_twice_impl_atomic.

  eapply trace_equiv_bind.
  reflexivity.
  intros.

  etransitivity.
  rewrite exec_equiv_bind_bind.
  apply trace_equiv_op.

  (* would be nice to have the right rewrite rules here, so that we can
     just [rewrite exec_equiv_bind_bind] in a continuation of the left-hand side
   *)
  etransitivity.
  eapply trace_equiv_bind_a.
  intros.
  rewrite exec_equiv_bind_bind at 1.

  match goal with
  | |- trace_equiv ?p1 _ =>
    instantiate (1 := fun x0 => p1)
  end.
  reflexivity.

  etransitivity.
  eapply inc_commutes_final.

  simpl.
  rewrite exec_equiv_bind_bind.
  reflexivity.
Qed.


Definition trace_match_one_thread {opLoT opMidT opHiT State T} lo_step hi_step
                                            (p1 : proc opLoT opMidT T)
                                            (p2 : proc opMidT opHiT T) :=
  forall (s : State) tr1,
    exec lo_step s (thread_upd threads_empty 1 (Some (existT _ _ p1))) tr1 ->
    exists tr2,
      exec hi_step s (thread_upd threads_empty 1 (Some (existT _ _ p2))) tr2 /\
      traces_match tr1 tr2.

Instance trace_match_one_thread_proper {opLoT opMidT opHiT State T lo_step hi_step} :
  Proper (exec_equiv ==> exec_equiv ==> Basics.flip Basics.impl) (@trace_match_one_thread opLoT opMidT opHiT State T lo_step hi_step).
Proof.
  intros p1 p1'; intros.
  intros p2 p2'; intros.
  unfold Basics.flip, Basics.impl; intros.
  unfold trace_match_one_thread in *; intros.
  apply H in H2.
  apply H1 in H2.
  destruct H2.
  eexists; intuition eauto.
  apply H0. eauto.
Qed.

Lemma traces_match_trace_match_hi : forall opLoT opMidT opHiT
  (tr1 : trace opLoT opMidT) (tr2 : trace opMidT opHiT),
  traces_match tr1 tr2 ->
  forall tr1',
  trace_match_hi tr1 tr1' ->
  traces_match tr1' tr2.
Proof.
  induction 1; simpl; intros; eauto.
  - generalize dependent t2.
    generalize dependent t1.
    induction tr1'; simpl; intros.
    + destruct e; eauto.
      * inversion H0; clear H0; subst; repeat sigT_eq.
        constructor. eauto.
      * inversion H0.
    + inversion H0.
  - generalize dependent t2.
    generalize dependent t1.
    induction tr1'; simpl; intros.
    + destruct e; eauto.
      * inversion H0.
      * inversion H0; clear H0; subst; repeat sigT_eq.
        constructor. eauto.
    + inversion H0.
  - induction tr1'; simpl; intros.
    + destruct e; eauto.
      * inversion H.
      * inversion H.
    + constructor.
Qed.

Instance trace_match_one_thread_proper2 {T opHi2T hi_step} :
  Proper (trace_equiv ==> exec_equiv ==> Basics.flip Basics.impl) (@trace_match_one_thread opT opHiT opHi2T State T op_step hi_step).
Proof.
  intros p1 p1'; intros.
  intros p2 p2'; intros.
  unfold Basics.flip, Basics.impl; intros.
  unfold trace_match_one_thread in *; intros.
  eapply H in H2. 2: rewrite thread_upd_eq; eauto.
  deex.
  apply H1 in H2.
  deex.
  eexists; intuition eauto.
  apply H0. eauto.
  eapply traces_match_trace_match_hi; eauto.
  unfold trace_match_hi in *; congruence.
Qed.

Theorem all_single_thread_traces_match' :
  forall T T' (p1 : proc opT opHiT T) (p2 : proc opHiT opHi2T T) (p1rest : T -> proc opT opHiT T') (p2rest : T -> proc opHiT opHi2T T'),
  (forall x, trace_match_one_thread op_step opHi_step (p1rest x) (p2rest x)) ->
  compile_ok p1 p2 ->
  trace_match_one_thread op_step opHi_step (Bind p1 p1rest) (Bind p2 p2rest).
Proof.
  intros.
  generalize dependent p2rest.
  generalize dependent p1rest.
  induction H0; intros.

  - rewrite inc_twice_atomic.

    unfold trace_match_one_thread; intros.

    exec_inv; repeat thread_inv.
    autorewrite with t in *.
    repeat ( exec_tid_inv; intuition try congruence ).

    exec_inv; repeat thread_inv.
    autorewrite with t in *.
    repeat ( exec_tid_inv; intuition try congruence ).

    repeat match goal with
    | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.
    repeat step_inv.

    exec_inv; repeat thread_inv.
    autorewrite with t in *.
    repeat ( exec_tid_inv; intuition try congruence ).

    apply H in H3. deex.

    eexists; split.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eapply ExecTidBind.
      eapply ExecTidBind.
      eapply ExecTidOpCall.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eapply ExecTidBind.
      eapply ExecTidBind.
      eapply ExecTidOpRun.
      constructor.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eapply ExecTidBind.
      eapply ExecTidOpRet.
    autorewrite with t.

    match goal with
    | H : exec _ ?s1 (thread_upd _ _ (Some ?p1)) _ |-
          exec _ ?s2 (thread_upd _ _ (Some ?p2)) _ =>
      replace p2 with p1; [ replace s2 with s1; [ eauto | ] | ]
    end.

    apply functional_extensionality; intros.
    destruct (x == 1); omega.

    f_equal. f_equal. omega.

    simpl.
    repeat constructor.
    replace (s1 1 + 1 + 1) with (s1 1 + 2) by omega.
    eauto.

  - unfold trace_match_one_thread in *; intros.

    exec_inv; repeat thread_inv; autorewrite with t in *.
    repeat exec_tid_inv; try intuition congruence.

    edestruct H; eauto. intuition try congruence.
    eexists. split.

    exec_one 1.
      eapply ExecTidBind. eauto. eauto.
      autorewrite with t; simpl.

    eauto.

  - rewrite exec_equiv_bind_bind.
    rewrite exec_equiv_bind_bind.
    eapply IHcompile_ok.
    intros.
    eapply H1.
    eapply H2.
Qed.

Theorem all_single_thread_traces_match :
  forall T' (p1 : proc opT opHiT T') (p2 : proc opHiT opHi2T T'),
  compile_ok p1 p2 ->
  trace_match_one_thread op_step opHi_step p1 p2.
Proof.
  intros.
  unfold trace_match_one_thread; intros.
  eapply exec_equiv_bind_ret in H0.
  eapply all_single_thread_traces_match' in H0; eauto.
  deex.
  eexists; split; eauto.
  eapply exec_equiv_bind_ret.
  eauto.

  clear H0.
  unfold trace_match_one_thread; intros.
  eapply exec_equiv_ret_None in H0.
  exec_inv; repeat thread_inv.

  eexists; split.
  eapply exec_equiv_ret_None.
  eapply ExecEmpty; eauto.

  eauto.
Qed.


Inductive compile_ok_atomic : forall T (p1 : proc opT opHiT T) (p2 : proc opHiT opHi2T T), Prop :=
| CompileAIncTwiceCall :
  compile_ok_atomic (InvokeOpHi IncTwice) (@OpCall opHiT opHi2T _ IncTwice)
| CompileAIncTwiceExec :
  compile_ok_atomic (Atomic (_ <- Op Inc; Op Inc)) (@OpExec opHiT opHi2T _ IncTwice)
| CompileAIncTwiceRet : forall T (r : T),
  compile_ok_atomic (ReturnOpHi r) (@OpRet opHiT opHi2T _ r)
| CompileARet : forall T (x : T),
  compile_ok_atomic (@Ret opT opHiT T x) (@Ret opHiT opHi2T T x)
| CompileABind : forall T1 T2 (p1a : proc opT opHiT T1) (p2a : proc opHiT opHi2T T1)
                             (p1b : T1 -> proc opT opHiT T2) (p2b : T1 -> proc opHiT opHi2T T2),
  compile_ok_atomic p1a p2a ->
  (forall x, compile_ok_atomic (p1b x) (p2b x)) ->
  compile_ok_atomic (Bind p1a p1b) (Bind p2a p2b).

Definition compile_ok_all_atomic (ts1 ts2 : threads_state) :=
  forall tid,
    (ts1 tid = None /\ ts2 tid = None) \/
    exists T p1 p2,
    ts1 tid = Some (existT _ T p1) /\ ts2 tid = Some (existT _ T p2) /\
    compile_ok_atomic p1 p2.

Definition trace_match_threads {opLoT opMidT opHiT State} lo_step hi_step
                                            (ts1 : @threads_state opLoT opMidT)
                                            (ts2 : @threads_state opMidT opHiT) :=
  forall (s : State) tr1,
    exec lo_step s ts1 tr1 ->
    exists tr2,
      exec hi_step s ts2 tr2 /\
      traces_match tr1 tr2.

Lemma compile_ok_all_atomic_del : forall ts1 ts2 tid,
  compile_ok_all_atomic ts1 ts2 ->
  compile_ok_all_atomic (thread_upd ts1 tid None) (thread_upd ts2 tid None).
Proof.
  unfold compile_ok_all_atomic; intros.
  specialize (H tid0).
  destruct (tid == tid0); subst.
  - repeat rewrite thread_upd_eq; intuition eauto.
  - repeat rewrite thread_upd_ne by auto. intuition eauto.
Qed.

Lemma compile_ok_atomic_thread_upd : forall ts1 ts2 T p1 p2 tid,
  compile_ok_all_atomic ts1 ts2 ->
  compile_ok_atomic p1 p2 ->
  compile_ok_all_atomic (thread_upd ts1 tid (Some (existT _ T p1)))
                        (thread_upd ts2 tid (Some (existT _ T p2))).
Proof.
  unfold compile_ok_all_atomic; intros.
  specialize (H tid0).
  destruct (tid == tid0); subst.
  - repeat rewrite thread_upd_eq.
    right.
    do 3 eexists.
    intuition eauto.
  - repeat rewrite thread_upd_ne by auto. intuition eauto.
Qed.

Lemma traces_match_prepend : forall opLoT opMidT opHiT (tr1 : trace opLoT opMidT) (tr2 : trace opMidT opHiT) evs evs',
  traces_match tr1 tr2 ->
  traces_match (prepend evs (TraceEmpty _ _)) (prepend evs' (TraceEmpty _ _)) ->
  traces_match (prepend evs tr1) (prepend evs' tr2).
Proof.
  intros.
  remember (prepend evs (TraceEmpty _ _)).
  remember (prepend evs' (TraceEmpty _ _)).
  generalize dependent evs'.
  generalize dependent evs.
  induction H0; intros.
  all: destruct evs; simpl in *.
  all: try inversion Heqt.
  all: subst.
  all: try solve [ constructor ; eauto ].

  all: destruct evs'; simpl in *.
  all: try inversion Heqt0.
  all: subst.
  all: try solve [ constructor; eauto ].

  all: try solve [ constructor; specialize (IHtraces_match nil); simpl in *; eauto ].
  all: try solve [ constructor; specialize (IHtraces_match ([e] ++ evs)); simpl in *; eauto ].

  eauto.
Qed.

Lemma compile_ok_atomic_exec_tid : forall T (p1 : proc _ _ T) p2,
  compile_ok_atomic p1 p2 ->
  forall tid s s' result evs,
  exec_tid op_step tid s p1 s' result evs ->
  exists result' evs',
  exec_tid opHi_step tid s p2 s' result' evs' /\
  traces_match (prepend evs (TraceEmpty _ _)) (prepend evs' (TraceEmpty _ _)) /\
  match result with
  | inl v => match result' with
    | inl v' => v = v'
    | inr _ => False
    end
  | inr p' => match result' with
    | inl _ => False
    | inr p'' => compile_ok_atomic p' p''
    end
  end.
Proof.
  induction 1; intros.

  - exec_tid_inv.
    do 2 eexists; split.
    constructor.
    split.
    simpl; eauto.
    eauto.

  - exec_tid_inv.
    repeat match goal with
    | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.
    repeat step_inv.
    do 2 eexists; split.
    constructor.

    match goal with
    | |- opHi_step _ _ _ _ ?s =>
      replace s with (fun tid' => if tid' == tid then s1 tid' + 2 else s1 tid')
    end.
    constructor.

    apply functional_extensionality; intros.
    destruct (x == tid); omega.

    split.
    simpl; eauto.

    destruct (tid == tid); omega.

  - exec_tid_inv.
    do 2 eexists; split.
    constructor.
    split.
    simpl; eauto.
    eauto.

  - exec_tid_inv.
    do 2 eexists; split.
    constructor.
    split.
    simpl; eauto.
    eauto.

  - exec_tid_inv.
    eapply IHcompile_ok_atomic in H12.
    repeat deex.

    destruct result0; destruct result'; try solve [ exfalso; eauto ].

    + do 2 eexists; split.
      eauto.
      split.
      eauto.
      subst; eauto.

    + do 2 eexists; split.
      eauto.
      split.
      eauto.
      constructor.
      eauto.
      eauto.
Qed.

Theorem all_traces_match_0 :
  forall ts1 ts2,
  compile_ok_all_atomic ts1 ts2 ->
  trace_match_threads op_step opHi_step ts1 ts2.
Proof.
  unfold trace_match_threads; intros.
  generalize dependent ts3.
  induction H0; intros.
  - specialize (H2 tid) as H2'.
    intuition try congruence.
    repeat deex.
    rewrite H3 in H; inversion H; clear H; subst.
    repeat sigT_eq'.

    edestruct compile_ok_atomic_exec_tid; eauto.
    repeat deex.

    edestruct IHexec.
    shelve.
    intuition idtac.

    eexists; split.
    eapply ExecOne with (tid := tid).
      eauto.
      eauto.
      eauto.

    eapply traces_match_prepend; eauto.
    Unshelve.

    destruct result, x; simpl in *; try solve [ exfalso; eauto ].
    eapply compile_ok_all_atomic_del; eauto.
    eapply compile_ok_atomic_thread_upd; eauto.

  - eexists; split.
    eapply ExecEmpty.
    2: eauto.

    intros.
      unfold no_runnable_threads; intros.
      specialize (H tid).
      specialize (H0 tid).
      intuition eauto.
    repeat deex.
    congruence.
Qed.

Inductive atomize_ok : forall T (p1 : proc opT opHiT T) (p2 : proc opT opHiT T), Prop :=
| AtomizeIncTwice :
  atomize_ok (inc_twice_impl) (inc_twice_impl_atomic)
| AtomizeRet : forall T (x : T),
  atomize_ok (Ret x) (Ret x)
| AtomizeBind : forall T1 T2 (p1a p2a : proc opT opHiT T1)
                             (p1b p2b : T1 -> proc opT opHiT T2),
  atomize_ok p1a p2a ->
  (forall x, atomize_ok (p1b x) (p2b x)) ->
  atomize_ok (Bind p1a p1b) (Bind p2a p2b).

Definition atomize_ok_all (ts1 ts2 : threads_state) :=
  forall tid,
    (ts1 tid = None /\ ts2 tid = None) \/
    exists T p1 p2,
    ts1 tid = Some (existT _ T p1) /\ ts2 tid = Some (existT _ T p2) /\
    atomize_ok p1 p2.

Definition compile_ok_all (ts1 ts2 : threads_state) :=
  forall tid,
    (ts1 tid = None /\ ts2 tid = None) \/
    exists T p1 p2,
    ts1 tid = Some (existT _ T p1) /\ ts2 tid = Some (existT _ T p2) /\
    compile_ok p1 p2.

Fixpoint compile_atomic T (p : proc opHiT opHi2T T) : proc opT opHiT T :=
  match p with
  | Ret t => Ret t
  | OpCall op => InvokeOpHi op
  | OpExec op =>
    match op with
    | IncTwice => Atomic (_ <- Op Inc; Op Inc)
    | Noop2 => Atomic (Ret tt)
    end
  | OpRet r => ReturnOpHi r
  | Bind p1 p2 =>
    Bind (compile_atomic p1) (fun r => compile_atomic (p2 r))
  | InvokeOpHi _ => Ret tt
  | ReturnOpHi v => Ret v
  | Atomic p => Atomic (compile_atomic p)
  end.

Definition atomize_ok_all_upto n (ts1 ts2 : threads_state) :=
  forall tid,
    (tid < n ->
     (ts1 tid = None /\ ts2 tid = None) \/
     exists T p1 p2,
     ts1 tid = Some (existT _ T p1) /\ ts2 tid = Some (existT _ T p2) /\
     atomize_ok p1 p2) /\
    (tid >= n ->
     ts1 tid = ts2 tid).

Lemma atomize_ok_all_upto_0 : forall (ts1 ts2 : threads_state),
  atomize_ok_all_upto 0 ts1 ts2 ->
  length ts1 = length ts2 ->
  ts1 = ts2.
Proof.
  induction ts1.
  - destruct ts3; simpl in *; intros; eauto. omega.
  - destruct ts3; simpl in *; intros; try omega.
    f_equal.
    + specialize (H 0); intuition idtac.
      unfold thread_get in H2; simpl in *.
      apply H2. omega.
    + apply IHts1; try omega.
      split; intros; try omega.
      specialize (H (S tid)); intuition idtac.
      apply H3. omega.
Qed.

Instance same_traces_proper {opT opHiT State op_step s} :
  Proper (exec_equiv_ts ==> exec_equiv_ts ==> iff) (@same_traces opT opHiT State op_step s).
Proof.
  unfold same_traces; split; intros.
  - apply H in H2.
    apply H1 in H2. deex.
    apply H0 in H2.
    eauto.
  - apply H in H2.
    apply H1 in H2. deex.
    apply H0 in H2.
    eauto.
Qed.

Instance exec_equiv_to_exec_equiv_opt {opT opHiT T} :
  Proper (@exec_equiv opT opHiT T ==> exec_equiv_opt) (fun p => Some (existT _ T p)).
Proof.
  unfold exec_equiv.
  intros p1 p2 H.
  eauto.
Qed.

Instance exec_equiv_ts_sym {opT opHiT} :
  Symmetric (@exec_equiv_ts opT opHiT).
Proof.
  split; intros.
  apply H; eauto.
  apply H; eauto.
Qed.

Theorem atomize_ok_preserves_trace_0 :
  forall T p1 p2,
  atomize_ok p1 p2 ->
  forall tid T' (p1rest p2rest : T -> proc _ _ T'),
  (forall x, trace_equiv (p1rest x) (p2rest x)) ->
  forall (ts : threads_state) (s : State),
  ts tid = Some (existT _ _ (Bind p1 p1rest)) ->
  same_traces op_step s ts (thread_updS ts tid (Bind p2 p2rest)).
Proof.
  induction 1; intros.
  - etransitivity.
    eapply inc_twice_atomic. eauto.
    etransitivity.
    eapply thread_updS_properTrace. reflexivity. reflexivity.
    eapply trace_equiv_bind_a. apply H.
    reflexivity.
  - replace (ts0) with (thread_updS ts0 tid (x <- Ret x; p1rest x)).
    etransitivity.
    eapply thread_updS_properTrace. reflexivity. reflexivity.
    eapply trace_equiv_bind_a. apply H.
    unfold thread_updS.
    autorewrite with t.
    reflexivity.
    unfold thread_updS.
    rewrite thread_upd_same; eauto.
  - (* rewrite exec_equiv_bind_bind. *)
    eapply same_traces_proper.
    reflexivity.
    eapply thread_updS_proper.
    reflexivity.
    reflexivity.
    eapply exec_equiv_bind_bind.

    etransitivity.

    instantiate (1 := thread_updS ts0 tid (x <- p1a; x <- p1b x; p1rest x)).
    eapply same_traces_proper.
    reflexivity.
    symmetry.
    eapply thread_updS_proper.
    reflexivity.
    reflexivity.
    eapply exec_equiv_bind_bind.

    unfold thread_updS; rewrite thread_upd_same; eauto.
    reflexivity.

    assert ((thread_updS ts0 tid (v <- p2a; Bind (p2b v) p2rest)) =
            (thread_updS (thread_updS ts0 tid (x <- p1a; Bind (p1b x) p1rest)) tid (v <- p2a; Bind (p2b v) p2rest))).
    unfold thread_updS; rewrite thread_upd_upd_eq; eauto.
    rewrite H4.
    eapply IHatomize_ok.
    2: unfold thread_updS; rewrite thread_upd_eq; reflexivity.

    unfold trace_equiv; intros.
    eapply H1.
    eassumption.
    eauto.
Qed.

Theorem atomize_ok_preserves_trace :
  forall tid (ts : threads_state) T p1 p2 op_step (s : State),
  atomize_ok p1 p2 ->
  ts tid = Some (existT _ T p2) ->
  same_traces op_step s
    (thread_upd ts tid (Some (existT _ _ p1))) ts.
Proof.
  unfold same_traces.
  intros.
  edestruct atomize_ok_preserves_trace_0.
  eauto.
Admitted.


Theorem atomize_ok_all_upto_preserves_trace :
  forall n ts1' ts1,
  length ts1 = length ts1' ->
  atomize_ok_all_upto n ts1 ts1' ->
    forall s,
      same_traces op_step s ts1 ts1'.
Proof.
  induction n; intros.
  - erewrite <- atomize_ok_all_upto_0; eauto.
    reflexivity.
  - destruct (lt_dec n (length ts1)).
    + etransitivity.
      instantiate (1 := thread_upd ts1' n (thread_get ts1 n)).
      * eapply IHn.
        admit.
        split; intros.
       -- rewrite thread_upd_ne by omega.
          specialize (H0 tid); intuition eauto.
       -- destruct (tid == n); subst.
          rewrite thread_upd_eq; eauto.
          rewrite thread_upd_ne; eauto.
          specialize (H0 tid); intuition eauto.
          eapply H3. omega.
      * specialize (H0 n); intuition idtac.
        edestruct H1. omega.
       -- intuition idtac. rewrite H3.
          admit.
       -- repeat deex.
          rewrite H0.
          eapply atomize_ok_preserves_trace; eauto.
    + eapply IHn. omega.
      split; intros.
     -- specialize (H0 tid); intuition eauto.
Admitted.

Theorem atomize_ok_all_preserves_trace :
  forall ts1' ts1,
  atomize_ok_all ts1 ts1' ->
    forall s,
      same_traces op_step s ts1 ts1'.
Admitted.


(*
Lemma app_is_thread_upd : forall opT opHiT (ts : @threads_state opT opHiT) p,
  ts ++ [p] = thread_upd ts (length ts) p.
Admitted.

Lemma trace_match_atomize_ok : forall ts1 ts1' tid,
  (forall (s : State) (tr1 : trace opT opHiT),
   exec op_step s ts1 tr1 ->
   exists tr1' : trace opT opHiT,
     exec op_step s ts1' tr1' /\ trace_match_hi tr1 tr1') ->
  forall T (p : proc _ _ T) p',
  atomize_ok p p' ->
  forall T' s tr1 (rx : T -> proc _ _ T'),
  exec op_step s (thread_upd ts1 tid (Some (existT _ _ (Bind p rx)))) tr1 ->
  exists tr1',
    exec op_step s (thread_upd ts1' tid (Some (existT _ _ (Bind p' rx)))) tr1' /\
    trace_match_hi tr1 tr1'.
Proof.
  induction 2; simpl; intros.
  - apply inc_twice_atomic in H0. deex.
    (* something fishy: ts1 needs to change to ts1' underneath.... *)
    
Admitted.

      eapply exec_equiv_bind_ret in H1.
      eapply trace_match_atomize_ok in H1.
      3: eauto.
      repeat deex.

      eexists; split.
      eapply exec_equiv_bind_ret.
      replace (length ts1') with (length ts1) by omega.
      apply H1.

      eauto.
      eapply IHts1'.
      omega.
      admit.
    }

    admit.
    admit.

    admit.
Admitted.
*)

Theorem all_traces_match_1 :
  forall ts1 ts1' ts2,
  atomize_ok_all ts1 ts1' ->
  compile_ok_all_atomic ts1' ts2 ->
  trace_match_threads op_step opHi_step ts1 ts2.
Proof.
  unfold trace_match_threads; intros.
  eapply atomize_ok_all_preserves_trace in H; eauto.
  deex.
  edestruct all_traces_match_0; eauto.
  intuition idtac.
  eexists; split.
  eauto.
  eapply traces_match_trace_match_hi; eauto.
  symmetry; eauto.
Qed.

Theorem make_one_atomic :
  forall T p2 (p1 : proc _ _ T),
  compile_ok p1 p2 ->
    atomize_ok p1 (compile_atomic p2) /\
    compile_ok_atomic (compile_atomic p2) p2.
Proof.
  induction 1; simpl; intros.
  - split. constructor. repeat constructor.
  - split; constructor.
  - intuition idtac.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
    constructor. eauto. intros. specialize (H1 x). intuition eauto.
Qed.

Lemma atomize_ok_cons : forall T (p1 : proc _ _ T) p2 ts1 ts2,
  atomize_ok_all ts1 ts2 ->
  atomize_ok p1 p2 ->
  atomize_ok_all (Some (existT _ _ p1) :: ts1) (Some (existT _ _ p2) :: ts2).
Proof.
  intros.
  intro tid; destruct tid.
  - unfold thread_get; simpl. right. do 3 eexists. eauto.
  - apply H.
Qed.

Lemma atomize_ok_cons_None : forall ts1 ts2,
  atomize_ok_all ts1 ts2 ->
  atomize_ok_all (None :: ts1) (None :: ts2).
Proof.
  intros.
  intro tid; destruct tid.
  - unfold thread_get; simpl. left; eauto.
  - apply H.
Qed.

Lemma compile_ok_atomic_cons : forall T (p1 : proc _ _ T) p2 ts1 ts2,
  compile_ok_all_atomic ts1 ts2 ->
  compile_ok_atomic p1 p2 ->
  compile_ok_all_atomic (Some (existT _ _ p1) :: ts1) (Some (existT _ _ p2) :: ts2).
Proof.
  intros.
  intro tid; destruct tid.
  - unfold thread_get; simpl. right. do 3 eexists. eauto.
  - apply H.
Qed.

Lemma compile_ok_atomic_cons_None : forall ts1 ts2,
  compile_ok_all_atomic ts1 ts2 ->
  compile_ok_all_atomic (None :: ts1) (None :: ts2).
Proof.
  intros.
  intro tid; destruct tid.
  - unfold thread_get; simpl. left; eauto.
  - apply H.
Qed.

Hint Resolve atomize_ok_cons.
Hint Resolve atomize_ok_cons_None.
Hint Resolve compile_ok_atomic_cons.
Hint Resolve compile_ok_atomic_cons_None.

Theorem make_all_atomic :
  forall ts1 ts2,
  compile_ok_all ts1 ts2 ->
  exists ts1',
    atomize_ok_all ts1 ts1' /\
    compile_ok_all_atomic ts1' ts2.
Proof.
  induction ts1; intros.
  - exists nil; split.
    intro tid; left; unfold thread_get; repeat rewrite nth_error_nil; eauto.
    intro tid.
    specialize (H tid); intuition; repeat deex.
    exfalso.
    unfold thread_get in H.
    rewrite nth_error_nil in H. congruence.
  - destruct ts3.
    + exists nil; split.
      2: intro tid; left; unfold thread_get; repeat rewrite nth_error_nil; eauto.
      intro tid.
      specialize (H tid); intuition; repeat deex.
      2: unfold thread_get in H0; rewrite nth_error_nil in H0; congruence.
      left. intuition eauto.
      unfold thread_get; rewrite nth_error_nil; eauto.
    + edestruct IHts1.
      * intro tid. specialize (H (S tid)).
        apply H.
      * intuition.
        destruct o; destruct a.
       -- destruct s.
          destruct s0.
          specialize (H 0) as H'.
            unfold thread_get in H'; simpl in H'. intuition try congruence.
          repeat deex.
          inversion H0; clear H0.
          inversion H3; clear H3.
          subst; repeat sigT_eq'.

          edestruct (make_one_atomic H4).
          exists (Some (existT _ _ (compile_atomic p4)) :: x).
          split; eauto.
       -- specialize (H 0); unfold thread_get in H; simpl in H;
            intuition try congruence.
          repeat deex; intuition congruence.
       -- specialize (H 0); unfold thread_get in H; simpl in H;
            intuition try congruence.
          repeat deex; intuition congruence.
       -- exists (None :: x). eauto.
Qed.

Theorem all_traces_match :
  forall ts1 ts2,
  compile_ok_all ts1 ts2 ->
  trace_match_threads op_step opHi_step ts1 ts2.
Proof.
  intros.
  eapply make_all_atomic in H; deex.
  eapply all_traces_match_1; eauto.
Qed.
