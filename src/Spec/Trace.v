Require Import Relations.Relation_Operators.
Require Import RelationClasses.
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
| Op : forall T (op : opT T), proc T
| Ret : forall T (v : T), proc T
| Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T
| InvokeOpHi : forall T' (op : opHiT T'), proc unit
| ReturnOpHi : forall T' (result : T'), proc unit
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


Inductive thread_state :=
| ThreadRunning
| ThreadCalled
| ThreadReturning : forall T (r : T), thread_state.

Definition threads_state := forall (tid : nat), option (proc unit * thread_state).

Definition thread_upd (ts : threads_state) (tid : nat) (s : proc unit * thread_state) :=
  fun tid' => if tid == tid' then Some s else ts tid'.

Definition thread_del (ts : threads_state) (tid : nat) :=
  fun tid' => if tid == tid' then None else ts tid'.


Inductive atomic_exec : forall T, proc T -> nat -> State -> T -> State -> list event -> Prop :=

| AtomicRet : forall T tid (v : T) s,
  atomic_exec (Ret v) tid s v s nil

| AtomicBind : forall T1 T2 tid (p1 : proc T1) (p2 : T1 -> proc T2)
                      s0 s1 s2 ev1 ev2 (v1 : T1) (v2 : T2),
  atomic_exec p1 tid s0 v1 s1 ev1 ->
  atomic_exec (p2 v1) tid s1 v2 s2 ev2 ->
  atomic_exec (Bind p1 p2) tid s0 v2 s2 (ev1 ++ ev2)

| AtomicOp : forall T tid (v : T) s s' op,
  op_step op tid s v s' ->
  atomic_exec (Op op) tid s v s'
    (InvokeLo tid op :: ReturnLo tid v :: nil)

| AtomicInvokeHi : forall T (op : opHiT T) tid s,
  atomic_exec (InvokeOpHi op) tid s tt s (InvokeHi tid op :: nil)

| AtomicReturnHi : forall T (r : T) tid s,
  atomic_exec (ReturnOpHi r) tid s tt s (ReturnHi tid r :: nil)

| AtomicAtomic : forall T (p : proc T) tid s r s' ev',
  atomic_exec p tid s r s' ev' ->
  atomic_exec (Atomic p) tid s r s' ev'.


Fixpoint prepend (evs : list event) (tr : trace) : trace :=
  match evs with
  | nil => tr
  | e :: evs' =>
    TraceEvent e (prepend evs' tr)
  end.


Inductive exec_tid (tid : nat) : State -> proc unit -> thread_state -> State -> proc unit -> thread_state -> list event -> Prop :=

| ExecTidRet : forall T (v : T) p s,
  exec_tid tid s (Bind (Ret v) p) ThreadRunning
               s (p v) ThreadRunning
               nil

| ExecTidOpCall : forall T p s (op : opT T),
  exec_tid tid s (Bind (Op op) p) ThreadRunning
               s (Bind (Op op) p) ThreadCalled
               [InvokeLo tid op]

| ExecTidOpRun : forall T (v : T) p s s' op,
  op_step op tid s v s' ->
  exec_tid tid s (Bind (Op op) p) ThreadCalled
               s' (p v) (ThreadReturning v)
               nil

| ExecTidOpRet : forall T (v : T) p s,
  exec_tid tid s p (ThreadReturning v)
               s p ThreadRunning
               [ReturnLo tid v]

| ExecTidAtomic : forall T (v : T) p ap s s' evs,
  atomic_exec ap tid s v s' evs ->
  exec_tid tid s (Bind (Atomic ap) p) ThreadRunning
               s' (p v) ThreadRunning
               evs

| ExecTidInvokeHi : forall p s T' (op : opHiT T'),
  exec_tid tid s (Bind (InvokeOpHi op) p) ThreadRunning
               s (p tt) ThreadRunning
               [InvokeHi tid op]

| ExecTidReturnHi : forall p s T' (r : T'),
  exec_tid tid s (Bind (ReturnOpHi r) p) ThreadRunning
               s (p tt) ThreadRunning
               [ReturnHi tid r]

| ExecTidBind : forall T1 (p1 : proc T1) T2 (p2 : T1 -> proc T2) p3 s,
  exec_tid tid s (Bind (Bind p1 p2) p3) ThreadRunning
               s (Bind p1 (fun x => Bind (p2 x) p3)) ThreadRunning
               nil.


Inductive exec : State -> threads_state -> trace -> Prop :=

| ExecOne : forall tid ts trace p ps p' ps' s s' evs,
  ts tid = Some (p, ps) ->
  exec_tid tid s p ps s' p' ps' evs ->
  exec s' (thread_upd ts tid (p', ps')) trace ->
  exec s ts (prepend evs trace)

| ExecDone : forall tid ts trace s,
  ts tid = Some (Ret tt, ThreadRunning) ->
  exec s (thread_del ts tid) trace ->
  exec s ts trace

| ExecEmpty : forall ts s,
  (forall tid, ts tid = None) ->
  exec s ts TraceEmpty.

End Proc.


Arguments Op {opT opHiT T}.
Arguments Ret {opT opHiT T}.
Arguments Bind {opT opHiT T T1}.
Arguments InvokeOpHi {opT opHiT T'}.
Arguments ReturnOpHi {opT opHiT T'}.
Arguments Atomic {opT opHiT T}.

Arguments threads_state {opT opHiT}.


Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).


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


Definition threads_empty {opT opHiT} : @threads_state opT opHiT :=
  fun x => None.

Definition inc_twice_impl :=
  _ <- InvokeOpHi IncTwice;
  _ <- Op Inc;
  i2 <- Op Inc;
  _ <- ReturnOpHi i2;
  Ret i2.

Definition p1 :=
  _ <- inc_twice_impl;
  Ret tt.

Definition ts := thread_upd threads_empty 1 (p1, ThreadRunning).

Lemma thread_upd_eq : forall opT opHiT ts p tid,
  @thread_upd opT opHiT ts tid p tid = Some p.
Proof.
  unfold thread_upd; intros.
  destruct (tid == tid); congruence.
Qed.

Lemma thread_upd_ne : forall opT opHiT ts p tid tid',
  tid <> tid' ->
  @thread_upd opT opHiT ts tid p tid' = ts tid'.
Proof.
  unfold thread_upd; intros.
  destruct (tid == tid'); congruence.
Qed.

Lemma thread_upd_upd_ne : forall opT opHiT ts p p' tid tid',
  tid <> tid' ->
  @thread_upd opT opHiT (@thread_upd opT opHiT ts tid p) tid' p' =
  @thread_upd opT opHiT (@thread_upd opT opHiT ts tid' p') tid p.
Proof.
  unfold thread_upd; intros.
  apply functional_extensionality; intros.
  destruct (tid' == x); destruct (tid == x); congruence.
Qed.

Lemma thread_del_upd_eq : forall opT opHiT ts p tid,
  @thread_del opT opHiT (thread_upd ts tid p) tid =
  @thread_del opT opHiT ts tid.
Proof.
  unfold thread_del, thread_upd; intros.
  apply functional_extensionality; intros.
  destruct (tid == x); congruence.
Qed.

Lemma thread_del_upd_ne : forall opT opHiT ts p tid tid',
  tid <> tid' ->
  @thread_del opT opHiT (@thread_upd opT opHiT ts tid p) tid' =
  @thread_upd opT opHiT (@thread_del opT opHiT ts tid') tid p.
Proof.
  unfold thread_del, thread_upd; intros.
  apply functional_extensionality; intros.
  destruct (tid == x); destruct (tid' == x); congruence.
Qed.

Lemma thread_del_empty : forall opT opHiT tid,
  @thread_del opT opHiT (threads_empty) tid =
  threads_empty.
Proof.
  unfold thread_del, threads_empty; intros.
  apply functional_extensionality; intros.
  destruct (tid == x); congruence.
Qed.

Lemma thread_upd_upd_eq : forall opT opHiT ts tid p1 p2,
  @thread_upd opT opHiT (thread_upd ts tid p1) tid p2 =
  thread_upd ts tid p2.
Proof.
  unfold thread_upd; intros.
  apply functional_extensionality; intros.
  destruct (tid == x); congruence.
Qed.

Hint Rewrite thread_upd_upd_eq : t.
Hint Rewrite thread_del_upd_eq : t.
Hint Rewrite thread_del_empty : t.


Definition init_state : State := fun tid' => 4.

Ltac exec_one tid' :=
  eapply ExecOne with (tid := tid');
    [ rewrite thread_upd_eq; reflexivity | | autorewrite with t ].

Definition ex_trace :
  { t : trace opT opHiT | exec op_step init_state ts t }.
Proof.
  eexists.
  unfold ts.
  unfold init_state.
  exec_one 1.
    eapply ExecTidBind.
  exec_one 1.
    eapply ExecTidInvokeHi.
  exec_one 1.
    eapply ExecTidBind.
  exec_one 1.
    eapply ExecTidOpCall.
  exec_one 1.
    eapply ExecTidOpRun.
    constructor.
  exec_one 1.
    eapply ExecTidOpRet.
  exec_one 1.
    eapply ExecTidBind.
  exec_one 1.
    eapply ExecTidOpCall.
  exec_one 1.
    eapply ExecTidOpRun.
    constructor.
  exec_one 1.
    eapply ExecTidOpRet.
  exec_one 1.
    eapply ExecTidBind.
  exec_one 1.
    eapply ExecTidReturnHi.
  exec_one 1.
    eapply ExecTidRet.
  eapply ExecDone with (tid := 1).
    rewrite thread_upd_eq.
    reflexivity.
    autorewrite with t.
  eapply ExecEmpty.
    unfold threads_empty; congruence.
Defined.

Eval compute in (proj1_sig ex_trace).


Definition p2 : proc opHiT opHi2T _ :=
  _ <- Op IncTwice;
  Ret tt.

Definition ts2 := thread_upd threads_empty 1 (p2, ThreadRunning).

Definition ex_trace2 :
  { t : trace opHiT opHi2T | exec opHi_step init_state ts2 t }.
Proof.
  eexists.
  unfold ts2.
  unfold init_state.
  exec_one 1.
    eapply ExecTidOpCall.
  exec_one 1.
    eapply ExecTidOpRun.
    constructor.
  exec_one 1.
    eapply ExecTidOpRet.
  eapply ExecDone with (tid := 1).
    rewrite thread_upd_eq.
    reflexivity.
    autorewrite with t.
  eapply ExecEmpty.
    unfold threads_empty; congruence.
Defined.

Eval compute in (proj1_sig ex_trace2).


Check InvokeLo.

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
  (exists p1 p2,
    ts1 tid = Some (p1, ThreadRunning) /\ ts2 tid = Some (p2, ThreadRunning) /\ compile_ok p1 p2).

Theorem ex_ts_compile_ok : threads_compile_ok ts ts2.
Proof.
  unfold threads_compile_ok, ts, ts2, thread_upd, threads_empty; intros.
  destruct (1 == tid); intuition eauto.
Qed.

Lemma thread_upd_inv : forall opT opHiT ts tid1 p tid2 p',
  @thread_upd opT opHiT ts tid1 p tid2 = Some p' ->
  tid1 = tid2 /\ p = p' \/
  tid1 <> tid2 /\ ts tid2 = Some p'.
Proof.
  unfold thread_upd; intros.
  destruct (tid1 == tid2); intuition eauto.
  inversion H; eauto.
Qed.

Lemma thread_empty_inv : forall opT opHiT tid p',
  @threads_empty opT opHiT tid = Some p' ->
  False.
Proof.
  unfold threads_empty; intros; congruence.
Qed.

Lemma thread_upd_not_empty : forall opT opHiT tid ts p,
  (forall tid', @thread_upd opT opHiT ts tid p tid' = None) -> False.
Proof.
  unfold thread_upd; intros.
  specialize (H tid).
  destruct (tid == tid); congruence.
Qed.


Ltac thread_inv :=
  match goal with
  | H : thread_upd _ _ _ _ = Some _ |- _ =>
    eapply thread_upd_inv in H; destruct H; (intuition idtac); subst
  | H : threads_empty _ = Some _ |- _ =>
    eapply thread_empty_inv in H; exfalso; apply H
  | H : (_, _) = (_, _) |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : _ = Bind _ _ |- _ =>
    solve [ inversion H ]
  | H : _ = Ret _ _ _|- _ =>
    solve [ inversion H ]
  | H : forall _, thread_upd _ _ _ _ = None |- _ =>
    solve [ eapply thread_upd_not_empty in H; exfalso; eauto ]
  end.

Ltac bind_inv :=
  match goal with
  | H : _ = Bind _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.

Ltac exec_inv :=
  match goal with
  | H : exec _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end;
  autorewrite with t in *.

Ltac exec_tid_inv :=
  match goal with
  | H : exec_tid _ _ _ _ _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end;
  autorewrite with t in *.


Ltac empty_inv :=
  try solve [ exfalso; eapply thread_empty_inv; eauto ].

Ltac step_inv :=
  match goal with
  | H : op_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : opHi_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
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
    try ( exec_tid_inv; repeat thread_inv ) ).
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


Definition same_traces {opLo opHi State} op_step (s : State) (ts1 ts2 : @threads_state opLo opHi) :=
  forall tr,
    exec op_step s ts1 tr ->
    exists tr', exec op_step s ts2 tr' /\
      trace_match_hi tr tr'.

Theorem trace_match_hi_ok : forall opLo opHi (tr1 tr2 : trace opLo opHi),
  trace_match_hi tr1 tr2 ->
  forall opHi2 (trHi : trace opHi opHi2),
    traces_match tr1 trHi -> traces_match tr2 trHi.
Proof.
Admitted.


Definition p1_a :=
  _ <- Atomic inc_twice_impl;
  Ret tt.


Definition ts_a := thread_upd threads_empty 1 (p1_a, ThreadRunning).


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
    try ( exec_tid_inv; repeat thread_inv ) ).

  repeat match goal with
  | H : ?a = ?a |- _ => clear H
  end.

  repeat step_inv.
  unfold p1_a.

  eexists; split.

  exec_one 1.
  eapply ExecTidAtomic.
    unfold inc_twice_impl.
    eapply AtomicBind.
      eapply AtomicInvokeHi.
    eapply AtomicBind.
      eapply AtomicOp.
      constructor.
    eapply AtomicBind.
      eapply AtomicOp.
      constructor.
    eapply AtomicBind.
      eapply AtomicReturnHi.
    eapply AtomicRet.
  eapply ExecDone with (tid := 1).
    rewrite thread_upd_eq.
    reflexivity.
    autorewrite with t.
  eapply ExecEmpty.
    unfold threads_empty; congruence.

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


Lemma can_ignore_return :
  forall opT opHiT T State
         (p : proc opT opHiT unit) op_step ts tid (s : State) (v : T),
  same_traces op_step s
    (thread_upd ts tid (p, ThreadReturning v))
    (thread_upd ts tid (p, ThreadRunning)).
Proof.
  unfold same_traces; intros.
  remember (thread_upd ts0 tid (p, ThreadReturning v)).
  generalize dependent ts0.
  induction H; intros; subst.

  - destruct (tid == tid0); subst.
    + rewrite thread_upd_eq in H.
      inversion H; clear H; subst.
      exec_tid_inv.

      eexists; intuition eauto.
      simpl; eauto.

    + rewrite thread_upd_ne in * by assumption.
      edestruct IHexec; intuition idtac.
      shelve.

      eexists; split.

      eapply ExecOne with (tid := tid0).
      rewrite thread_upd_ne by assumption.
      eauto.

      eauto.

      rewrite thread_upd_upd_ne by assumption.
      eauto.
      eauto.

      Unshelve.
      all: try rewrite thread_upd_upd_ne by assumption.
      all: try reflexivity.

  - destruct (tid == tid0).
    + subst.
      rewrite thread_upd_eq in H.
      congruence.

    + rewrite thread_upd_ne in * by assumption.
      edestruct IHexec; intuition idtac.
      shelve.

      eexists; split.

      eapply ExecDone with (tid := tid0).
      rewrite thread_upd_ne by assumption.
      eauto.

      rewrite thread_del_upd_ne by assumption.
      eauto.
      eauto.

      Unshelve.
      all: try rewrite thread_del_upd_ne by assumption.
      all: try reflexivity.

  - specialize (H tid).
    rewrite thread_upd_eq in H.
    congruence.
Qed.


Theorem atomic_start :
  forall opT opHiT T State
         op (p : T -> proc opT opHiT unit) ps op_step ts tid (s : State),
  same_traces op_step s
    (thread_upd ts tid (Bind (Op op) p, ps))
    (thread_upd ts tid (Bind (Atomic (Op op)) p, ThreadRunning)).
Proof.
  unfold same_traces; intros.
  remember (thread_upd ts0 tid (Bind (@Op opT0 opHiT0 T op) p, ps)) as ts.
  generalize dependent ts0.
  generalize dependent ps.
  induction H; intros; subst.

  - destruct (tid == tid0).
    + subst.
      rewrite thread_upd_eq in H.

      inversion H; clear H; subst.

      destruct ps; exec_tid_inv.

      * edestruct IHexec; intuition idtac.

        eexists; split.
        eauto.

        simpl; intros.
        eauto.

      * edestruct can_ignore_return; eauto; intuition idtac.

        eexists; split.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_eq. reflexivity.
          eapply ExecTidAtomic.
          constructor.
          eauto.
          autorewrite with t.

        eauto.

        simpl; intros. eauto.

      * edestruct IHexec; intuition idtac.

        eexists; split.
        eauto.
        simpl; eauto.

    + rewrite thread_upd_ne in * by assumption.
      edestruct IHexec; intuition idtac.
      shelve.

      eexists; split.

      eapply ExecOne with (tid := tid0).
      rewrite thread_upd_ne by assumption.
      eauto.

      eauto.

      rewrite thread_upd_upd_ne by assumption.
      eauto.
      eauto.

      Unshelve.
      all: try rewrite thread_upd_upd_ne by assumption.
      all: try reflexivity.

  - destruct (tid == tid0).
    + subst.
      rewrite thread_upd_eq in H.
      congruence.

    + rewrite thread_upd_ne in * by assumption.
      edestruct IHexec; intuition idtac.
      shelve.

      eexists; split.

      eapply ExecDone with (tid := tid0).
      rewrite thread_upd_ne by assumption.
      eauto.

      rewrite thread_del_upd_ne by assumption.
      eauto.
      eauto.

      Unshelve.
      all: try rewrite thread_del_upd_ne by assumption.
      all: try reflexivity.

  - specialize (H tid).
    rewrite thread_upd_eq in H.
    congruence.
Qed.


Lemma exec_tid_p'_eq : forall opT opHiT State op_step tid s p ps s' p' p'' ps' evs,
  @exec_tid opT opHiT State op_step tid s p ps s' p' ps' evs ->
  p' = p'' ->
  exec_tid op_step tid s p ps s' p'' ps' evs.
Proof.
  intros; subst; eauto.
Qed.


Hint Constructors exec_tid.
Hint Constructors atomic_exec.


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

Lemma inc_commutes_exec_tid : forall tid0 tid1 s p ps s' p' ps' evs,
  tid0 <> tid1 ->
  @exec_tid opT opHiT State op_step tid1 s p ps s' p' ps' evs ->
  @exec_tid opT opHiT State op_step tid1 (fun tid => if tid == tid0 then s tid + 1 else s tid) p ps
                        (fun tid => if tid == tid0 then s' tid + 1 else s' tid) p' ps' evs.
Proof.
  intros.
  destruct H0; simpl; eauto.
  - constructor.
    eapply inc_commutes_op_step; eauto.
  - constructor.
    induction H0; eauto.
    constructor.
    eapply inc_commutes_op_step; eauto.
Qed.

Lemma inc_commutes_exec_tid' : forall tid0 s p ps s' p' ps' evs,
  @exec_tid opT opHiT State op_step tid0 s p ps s' p' ps' evs ->
  forall tid1, tid0 <> tid1 ->
  s tid1 = s' tid1.
Proof.
  intros.
  destruct H; eauto.
  - eapply inc_commutes_op_step'; eauto.
  - induction H; eauto.
    + eapply eq_trans.
      apply IHatomic_exec1; eauto.
      apply IHatomic_exec2; eauto.
    + eapply inc_commutes_op_step'; eauto.
Qed.


Theorem inc_commutes :
  forall TA (ap : proc _ _ TA) (p : TA -> _ -> proc opT opHiT unit) ts tid (s : State) tr tidps tidps' ts' s',
  (tidps = (r <- Atomic ap; Bind (Op Inc) (p r), ThreadRunning) /\
   tidps' = (x <- Atomic (r <- ap; r' <- Op Inc; Ret (r, r'));
             p (fst x) (snd x), ThreadRunning) /\
   s' = s \/
   exists ps r,
   tidps = (Bind (Op Inc) (p r), ps) /\
   tidps' = (p r (s tid + 1), ThreadRunning) /\
   (ps = ThreadRunning \/ ps = ThreadCalled) /\
   s' = (fun tid' => if tid' == tid then s tid' + 1 else s tid')
  ) ->
  ts' = thread_upd ts tid tidps ->
  exec op_step s ts' tr ->
  exists tr',
    exec op_step s' (thread_upd ts tid tidps') tr' /\
    trace_match_hi tr tr'.
Proof.
  intros.
  generalize dependent ts0.
  generalize dependent tidps'.
  generalize dependent tidps.
  generalize dependent s'.
  induction H1; intros; subst.

  - destruct (tid == tid0).
    + subst.
      rewrite thread_upd_eq in H.
      inversion H; clear H; subst.

      intuition idtac; subst.

      * inversion H2; clear H2; subst.
        exec_tid_inv.

        edestruct IHexec.
        2: reflexivity.
        right. do 2 eexists.
          split. reflexivity.
          split. reflexivity.
          split. eauto.
          reflexivity.
        intuition idtac.

        eexists; split.

        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_eq. reflexivity.
          2: autorewrite with t; eassumption.

          eapply exec_tid_p'_eq.
          eapply ExecTidAtomic.
          econstructor. eauto.
          econstructor. constructor.
            (* XXX specific to Inc *)
            constructor.
          constructor.

          simpl.
          reflexivity.

          simpl.
          rewrite prepend_app; simpl.
          eauto.

      * repeat deex.
        inversion H; clear H; subst.
        autorewrite with t in *.
        exec_tid_inv; intuition idtac; try congruence.

       -- edestruct IHexec.
          2: reflexivity.
          right. do 2 eexists.
            split. reflexivity.
            split. reflexivity.
            split. eauto.
            reflexivity.
          intuition idtac.

          eexists; split.
          eauto.
          simpl; eauto.

       -- edestruct can_ignore_return; eauto; intuition idtac.

          step_inv.

          eexists; split.
          eauto.
          simpl; eauto.

    + rewrite thread_upd_ne in * by assumption.

      intuition idtac; subst.
      * edestruct IHexec.
          shelve.
          shelve.
        intuition idtac.

        eexists; split.

        eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne by assumption.
        eauto.
        eauto.

        rewrite thread_upd_upd_ne by assumption.
        eauto.
        eauto.

        Unshelve.
        3: rewrite thread_upd_upd_ne by assumption; reflexivity.
        eauto.

      * edestruct IHexec.
          shelve.
          shelve.
        intuition idtac.

        repeat deex.

        eexists; split.

        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne by assumption.
          eauto.

        eapply inc_commutes_exec_tid; eauto.
        rewrite thread_upd_upd_ne by assumption.
        eauto.
        eauto.

        Unshelve.
        3: rewrite thread_upd_upd_ne by assumption; reflexivity.
        right. repeat deex.
        do 2 eexists.
          split. reflexivity.
          split. rewrite (inc_commutes_exec_tid' H0) by auto.
            reflexivity.
          eauto.

  - destruct (tid == tid0).
    + subst.
      rewrite thread_upd_eq in H.
      intuition idtac; repeat deex; congruence.

    + rewrite thread_upd_ne in * by assumption.
      edestruct IHexec.
        shelve.
        shelve.

      eexists; split.

      eapply ExecDone with (tid := tid0).
      rewrite thread_upd_ne by assumption.
      eauto.
      rewrite thread_del_upd_ne.
        intuition eauto.
        intuition eauto.
        intuition eauto.

      Unshelve.
        3: rewrite thread_del_upd_ne by assumption; eauto.
        eauto.

  - specialize (H tid).
    rewrite thread_upd_eq in H.
    congruence.
Qed.

Theorem inc_commutes_final :
  forall TA (ap : proc _ _ TA) (p : TA -> _ -> proc opT opHiT unit) ts tid (s : State),
  same_traces op_step s
    (thread_upd ts tid (r <- Atomic ap;
                        Bind (Op Inc) (p r), ThreadRunning))
    (thread_upd ts tid (x <- Atomic (r <- ap; r' <- Op Inc; Ret (r, r'));
                        p (fst x) (snd x), ThreadRunning)).
Proof.
  unfold same_traces; intros.
  eapply inc_commutes; eauto.
Qed.


Definition inc_twice_impl_atomic :=
  _ <- InvokeOpHi IncTwice;
  i12 <- Atomic (i1 <- Op Inc; i2 <- Op Inc; Ret (i1, i2));
  _ <- ReturnOpHi (snd i12);
  Ret (snd i12).


Definition trace_equiv {T} (p1 p2 : proc opT opHiT T) :=
  forall p ts tid s,
  same_traces op_step s
    (thread_upd ts tid (r <- p1; p r, ThreadRunning))
    (thread_upd ts tid (r <- p2; p r, ThreadRunning)).


Require Import RelationClasses.
Require Import Morphisms.

Instance trace_match_hi_preorder {opLoT opHiT} :
  PreOrder (@trace_match_hi opLoT opHiT).
Proof.
  split.
  - intro t.
    eapply trace_match_hi_refl.
  - intros t1 t2 t3.
    eapply trace_match_hi_trans.
Qed.

Instance trace_equiv_preorder {T} :
  PreOrder (@trace_equiv T).
Proof.
  split.
  - intro p.
    unfold trace_equiv, same_traces; intros.
    eexists; intuition eauto.
  - intros p1 p2 p3.
    intros.
    unfold trace_equiv, same_traces; intros.
    edestruct H; eauto; intuition idtac.
    edestruct H0; eauto; intuition idtac.
    eexists; intuition eauto.
    eapply trace_match_hi_trans; eauto.
Qed.


Instance trace_equiv_proper {T} : Proper (Basics.flip trace_equiv ==> trace_equiv ==> Basics.impl) (@trace_equiv T).
Proof.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  unfold trace_equiv, same_traces.
  intros.
  edestruct H21; eauto; intuition idtac.
  edestruct H; eauto; intuition idtac.
  edestruct H34; eauto; intuition idtac.
  eexists; intuition eauto.
  eapply trace_match_hi_trans; eauto.
  eapply trace_match_hi_trans; eauto.
Qed.


Instance trace_equiv_proper_flip {T} : Proper (trace_equiv ==> Basics.flip trace_equiv ==> Basics.flip Basics.impl) (@trace_equiv T).
Proof.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  unfold trace_equiv, same_traces.
  intros.
  edestruct H21; eauto; intuition idtac.
  edestruct H; eauto; intuition idtac.
  edestruct H34; eauto; intuition idtac.
  eexists; intuition eauto.
  eapply trace_match_hi_trans; eauto.
  eapply trace_match_hi_trans; eauto.
Qed.


Theorem trace_equiv_op : forall T (op : opT T),
  trace_equiv (Op op) (Atomic (Op op)).
Proof.
  unfold trace_equiv; intros.
  eapply atomic_start.
Qed.


Definition exec_equiv {opT opHiT T} (p1 p2 : proc opT opHiT T) :=
  forall State op_step (s : State) ts tid tr px,
    exec op_step s (thread_upd ts tid (Bind p1 px, ThreadRunning)) tr <->
    exec op_step s (thread_upd ts tid (Bind p2 px, ThreadRunning)) tr.

Theorem monad_left_id : forall opT opHiT T T' (v : T) (p : T -> proc opT opHiT T'),
  exec_equiv (Bind (Ret v) p) (p v).
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
      remember (thread_upd ts tid p); generalize dependent ts;
        induction H; intros; subst
    end.

    + destruct (tid == tid0); subst.
      * rewrite thread_upd_eq in H; inversion H; clear H; subst.
        exec_tid_inv.

  - eapply exec_trace_eq.
      exec_one tid.
      constructor.
      exec_one tid.
      constructor.
      eauto.
    reflexivity.
Qed.


Theorem trace_equiv_bind : forall T1 T2 (p1 p1' : proc _ _ T1) (p2 p2' : T1 -> proc _ _ T2),
  trace_equiv p1 p1' ->
  (forall x, trace_equiv (p2 x) (p2' x)) ->
  trace_equiv (Bind p1 p2) (Bind p1' p2').
Proof.
Admitted.


Theorem trace_equiv_bind_swap : forall T1 T2 T3 (p1 : proc _ _ T1) (p2 : T1 -> proc _ _ T2) (p3 : T1 -> T2 -> proc _ _ T3),
  trace_equiv (Bind p1 (fun x => Bind (p2 x) (p3 x)))
              (Bind (Bind p1 (fun x => Bind (p2 x) (fun y => Ret (x, y))))
                    (fun p => p3 (fst p) (snd p))).
Proof.
Admitted.


Theorem trace_equiv_inc_commutes : forall T (ap : proc opT opHiT T),
  trace_equiv (r <- Atomic ap; i <- Op Inc; Ret (r, i))
              (Atomic (r <- ap; i <- Op Inc; Ret (r, i))).
Proof.
Admitted.


Theorem inc_twice_atomic :
  trace_equiv inc_twice_impl inc_twice_impl_atomic.
Proof.
  unfold inc_twice_impl, inc_twice_impl_atomic.

  eapply trace_equiv_bind.
  reflexivity.
  intros.

  etransitivity.
  eapply trace_equiv_bind.
  eapply trace_equiv_op.

  intros.
  match goal with
  | |- trace_equiv ?p1 _ =>
    instantiate (1 := fun x => p1)
  end.
  reflexivity.

  etransitivity.
  eapply trace_equiv_bind_swap.

  simpl.
  etransitivity.
  eapply trace_equiv_bind.
  apply trace_equiv_inc_commutes.

  intros.
  match goal with
  | |- trace_equiv ?p1 (?p2 ?x) => 
    match eval pattern x in p1 with
    | ?f x =>
      instantiate (1 := f)
    end
  end.
  reflexivity.

  reflexivity.
Qed.


Theorem all_single_thread_traces_match :
  forall s tr1 T (p1 : proc opT opHiT T) (p2 : proc opHiT opHi2T T) (p1rest : T -> proc opT opHiT unit) (p2rest : T -> proc opHiT opHi2T unit),
  (forall x,
    exec op_step s
      (thread_upd threads_empty 1 (p1rest x, ThreadRunning)) tr1 ->
    exists tr2,
      exec opHi_step s (thread_upd threads_empty 1 (p2rest x, ThreadRunning)) tr2 /\
        traces_match tr1 tr2) ->
  compile_ok p1 p2 ->
  exec op_step s (thread_upd threads_empty 1 (Bind p1 p1rest, ThreadRunning)) tr1 ->
  exists tr2,
    exec opHi_step s (thread_upd threads_empty 1 (Bind p2 p2rest, ThreadRunning)) tr2 /\
    traces_match tr1 tr2.
Proof.
  intros.
  induction H0.

  - admit.

  - exec_inv; repeat thread_inv; autorewrite with t in *.
    exec_tid_inv.
    edestruct H; eauto.
    eexists; intuition eauto.

    eapply exec_trace_eq.
      exec_one 1.
      constructor.
      eauto.
      reflexivity.

  - edestruct IHcompile_ok.
    

 1.
  - 

  induction H0.
  - intros.
    inversion H; clear H; subst; repeat sigT_eq.
    unfold inc_twice_impl in H1.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    autorewrite with t in *.

    eexists.
    split.

    eapply ExecOpCall with (tid := 1).
      rewrite thread_upd_eq.
      reflexivity.
      autorewrite with t.
    eapply ExecOp with (tid := 1).
      rewrite thread_upd_eq.
      reflexivity.
      constructor.
      autorewrite with t.
    eapply ExecOpRet with (tid := 1).
      rewrite thread_upd_eq.
      reflexivity.
      autorewrite with t.

    admit.

    constructor.
    constructor.
    constructor.
    constructor.
    constructor.
    repeat step_inv.
    replace (s + 1 + 1) with (s + 2) by omega.
    constructor.

    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    exec_inv; repeat thread_inv.
    repeat ( exec_inv; repeat thread_inv ).
    

  induction H.
  - admit.
  - admit.
  - 

Admitted.

Theorem all_single_thread_traces_match :
  forall s tr1 tr2 p1 p2,
  compile_ok p1 p2 ->
  exec op_step s (thread_upd threads_empty 1 p1) tr1 ->
  exec opHi_step s (thread_upd threads_empty 1 p2) tr2 ->
  traces_match tr1 tr2.
Proof.
  intros.
  eapply all_single_thread_traces_match'; eauto.
  eapply helper1; eauto.
  eapply helper1; eauto.
Qed.
