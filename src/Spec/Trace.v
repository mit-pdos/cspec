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

Definition thread_upd (ts : threads_state) (tid : nat) (s : option (proc unit * thread_state)) :=
  fun tid' => if tid == tid' then s else ts tid'.


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


Inductive exec_tid : forall T (tid : nat),
  State -> proc T -> thread_state ->
  State -> T + proc T -> thread_state -> list event -> Prop :=

| ExecTidRet : forall tid T (v : T) s,
  exec_tid tid s (Ret v) ThreadRunning
               s (inl v) ThreadRunning
               nil

| ExecTidOpCall : forall tid T s (op : opT T),
  exec_tid tid s (Op op) ThreadRunning
               s (inr (Op op)) ThreadCalled
               [InvokeLo tid op]

| ExecTidOpRun : forall tid T (v : T) s s' op,
  op_step op tid s v s' ->
  exec_tid tid s (Op op) ThreadCalled
               s' (inl v) (ThreadReturning v)
               nil

| ExecTidOpRet : forall tid T (v : T) T' (p : proc T') s,
  exec_tid tid s p (ThreadReturning v)
               s (inr p) ThreadRunning
               [ReturnLo tid v]

| ExecTidAtomic : forall tid T (v : T) ap s s' evs,
  atomic_exec ap tid s v s' evs ->
  exec_tid tid s (Atomic ap) ThreadRunning
               s' (inl v) ThreadRunning
               evs

| ExecTidInvokeHi : forall tid s T' (op : opHiT T'),
  exec_tid tid s (InvokeOpHi op) ThreadRunning
               s (inl tt) ThreadRunning
               [InvokeHi tid op]

| ExecTidReturnHi : forall tid s T' (r : T'),
  exec_tid tid s (ReturnOpHi r) ThreadRunning
               s (inl tt) ThreadRunning
               [ReturnHi tid r]

| ExecTidBind : forall tid T1 (p1 : proc T1) T2 (p2 : T1 -> proc T2) ts ts' s s' result evs,
  ts = ThreadRunning \/ ts = ThreadCalled ->
  exec_tid tid s p1 ts
               s' result ts' evs ->
  exec_tid tid s (Bind p1 p2) ts
               s' (inr
                   match result with
                   | inl r => p2 r
                   | inr p1' => Bind p1' p2
                   end
                  ) ts' evs.

Inductive exec : State -> threads_state -> trace -> Prop :=

| ExecOne : forall tid ts trace p ps s s' ps' evs result,
  ts tid = Some (p, ps) ->
  exec_tid tid s p ps s' result ps' evs ->
  exec s' (thread_upd ts tid
            match result with
            | inl _ => None
            | inr p' => Some (p', ps')
            end) trace ->
  exec s ts (prepend evs trace)

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

Definition ts := thread_upd threads_empty 1 (Some (p1, ThreadRunning)).

Lemma thread_upd_eq : forall opT opHiT ts p tid,
  @thread_upd opT opHiT ts tid p tid = p.
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

Lemma thread_upd_upd_eq : forall opT opHiT ts tid p1 p2,
  @thread_upd opT opHiT (thread_upd ts tid p1) tid p2 =
  thread_upd ts tid p2.
Proof.
  unfold thread_upd; intros.
  apply functional_extensionality; intros.
  destruct (tid == x); congruence.
Qed.

Lemma thread_upd_None_empty : forall opT opHiT tid,
  @thread_upd opT opHiT (threads_empty) tid None =
  threads_empty.
Proof.
  unfold thread_upd, threads_empty; intros.
  apply functional_extensionality; intros.
  destruct (tid == x); congruence.
Qed.

Hint Rewrite thread_upd_upd_eq : t.
Hint Rewrite thread_upd_None_empty : t.


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
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    constructor.
    simpl; autorewrite with t.
  exec_one 1.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    constructor.
    simpl; autorewrite with t.
  exec_one 1.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
  eapply ExecEmpty.
    unfold threads_empty; congruence.
Defined.

Eval compute in (proj1_sig ex_trace).


Definition p2 : proc opHiT opHi2T _ :=
  _ <- Op IncTwice;
  Ret tt.

Definition ts2 := thread_upd threads_empty 1 (Some (p2, ThreadRunning)).

Definition ex_trace2 :
  { t : trace opHiT opHi2T | exec opHi_step init_state ts2 t }.
Proof.
  eexists.
  unfold ts2.
  unfold init_state.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    constructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
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
  @thread_upd opT opHiT ts tid1 (Some p) tid2 = Some p' ->
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
  (forall tid', @thread_upd opT opHiT ts tid (Some p) tid' = None) -> False.
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


Definition same_traces {opLo opHi State} op_step (s : State) (ts1 ts2 : @threads_state opLo opHi) :=
  forall tr,
    exec op_step s ts1 tr ->
    exists tr', exec op_step s ts2 tr' /\
      trace_match_hi tr tr'.


Definition p1_a :=
  _ <- Atomic inc_twice_impl;
  Ret tt.


Definition ts_a := thread_upd threads_empty 1 (Some (p1_a, ThreadRunning)).


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
      eapply AtomicOp.
      constructor.
    eapply AtomicBind.
      eapply AtomicOp.
      constructor.
    eapply AtomicBind.
      eapply AtomicReturnHi.
    eapply AtomicRet.
    simpl; autorewrite with t.
  exec_one 1.
    repeat eapply ExecTidBind; eauto.
    econstructor.
    simpl; autorewrite with t.
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
    (thread_upd ts tid (Some (p, ThreadReturning v)))
    (thread_upd ts tid (Some (p, ThreadRunning))).
Proof.
  unfold same_traces; intros.
  remember (thread_upd ts0 tid (Some (p, ThreadReturning v))).
  generalize dependent ts0.
  induction H; intros; subst.

  - destruct (tid == tid0); subst.
    + rewrite thread_upd_eq in H.
      inversion H; clear H; subst.
      exec_tid_inv.
      2: intuition congruence.

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

  - specialize (H tid).
    rewrite thread_upd_eq in H.
    congruence.
Qed.


Theorem atomic_start :
  forall opT opHiT T State
         op (p : T -> proc opT opHiT unit) ps op_step ts tid (s : State),
  same_traces op_step s
    (thread_upd ts tid (Some (Bind (Op op) p, ps)))
    (thread_upd ts tid (Some (Bind (Atomic (Op op)) p, ThreadRunning))).
Proof.
  unfold same_traces; intros.
  remember (thread_upd ts0 tid (Some (Bind (@Op opT0 opHiT0 T op) p, ps))) as ts.
  generalize dependent ts0.
  generalize dependent ps.
  induction H; intros; subst.

  - destruct (tid == tid0).
    + subst.
      rewrite thread_upd_eq in H.

      inversion H; clear H; subst.

      destruct ps; repeat exec_tid_inv; intuition try congruence.

      * edestruct IHexec; intuition idtac.

        eexists; split.
        eauto.

        simpl; intros.
        eauto.

      * edestruct can_ignore_return; eauto; intuition idtac.

        eexists; split.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_eq. reflexivity.
          eapply ExecTidBind; eauto.
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

  - specialize (H tid).
    rewrite thread_upd_eq in H.
    congruence.
Qed.


Lemma exec_tid_p'_eq : forall opT opHiT State op_step T tid s p ps s' result' result'' ps' evs,
  @exec_tid opT opHiT State op_step T tid s p ps s' result' ps' evs ->
  result' = result'' ->
  exec_tid op_step tid s p ps s' result'' ps' evs.
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

Lemma inc_commutes_exec_tid : forall tid0 tid1 T s p ps s' result' ps' evs,
  tid0 <> tid1 ->
  @exec_tid opT opHiT State op_step T tid1 s p ps s' result' ps' evs ->
  @exec_tid opT opHiT State op_step T tid1 (fun tid => if tid == tid0 then s tid + 1 else s tid) p ps
                        (fun tid => if tid == tid0 then s' tid + 1 else s' tid) result' ps' evs.
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

Lemma inc_commutes_exec_tid' : forall T tid0 s p ps s' result' ps' evs,
  @exec_tid opT opHiT State op_step T tid0 s p ps s' result' ps' evs ->
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
  ts' = thread_upd ts tid (Some tidps) ->
  exec op_step s ts' tr ->
  exists tr',
    exec op_step s' (thread_upd ts tid (Some tidps')) tr' /\
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
        repeat exec_tid_inv; try congruence.

        edestruct IHexec.
        2: reflexivity.
        right. do 2 eexists.
          split. reflexivity.
          split. reflexivity.
          split. eauto.
          reflexivity.
        intuition idtac; try congruence.

        eexists; split.

        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_eq. reflexivity.
          eapply ExecTidBind; eauto.
          eapply ExecTidAtomic.
          econstructor. eauto.
          econstructor. constructor.
            (* XXX specific to Inc *)
            constructor.
          constructor.

          simpl. autorewrite with t; eassumption.

        simpl. rewrite prepend_app. simpl. eauto.

      * repeat deex.
        inversion H; clear H; subst.
        autorewrite with t in *.
        repeat exec_tid_inv; intuition idtac; try congruence.

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

  - specialize (H tid).
    rewrite thread_upd_eq in H.
    congruence.
Qed.

Theorem inc_commutes_final :
  forall TA (ap : proc _ _ TA) (p : TA -> _ -> proc opT opHiT unit) ts tid (s : State),
  same_traces op_step s
    (thread_upd ts tid (Some (r <- Atomic ap;
                              Bind (Op Inc) (p r), ThreadRunning)))
    (thread_upd ts tid (Some (x <- Atomic (r <- ap; r' <- Op Inc; Ret (r, r'));
                              p (fst x) (snd x), ThreadRunning))).
Proof.
  unfold same_traces; intros.
  eapply inc_commutes; eauto.
Qed.


Definition inc_twice_impl_atomic :=
  _ <- InvokeOpHi IncTwice;
  i12 <- Atomic (i1 <- Op Inc; i2 <- Op Inc; Ret (i1, i2));
  _ <- ReturnOpHi (snd i12);
  Ret (snd i12).


Definition trace_equiv (p1 p2 : proc opT opHiT unit) :=
  forall ts tid s,
  same_traces op_step s
    (thread_upd ts tid (Some (p1, ThreadRunning)))
    (thread_upd ts tid (Some (p2, ThreadRunning))).


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

Instance trace_equiv_preorder :
  PreOrder trace_equiv.
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


Instance trace_equiv_proper : Proper (Basics.flip trace_equiv ==> trace_equiv ==> Basics.impl) trace_equiv.
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


Instance trace_equiv_proper_flip : Proper (trace_equiv ==> Basics.flip trace_equiv ==> Basics.flip Basics.impl) trace_equiv.
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


Theorem trace_equiv_op : forall T (op : opT T) (p : T -> proc _ _ unit),
  trace_equiv (Bind (Op op) p) (Bind (Atomic (Op op)) p).
Proof.
  unfold trace_equiv; intros.
  eapply atomic_start.
Qed.


Definition exec_equiv {opT opHiT} (p1 p2 : proc opT opHiT unit) :=
  forall State op_step (s : State) ts tid tr ps,
    exec op_step s (thread_upd ts tid (Some (p1, ps))) tr <->
    exec op_step s (thread_upd ts tid (Some (p2, ps))) tr.

Instance exec_equiv_preorder {opLoT opHiT} :
  PreOrder (@exec_equiv opLoT opHiT).
Proof.
  split.
  - intro t.
    unfold exec_equiv; split; eauto.
  - intros t1 t2 t3.
    unfold exec_equiv; split; intros.
    + eapply H0. eapply H. eauto.
    + eapply H. eapply H0. eauto.
Qed.


(*
Definition exec_tid_local {opT opHiT T} (p1 p2 : proc opT opHiT T) :=
  forall State op_step (s : State) tid,
    @exec_tid opT opHiT State op_step T tid s p1 ThreadRunning s (inr p2) ThreadRunning nil /\
    (forall s' result' ts' evs,
     @exec_tid opT opHiT State op_step T tid s p1 ThreadRunning s' result' ts' evs ->
     s' = s /\
     result' = inr p2 /\
     ts' = ThreadRunning /\
     evs = nil).

Theorem exec_tid_local_bind_ret : forall opT opHiT T (p : T -> proc opT opHiT unit) v,
  exec_tid_local (Bind (Ret v) p) (p v).
Proof.
  unfold exec_tid_local; split; intros.
  - pose proof ExecTidRet.
    eapply ExecTidBind in H; eauto.
  - repeat exec_tid_inv; try intuition congruence.
Qed.

Definition exec_tid_local_star {opT opHiT} (p1 p2 : proc opT opHiT unit) :=
  clos_refl_trans _ exec_tid_local p1 p2.

Instance exec_tid_local_star_preorder {opT opHiT} :
  PreOrder (@exec_tid_local_star opT opHiT).
Proof.
  split.
  - unfold Reflexive, exec_tid_local_star; intros.
    apply rt_refl.
  - unfold Transitive, exec_tid_local_star; intros.
    eapply rt_trans; eauto.
Qed.

Theorem exec_tid_local_to_star : forall opT opHiT (p1 p2 : proc opT opHiT unit),
  exec_tid_local p1 p2 ->
  exec_tid_local_star p1 p2.
Proof.
  unfold exec_tid_local, exec_tid_local_star; intuition.
Qed.

Theorem exec_tid_local_to_exec : forall opT opHiT (p1 p2 : proc opT opHiT unit),
  exec_tid_local p1 p2 ->
  exec_equiv p1 p2.
Proof.
  unfold exec_equiv; split; intros.
  * match goal with
    | H : exec _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
      remember (thread_upd ts tid p); generalize dependent ts;
        induction H; intros; subst
    end.
    - destruct (tid0 == tid); subst.
      + rewrite thread_upd_eq in H0; inversion H0; clear H0; subst.
        eapply H in H1; intuition subst.
        simpl.
        rewrite thread_upd_upd_eq in *; auto.
      + eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in H0 by auto.
          rewrite thread_upd_ne by auto.
          eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eapply IHexec.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    - specialize (H0 tid).
      rewrite thread_upd_eq in H0.
      congruence.
  * match goal with
    | H : exec _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
      remember (thread_upd ts tid p); generalize dependent ts;
        induction H; intros; subst
    end.
    - destruct (tid0 == tid); subst.
      + rewrite thread_upd_eq in H0; inversion H0; clear H0; subst.
        rewrite <- app_nil_l with (l := evs).
        rewrite prepend_app.

        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. reflexivity.
          unfold exec_tid_local in H. edestruct H. apply H0.
        autorewrite with t; simpl.

        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. reflexivity.
          eauto.
        autorewrite with t in *; simpl.

        eauto.

      + eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in H0 by auto.
          rewrite thread_upd_ne by auto.
          eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eapply IHexec.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    - specialize (H0 tid).
      rewrite thread_upd_eq in H0.
      congruence.
Qed.

Theorem exec_tid_local_star_to_exec : forall opT opHiT (p1 p2 : proc opT opHiT unit),
  exec_tid_local_star p1 p2 ->
  exec_equiv p1 p2.
Proof.
  unfold exec_tid_local_star; intros.
  eapply Operators_Properties.clos_rt_rt1n in H.
  induction H.
  - reflexivity.
  - eapply exec_tid_local_to_exec in H.
    etransitivity; eauto.
Qed.
*)

Theorem exec_equiv_bind_bind : forall opT opHiT T1 T2 (p1 : proc opT opHiT T1) (p2 : T1 -> proc opT opHiT T2) (p3 : T2 -> proc opT opHiT unit),
  exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Some (?p, ?ps))) _ |- _ =>
      remember (thread_upd ts tid (Some (p, ps)));
      generalize dependent ts;
      generalize dependent ps;
      generalize dependent p3;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * rewrite thread_upd_eq in H. inversion H; clear H. subst.
        exec_tid_inv.
        {
          eapply ExecOne with (tid := tid).
            rewrite thread_upd_eq. eauto.
            constructor.
            simpl.
            autorewrite with t.
            eauto.
        }

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
    | H : exec _ _ (thread_upd ?ts ?tid (Some (?p, ?ps))) _ |- _ =>
      remember (thread_upd ts tid (Some (p, ps)));
      generalize dependent ts;
      generalize dependent ps;
      generalize dependent p3;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * rewrite thread_upd_eq in H. inversion H; clear H. subst.
        exec_tid_inv.
        {
          eapply ExecOne with (tid := tid).
            rewrite thread_upd_eq. eauto.
            constructor.
            simpl.
            autorewrite with t.
            eauto.
        }

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


Instance trace_equiv_exec_equiv_proper :
  Proper (exec_equiv ==> exec_equiv ==> iff) trace_equiv.
Proof.
  intros p1 p1' ?.
  intros p2 p2' ?.
  unfold trace_equiv, same_traces; split; intros.
  - apply H in H2.
    apply H1 in H2.
    deex.
    apply H0 in H2.
    eauto.
  - apply H in H2.
    apply H1 in H2.
    deex.
    apply H0 in H2.
    eauto.
Qed.


Theorem trace_equiv_bind_a : forall T (p : proc _ _ T) (p2 p2' : T -> proc _ _ unit),
  (forall x, trace_equiv (p2 x) (p2' x)) ->
  trace_equiv (Bind p p2) (Bind p p2').
Proof.
  intros.
  unfold trace_equiv, same_traces; intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid (Some (Bind ?p ?p2, ?ps))) _ |- _ =>
    remember (thread_upd ts tid (Some (Bind p p2, ps)));
    generalize dependent ts;
    generalize dependent p;
    generalize dependent ps;
    induction H; intros; subst
  end.
  - destruct (tid0 == tid); subst.
    + rewrite thread_upd_eq in H0. inversion H0; clear H0. subst.
      exec_tid_inv.
      {
        edestruct IHexec. eauto. intuition idtac.
        eexists; split.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          constructor.
          simpl.
          autorewrite with t.
          eauto.
        simpl. eauto.
      }

      destruct result0.
      * edestruct H.
        (* [trace_equiv] cannot deal with a thread whose current state
           is [ThreadCalled]. *)
        admit.

        destruct H0.
        eexists; split.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
          autorewrite with t.

        (* another [ThreadCalled] vs [ThreadRunning] mismatch.. *)
        admit.

        eauto.

      * edestruct IHexec. eauto.
        eexists; split. destruct H0.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.
        eauto.

        intuition eauto.

    + rewrite thread_upd_upd_ne in * by eauto.
      edestruct IHexec. shelve.

      eexists; split.
      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_upd_ne by auto.
      intuition eauto.
      intuition eauto.
  - specialize (H0 tid).
    rewrite thread_upd_eq in H0.
    congruence.
Admitted.


Theorem trace_equiv_bind : forall T1 T2 (p1 p1' : proc _ _ T1) (p2 p2' : T1 -> proc _ _ T2),
  (forall rx, trace_equiv (Bind p1 rx) (Bind p1' rx)) ->
  (forall rx, (forall x, trace_equiv (Bind (p2 x) rx) (Bind (p2' x) rx))) ->
  (forall rx, trace_equiv (Bind (Bind p1 p2) rx) (Bind (Bind p1' p2') rx)).
Proof.
  intros.
  repeat rewrite exec_equiv_bind_bind.
  rewrite H.
  eapply trace_equiv_bind_a.
  eauto.
Qed.


Theorem trace_equiv_bind_swap' : forall T1 T2 (p1 : proc _ _ T1) (p2 : T1 -> proc _ _ T2) (p3 : T2 -> proc _ _ unit),
  trace_equiv (Bind (Bind p1 p2) p3)
              (Bind p1 (fun x => Bind (p2 x) p3)).
Proof.
  intros.
  rewrite exec_equiv_bind_bind.
  reflexivity.
Qed.


Theorem trace_equiv_bind_swap : forall T1 T2 (p1 : proc _ _ T1) (p2 : T1 -> proc _ _ T2) (p3 : T1 -> T2 -> proc _ _ unit),
  trace_equiv (Bind p1 (fun x => Bind (p2 x) (p3 x)))
              (Bind (Bind p1 (fun x => Bind (p2 x) (fun y => Ret (x, y))))
                    (fun p => p3 (fst p) (snd p))).
Proof.
  unfold trace_equiv, same_traces.
  intros.
  
Admitted.


Theorem trace_equiv_inc_commutes : forall T (ap : proc opT opHiT T) rx,
  trace_equiv (Bind (r <- Atomic ap; i <- Op Inc; Ret (r, i)) rx)
              (Bind (Atomic (r <- ap; i <- Op Inc; Ret (r, i))) rx).
Proof.
Admitted.


Theorem inc_twice_atomic : forall rx,
  trace_equiv (Bind inc_twice_impl rx) (Bind inc_twice_impl_atomic rx).
Proof.
(*
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
*)
Admitted.


Definition trace_match_one_thread {opLoT opMidT opHiT State} lo_step hi_step (s : State)
                                            (p1 : proc opLoT opMidT unit)
                                            (p2 : proc opMidT opHiT unit) :=
  forall tr1,
    exec lo_step s (thread_upd threads_empty 1 (Some (p1, ThreadRunning))) tr1 ->
    exists tr2,
      exec hi_step s (thread_upd threads_empty 1 (Some (p2, ThreadRunning))) tr2 /\
      traces_match tr1 tr2.

Instance trace_match_one_thread_proper {opLoT opMidT opHiT State lo_step hi_step s} :
  Proper (exec_equiv ==> exec_equiv ==> Basics.flip Basics.impl) (@trace_match_one_thread opLoT opMidT opHiT State lo_step hi_step s).
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

Instance trace_match_one_thread_proper2 {opHi2T hi_step s} :
  Proper (trace_equiv ==> exec_equiv ==> Basics.flip Basics.impl) (@trace_match_one_thread opT opHiT opHi2T State op_step hi_step s).
Proof.
  intros p1 p1'; intros.
  intros p2 p2'; intros.
  unfold Basics.flip, Basics.impl; intros.
  unfold trace_match_one_thread in *; intros.
  apply H in H2.
  deex.
  apply H1 in H2.
  deex.
  eexists; intuition eauto.
  apply H0. eauto.
  eapply traces_match_trace_match_hi; eauto.
  unfold trace_match_hi in *; congruence.
Qed.

Theorem all_single_thread_traces_match :
  forall s T (p1 : proc opT opHiT T) (p2 : proc opHiT opHi2T T) (p1rest : T -> proc opT opHiT unit) (p2rest : T -> proc opHiT opHi2T unit),
  (forall s' x, trace_match_one_thread op_step opHi_step s' (p1rest x) (p2rest x)) ->
  compile_ok p1 p2 ->
  trace_match_one_thread op_step opHi_step s (Bind p1 p1rest) (Bind p2 p2rest).
Proof.
  intros.
  generalize dependent p2rest.
  generalize dependent p1rest.
  generalize dependent s.
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

    exec_inv; repeat thread_inv.
    autorewrite with t in *.
    repeat ( exec_tid_inv; intuition try congruence ).

    apply H in H5. deex.

    eexists; split.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eauto.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eapply ExecTidBind; auto.
      eapply ExecTidOpRun.
      constructor.
    eapply ExecOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eapply ExecTidOpRet.
    autorewrite with t.

    match goal with
    | H : exec _ ?s1 (thread_upd _ _ (Some (?p1, _))) _ |-
          exec _ ?s2 (thread_upd _ _ (Some (?p2, _))) _ =>
      replace p2 with p1; [ replace s2 with s1; [ eauto | ] | ]
    end.

    apply functional_extensionality; intros.
    destruct (x == 1); omega.

    f_equal. omega.

    simpl.
    repeat constructor.
    replace (s' 1 + 1 + 1) with (s' 1 + 2) by omega.
    eauto.

  - unfold trace_match_one_thread in *; intros.

    exec_inv; repeat thread_inv; autorewrite with t in *.
    repeat exec_tid_inv; try intuition congruence.

    edestruct H; eauto. intuition try congruence.
    eexists. split.

    exec_one 1.
      eapply ExecTidBind. eauto. eauto.
      autorewrite with t; simpl.

    eapply H1.
    eauto.

  - rewrite exec_equiv_bind_bind.
    rewrite exec_equiv_bind_bind.
    eapply IHcompile_ok.
    intros.
    eapply H1.
    eapply H2.
Qed.
