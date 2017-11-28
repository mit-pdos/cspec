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


Definition threads_empty {opT opHiT} : threads_state opT opHiT :=
  fun x => None.

Definition inc_twice_impl :=
  (Bind (InvokeOpHi opT opHiT _ IncTwice) (fun _ =>
  (Bind (Op opT opHiT _ Inc) (fun i1 =>
  (Bind (Op opT opHiT _ Inc) (fun i2 =>
  (Bind (ReturnOpHi opT opHiT i2) (fun _ =>
        (Ret opT opHiT i2))))))))).

Definition p1 :=
  (Bind inc_twice_impl (fun _ =>
        (Ret opT opHiT tt))).

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
  @thread_del opT opHiT (@thread_upd opT opHiT ts tid p) tid =
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


Definition p2 :=
  (Bind (Op opHiT opHi2T _ IncTwice) (fun _ =>
        (Ret opHiT opHi2T tt))).

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
  compile_ok (inc_twice_impl) (Op opHiT opHi2T _ IncTwice)
| CompileRet : forall T (x : T),
  compile_ok (Ret opT opHiT x) (Ret opHiT opHi2T x)
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

Definition threads_compile_ok (ts1 : threads_state opT opHiT) (ts2 : threads_state opHiT opHi2T) :=
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

Definition same_traces {opLo opHi State} op_step (s : State) (ts1 ts2 : threads_state opLo opHi) :=
  forall tr,
    exec op_step s ts1 tr ->
    exists tr', exec op_step s ts2 tr' /\
      forall opHi2 (trHi : trace opHi opHi2),
        traces_match tr trHi -> traces_match tr' trHi.


Definition p1_a :=
  (Bind (Atomic inc_twice_impl) (fun _ =>
        (Ret opT opHiT tt))).

Definition ts_a := thread_upd threads_empty 1 (p1_a, ThreadRunning).


Lemma exec_trace_eq : forall opLo opHi State op_step (s : State) (ts : threads_state opLo opHi) tr1 tr2,
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
  eauto.
Qed.


Lemma traces_match_prepend_one : forall opLo opMid a (tr0 tr1 : trace opLo opMid),
  (forall opHi (trHi : trace opMid opHi),
    traces_match tr0 trHi ->
    traces_match tr1 trHi) ->
  (forall opHi (trHi : trace opMid opHi),
    traces_match (TraceEvent a tr0) trHi ->
    traces_match (TraceEvent a tr1) trHi).
Proof.
  intros.
  remember (TraceEvent a tr0).
  generalize dependent a.
  induction H0; intros; subst; simpl in *.
  all: try congruence.
  all: eauto.
  all: inversion Heqt; subst.
  all: eauto.
Qed.

Lemma traces_match_prepend : forall opLo opMid evs (tr0 tr1 : trace opLo opMid),
  (forall opHi (trHi : trace opMid opHi),
    traces_match tr0 trHi ->
    traces_match tr1 trHi) ->
  (forall opHi (trHi : trace opMid opHi),
    traces_match (prepend evs tr0) trHi ->
    traces_match (prepend evs tr1) trHi).
Proof.
  induction evs; simpl; intros.
  eauto.
  eapply traces_match_prepend_one.
    2: eassumption.
  eauto.
Qed.


Theorem atomic_start :
  forall opT opHiT T State
         op (p : T -> proc opT opHiT unit) ps op_step ts tid (s : State),
  same_traces op_step s
    (thread_upd ts tid (Bind (Op opT opHiT T op) p, ps))
    (thread_upd ts tid (Bind (Atomic (Op opT opHiT T op)) p, ThreadRunning)).
Proof.
  unfold same_traces; intros.
  remember (thread_upd ts0 tid (Bind (Op opT0 opHiT0 T op) p, ps)) as ts.
  generalize dependent ts0.
  generalize dependent ps.
  induction H; intros; subst.

  - destruct (tid == tid0).
    + subst.
      rewrite thread_upd_eq in H.

      inversion H; clear H; subst.

      exec_tid_inv.
      * edestruct IHexec; intuition idtac.
        eexists; split.
        eauto.

        simpl; intros.
        eapply H2.

        remember (TraceEvent (InvokeLo opT0 opHiT0 tid0 T op) trace0).
        induction H; intros; subst.
        all: try congruence.
        constructor. eauto.
        constructor. eauto.

      * eexists; split.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_eq. reflexivity.
          eapply ExecTidAtomic.
          constructor.
          eauto.
          autorewrite with t.

        (* ThreadRunning <> ThreadReturning v... *)
        admit.

        simpl; intros.
        constructor. constructor. eauto.

      * edestruct IHexec; intuition idtac.
        eexists; intuition eauto.

        eapply H2.
        simpl in *.
        remember (TraceEvent (ReturnLo opT0 opHiT0 tid0 v) trace0).
        induction H; intros; subst.
        all: try congruence.
        constructor. eauto.
        constructor. eauto.

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

      eapply traces_match_prepend; eauto.

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
Admitted.


(*
Lemma helper1 : forall S opT opHiT step (s : S) tid p (tr : trace opT opHiT),
  exec step s (thread_upd threads_empty tid p) tr ->
  exec step s (thread_upd threads_empty tid (Bind p (fun _ => Ret _ _ tt))) tr.
Proof.
Admitted.
*)


(**
 PLAN:
 two proof styles:
  - state correspondence like in POCS
  - commute operations in low level while preserving high-level trace
 The theorem below tries to do state correspondence, in a way.

 Need to figure out how to deal with semicolon.
 Need to figure out how to generalize the [compile_ok p1 p2] statement to
  allow for some partially-executed code inside of [p1].  This corresponds
  to some relation between states [s2] and [s1] in the high and low levels,
  respectively.
*)

(**
 TODO: introduce notion of atomicity.

 In particular, we would like to show that the low-level implementation opcodes
 (i.e., Inc) can be commuted to produce atomic groups of more than one opcode.
 Then, we can group the entire inc_twice_impl into a single atomic unit.  Then
 this might simplify our proof.
*)


Theorem all_single_thread_traces_match :
  forall s tr1 (p1 : proc opT opHiT unit) (p2 : proc opHiT opHi2T unit),
  compile_ok p1 p2 ->
  exec op_step s (thread_upd threads_empty 1 (p1, ThreadRunning)) tr1 ->
  exists tr2,
    exec opHi_step s (thread_upd threads_empty 1 (p2, ThreadRunning)) tr2 /\
    traces_match tr1 tr2.
Proof.
  intros.
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
