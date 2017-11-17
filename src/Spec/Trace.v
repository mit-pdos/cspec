Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import ClassicalFacts.
Require Import FunctionalExtensionality.
Require Import Helpers.Helpers.

Axiom EM : excluded_middle.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Proc.

Variable opT : Type -> Type.
Variable opHiT : Type -> Type.

CoInductive proc : Type -> Type :=
| Op : forall T (op : opT T), proc T
| Ret : forall T (v : T), proc T
| Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T
| InvokeOpHi : forall T' (op : opHiT T'), proc unit
| ReturnOpHi : forall T' (result : T'), proc unit.


Variable State : Type.

Variable op_step : forall T, opT T -> nat -> State -> T -> State -> Prop.


CoInductive trace :=
| InvokeLo : forall (tid : nat) T (op : opT T), trace -> trace
| ReturnLo : forall (tid : nat) T (result : T), trace -> trace
| InvokeHi : forall (tid : nat) T (op : opHiT T), trace -> trace
| ReturnHi : forall (tid : nat) T (result : T), trace -> trace
| Empty : trace.


Definition threads_state := forall (tid : nat), option (proc unit).

Definition thread_upd (ts : threads_state) (tid : nat) (s : proc unit) :=
  fun tid' => if tid == tid' then Some s else ts tid'.

Definition thread_del (ts : threads_state) (tid : nat) :=
  fun tid' => if tid == tid' then None else ts tid'.


CoInductive exec : State -> threads_state -> trace -> Prop :=

| ExecRet : forall tid ts T (v : T) trace p s,
  ts tid = Some (Bind (Ret v) p) ->
  exec s (thread_upd ts tid (p v)) trace ->
  exec s ts trace

| ExecOp : forall tid ts T (v : T) trace p s s' op,
  ts tid = Some (Bind (Op op) p) ->
  op_step op tid s v s' ->
  exec s' (thread_upd ts tid (p v)) trace ->
  exec s ts (InvokeLo tid op (ReturnLo tid v trace))

| ExecInvokeHi : forall tid ts trace p s T' (op : opHiT T'),
  ts tid = Some (Bind (InvokeOpHi op) p) ->
  exec s (thread_upd ts tid (p tt)) trace ->
  exec s ts (InvokeHi tid op trace)

| ExecReturnHi : forall tid ts trace p s T' (r : T'),
  ts tid = Some (Bind (ReturnOpHi r) p) ->
  exec s (thread_upd ts tid (p tt)) trace ->
  exec s ts (ReturnHi tid r trace)

| ExecBind : forall tid ts trace T1 (p1 : proc T1) T2 (p2 : T1 -> proc T2) p3 s,
  ts tid = Some (Bind (Bind p1 p2) p3) ->
  exec s (thread_upd ts tid (Bind p1 (fun x => Bind (p2 x) p3))) trace ->
  exec s ts trace

| ExecDone : forall tid ts trace s,
  ts tid = Some (Ret tt) ->
  exec s (thread_del ts tid) trace ->
  exec s ts trace

| ExecEmpty : forall ts s,
  (forall tid, ts tid = None) ->
  exec s ts Empty.

End Proc.


Inductive opT : Type -> Type :=
| Inc : opT nat.

Inductive opHiT : Type -> Type :=
| IncTwice : opHiT nat.

Inductive opHi2T : Type -> Type :=
.

Definition State := nat.

Inductive op_step : forall T, opT T -> nat -> State -> T -> State -> Prop :=
| StepInc : forall tid n,
  op_step Inc tid n (n+1) (n+1).

Inductive opHi_step : forall T, opHiT T -> nat -> State -> T -> State -> Prop :=
| StepIncTwice : forall tid n,
  opHi_step IncTwice tid n (n+2) (n+2).


Definition threads_empty {opT opHiT} : threads_state opT opHiT :=
  fun x => None.

Definition ts := thread_upd threads_empty 1
  (Bind (InvokeOpHi opT opHiT _ IncTwice) (fun _ =>
  (Bind (Op opT opHiT _ Inc) (fun i1 =>
  (Bind (Op opT opHiT _ Inc) (fun i2 =>
  (Bind (ReturnOpHi opT opHiT i2) (fun _ =>
        (Ret opT opHiT tt))))))))).

Lemma thread_upd_eq : forall opT opHiT ts p tid,
  @thread_upd opT opHiT ts tid p tid = Some p.
Proof.
  unfold thread_upd; intros.
  destruct (tid == tid); congruence.
Qed.

Lemma thread_del_upd_eq : forall opT opHiT ts p tid,
  @thread_del opT opHiT (@thread_upd opT opHiT ts tid p) tid =
  @thread_del opT opHiT ts tid.
Proof.
  unfold thread_del, thread_upd; intros.
  apply functional_extensionality; intros.
  destruct (tid == x); congruence.
Qed.

Lemma thread_del_empty : forall opT opHiT tid,
  @thread_del opT opHiT (threads_empty) tid =
  threads_empty.
Proof.
  unfold thread_del, threads_empty; intros.
  apply functional_extensionality; intros.
  destruct (tid == x); congruence.
Qed.


Definition ex_trace :
  { t : trace opT opHiT | exec op_step 4 ts t }.
Proof.
  eexists.
  eapply ExecInvokeHi with (tid := 1).
    unfold ts.
    rewrite thread_upd_eq.
    reflexivity.
  eapply ExecOp with (tid := 1).
    unfold ts.
    rewrite thread_upd_eq.
    reflexivity.
    constructor.
  eapply ExecOp with (tid := 1).
    unfold ts.
    rewrite thread_upd_eq.
    reflexivity.
    constructor.
  eapply ExecReturnHi with (tid := 1).
    unfold ts.
    rewrite thread_upd_eq.
    reflexivity.
  eapply ExecDone with (tid := 1).
    rewrite thread_upd_eq.
    reflexivity.
  eapply ExecEmpty.
    unfold ts.
    repeat rewrite thread_del_upd_eq.
    rewrite thread_del_empty.
    unfold threads_empty; congruence.
Defined.

Eval compute in (proj1_sig ex_trace).


Definition ts2 := thread_upd threads_empty 1
  (Bind (Op opHiT opHi2T _ IncTwice) (fun _ =>
        (Ret opHiT opHi2T tt))).

Definition ex_trace2 :
  { t : trace opHiT opHi2T | exec opHi_step 4 ts2 t }.
Proof.
  eexists.
  eapply ExecOp with (tid := 1).
    unfold ts2.
    rewrite thread_upd_eq.
    reflexivity.
    constructor.
  eapply ExecDone with (tid := 1).
    rewrite thread_upd_eq.
    reflexivity.
  eapply ExecEmpty.
    unfold ts2.
    repeat rewrite thread_del_upd_eq.
    rewrite thread_del_empty.
    unfold threads_empty; congruence.
Defined.

Eval compute in (proj1_sig ex_trace2).


Check InvokeLo.

Inductive traces_match {opLoT opMidT opHiT} :
  forall (t1 : trace opLoT opMidT)
         (t2 : trace opMidT opHiT), Prop :=

| MatchInvokeLo : forall t1 t2 tid T (op : opLoT T),
  traces_match t1 t2 ->
  traces_match (@InvokeLo opLoT opMidT tid _ op t1) t2
| MatchReturnLo : forall t1 t2 tid T (r : T),
  traces_match t1 t2 ->
  traces_match (@ReturnLo opLoT opMidT tid _ r t1) t2

| MatchInvokeMid : forall t1 t2 tid T (op : opMidT T),
  traces_match t1 t2 ->
  traces_match (@InvokeHi opLoT opMidT tid _ op t1)
               (@InvokeLo opMidT opHiT tid _ op t2)
| MatchReturnMid : forall t1 t2 tid T (r : T),
  traces_match t1 t2 ->
  traces_match (@ReturnHi opLoT opMidT tid _ r t1)
               (@ReturnLo opMidT opHiT tid _ r t2)

| MatchInvokeHi : forall t1 t2 tid T (op : opHiT T),
  traces_match t1 t2 ->
  traces_match t1 (@InvokeHi opMidT opHiT tid _ op t2)
| MatchReturnHi : forall t1 t2 tid T (r : T),
  traces_match t1 t2 ->
  traces_match t1 (@ReturnHi opMidT opHiT tid _ r t2)

| MatchEmpty :
  traces_match (Empty opLoT opMidT) (Empty opMidT opHiT).

Hint Constructors traces_match.


Theorem ex_trace_ex_trace2 :
  traces_match (proj1_sig ex_trace) (proj1_sig ex_trace2).
Proof.
  simpl.
  eauto 10.
Qed.
