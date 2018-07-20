Require Export Trace.
Require Export ConcurProc.
Require Export ExecSemantics.
Require Export Helpers.FinMap.

Require Import ProofAutomation.
Require Import Helpers.ListStuff.
Require Import Helpers.Instances.

Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Bool.

Section Execution.

  Variable Op:Type -> Type.
  Variable State: Type.
  Variable op_step: OpSemantics Op State.

  Inductive exec_till : nat -> State -> threads_state Op -> trace -> Prop :=

  | ExecTillOne : forall T tid tid' (ts : threads_state Op) trace p s s' evs result spawned n,
    ts tid = @Proc Op T p ->
    ts tid' = NoProc ->
    exec_tid op_step tid s p s' result spawned evs ->
    exec_till n s' (thread_upd (thread_upd ts tid' spawned) tid
              match result with
              | inl _ => NoProc
              | inr p' => Proc p'
              end) trace ->
    exec_till (S n) s ts (prepend tid evs trace)

  | ExecTillStop : forall (ts : threads_state Op) s,
    exec_till 0 s ts TraceEmpty.

  Theorem exec_to_counter : forall s ts tr,
      exec op_step s ts tr ->
      exists n, exec_till n s ts tr.
  Proof.
    induction 1; propositional;
      eauto using ExecTillOne, ExecTillStop.
  Qed.

  Theorem exec_till_to_exec : forall n s ts tr,
      exec_till n s ts tr ->
      exec op_step s ts tr.
  Proof.
    induction 1; propositional;
      eauto using ExecOne, ExecStop.
  Qed.

  Theorem ExecPrefixOne
       : forall (T : Type)
           (tid : nat) (ts : threads_state Op) (tr : trace)
           (p : proc Op T) (s s' : State)
           (evs : list event) (result : T + proc Op T)
           (tid' : nat) spawned,
         thread_get ts tid = Proc p ->
         thread_get ts tid' = NoProc ->
         exec_tid op_step tid s p s' result spawned evs ->
         exec op_step s'
           (thread_upd (thread_upd ts tid' spawned) tid
             (match result with
              | inl _ => NoProc
              | inr p' => Proc p'
              end)) tr ->
         exec op_step s ts (prepend tid evs tr).
  Proof.
    intros.
    eapply ExecOne; eauto.
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
    exec_tid op_step tid s p s' (inl r) spawned evs ->
    exec_any tid s p r s'
  | ExecAnyThisMore :
    forall T (p p' : proc Op T) (s' s0 : State) r spawned evs,
    exec_tid op_step tid s p s0 (inr p') spawned evs ->
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
    exec_any tid s (Call op) r s' ->
      exists s0 evs,
        exec_others tid s s0 /\
        op_step op tid s0 r s' evs.
  Proof.
    intros.
    remember (Call op).
    induct H;
      repeat match goal with
             | [ H: forall _, Call _ = Call _ -> _ |- _ ] =>
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
      exec_tid op_step tid' s p s' result spawned evs ->
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

End Execution.

Hint Constructors exec_any.
Hint Resolve exec_tid_exec_others.
Hint Resolve exec_others_exec_any.
Hint Resolve exec_others_trans.

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

Hint Resolve ExecOne.
Hint Extern 1 (exec _ _ _ TraceEmpty) => simple apply ExecStop.

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

(* for performance reasons, we define this safely repeated version of
  exec_tid_inv *)
Local Notation exec_p p := (exec_tid _ _ _ p _ _ _ _) (only parsing).
Ltac exec_tid_simpl :=
  let execinv H := inversion H; clear H; subst in
  repeat (match goal with
          | [ H: exec_p (Ret _) |- _ ] => execinv H
          | [ H: exec_p (Atomic _) |- _ ] => execinv H
          | [ H: exec_p (Call _) |- _ ] => execinv H
          | [ H: exec_p (Bind _ _) |- _ ] => execinv H
          | [ H: exec_p (Until _ _ _) |- _ ] => execinv H
          | [ H: exec_p (Spawn _) |- _ ] => execinv H
          end || maybe_proc_inv);
  autorewrite with t in *.

(* former unoptimized implementation *)
(* Ltac exec_tid_simpl := repeat (exec_tid_inv; is_one_goal). *)

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

Local Lemma exec_ts_eq : forall Op State (op_step: OpSemantics Op State) s ts ts' tr,
    exec op_step s ts' tr ->
    ts = ts' ->
    exec op_step s ts tr.
Proof.
  propositional.
Qed.

Local Lemma exec_till_ts_eq : forall n Op State (op_step: OpSemantics Op State) s ts ts' tr,
    exec_till op_step n s ts' tr ->
    ts = ts' ->
    exec_till op_step n s ts tr.
Proof.
  propositional.
Qed.

(* abstract the thread state in an exec goal (to deal with different update
forms) *)
Ltac abstract_ts :=
  match goal with
  | |- exec _ _ ?ts _ => eapply exec_ts_eq
  | |- exec_till _ _ _ ?ts _ => eapply exec_till_ts_eq
  end.

Local Lemma exec_tr_eq : forall Op State (op_step: OpSemantics Op State) s ts tr tr',
    exec op_step s ts tr' ->
    tr = tr' ->
    exec op_step s ts tr.
Proof.
  propositional.
Qed.

(* abstract the trace in an exec goal (to deal with different calls to
prepend/list append) *)
Ltac abstract_tr :=
  match goal with
  | |- exec _ _ _ ?tr => eapply exec_tr_eq
  end.

Ltac NoProc_upd :=
  repeat lazymatch goal with
         | [ H: thread_get (thread_upd _ ?tid (Proc _)) ?tid' = NoProc |- _ ] =>
           cmp_ts tid tid';
           [ solve [ maybe_proc_inv ] | ]
         end.

Ltac remove_redundant_upds :=
  repeat match goal with
         | [ Heq: thread_get ?ts ?tid = ?p,
                  H: context[thread_upd ?ts ?tid ?p] |- _ ] =>
           rewrite (thread_upd_same_eq _ _ Heq) in H
         | [ Heq: thread_get ?ts ?tid = ?p
             |- context[thread_upd ?ts ?tid ?p] ] =>
           rewrite (thread_upd_same_eq _ _ Heq) in |- *
         end.

(* the ExecPrefix tactic solves exec goals by splitting them into one
execution step and leaving the exec for [auto] *)

(* copy some basic hints from core *)
Hint Extern 2 (_ <> _) => simple apply not_eq_sym; trivial : exec.
Hint Extern 2 (_ = _) => simple apply eq_sym : exec.
Hint Resolve eq_refl : exec.

Local Lemma thread_upd_aba :
  forall Op (ts: threads_state Op) tid1 tid2 p1 p2 p3,
    tid1 <> tid2 ->
    ts [[tid1 := p1]] [[tid2 := p2]] [[tid1 := p3]] =
    ts [[tid2 := p2]] [[tid1 := p3]].
Proof.
  intros.
  rewrite ?thread_upd_ne_comm with (tid:=tid2) (tid':=tid1) by auto.
  f_equal.
  autorewrite with t; auto.
Qed.

Local Lemma thread_upd_abc_to_cab :
  forall Op (ts: threads_state Op) tid1 tid2 tid3 p1 p2 p3,
    tid1 <> tid2 ->
    tid1 <> tid3 ->
    ts [[tid1 := p1]] [[tid2 := p2]] [[tid3 := p3]] =
    ts [[tid2 := p2]] [[tid3 := p3]] [[tid1 := p1]].
Proof.
  intros.
  rewrite thread_upd_ne_comm with (tid := tid1) (tid' := tid2) by congruence.
  rewrite thread_upd_ne_comm with (tid := tid1) (tid' := tid3) by congruence.
  auto.
Qed.

Local Lemma thread_upd_other_eq : forall Op (ts:threads_state Op)
                              tid T (p: proc _ T) tid' T' (p': proc _ T'),
    tid' <> tid ->
    ts tid' = Proc p ->
    ts [[tid := Proc p']] tid' = Proc p.
Proof.
  intros.
  autorewrite with t.
  auto.
Qed.

Local Lemma thread_upd_spawn_delay :
  forall Op (ts: threads_state Op) tid T (p: proc _ T) tid' spawned tid'' p',
    tid'' <> tid ->
    tid <> tid' ->
    ts [[tid := Proc p]] [[tid' := spawned]] [[tid'' := p']] =
    ts [[tid' := spawned]] [[tid'' := p']] [[tid := Proc p]].
Proof.
  intros.
  apply thread_upd_abc_to_cab; auto.
Qed.

Local Lemma thread_spawn_none :
  forall Op (ts: threads_state Op) T (p: proc Op T) tid tid' ,
    tid <> tid' ->
    ts tid' = NoProc ->
    ts [[tid := Proc p]] [[tid' := NoProc]] =
    ts [[tid := Proc p]].
Proof.
  intros.
  rewrite thread_upd_same_eq; auto.
  autorewrite with t; auto.
Qed.

Hint Resolve thread_upd_other_eq : exec.
Hint Resolve thread_upd_spawn_delay : exec.
Hint Resolve thread_upd_ne_comm : exec.
Hint Resolve thread_upd_abc_to_cab : exec.
Hint Constructors exec_tid atomic_exec : exec.

Hint Extern 1 (exec _ _ _ _) =>
match goal with
| |- exec _ _ ?ts _ => first [ is_evar ts; fail 1 | eapply exec_ts_eq ]
end : exec.

Hint Rewrite thread_spawn_none using congruence : t.
Hint Rewrite thread_upd_aba using congruence : t.

Ltac ExecPrefix tid_arg tid'_arg :=
  eapply ExecPrefixOne with (tid:=tid_arg) (tid':=tid'_arg);
  autorewrite with t;
  (* need to exclude core for performance reasons *)
  eauto 7 with nocore exec;
  remove_redundant_upds;
  cbv beta iota.

Module Examples.

  Theorem ret_exec_example : forall Op State (op_step: OpSemantics Op State)
                               (ts: threads_state Op) tid tid' T (v:T) s tr,
    tid <> tid' ->
    ts tid' = NoProc ->
    ts tid = NoProc ->
    exec op_step s ts tr ->
    exec op_step s (ts [[tid := Proc (Ret v)]]) tr.
  Proof.
    intros.
    abstract_tr.
    ExecPrefix tid tid'.
    eassumption.
    reflexivity.
  Qed.

End Examples.
