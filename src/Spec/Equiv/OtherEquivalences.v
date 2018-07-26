Require Import Spec.ConcurExec.
Require Import Spec.ThreadsState.
Require Import Spec.Equiv.Execution.

Require Import ProofAutomation.
Require Import Spec.Equiv.Automation.
Require Import Helpers.Instances.

Require Import Relations.Relation_Operators.
Require Import Morphisms.
Require Import List.
Require Import Omega.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Section OpSemantics.

  Context {Op:Type -> Type}.
  Context {State:Type}.
  Variable op_step: OpSemantics Op State.

  Local Obligation Tactic := try RelInstance_t.

  (** A stronger notion of equivalence where number of steps taken must be
    identical *)

  Local Definition exec_equiv_ts_N n (ts1 ts2: threads_state Op) :=
    forall (s: State) tr,
      exec_till op_step n s ts1 tr <->
      exec_till op_step n s ts2 tr.

  Definition exec_equiv_N n T (p1 p2: proc Op T) :=
    forall ts tid, exec_equiv_ts_N n (ts [[tid := Proc p1]]) (ts [[tid := Proc p2]]).

  (** Trace inclusion for an entire threads_state *)

  Definition trace_incl_ts_s s (ts1 ts2 : threads_state Op) :=
    forall tr,
      exec op_step s ts1 tr ->
      exec op_step s ts2 tr.

  Definition trace_incl_ts (ts1 ts2 : threads_state Op) :=
    forall tr (s : State),
      exec op_step s ts1 tr ->
      exec op_step s ts2 tr.

  Global Program Instance trace_incl_ts_preorder :
    PreOrder trace_incl_ts.
  Next Obligation.
    hnf; intros.
    eauto.
  Qed.
  Next Obligation.
    unfold trace_incl_ts in *; eauto.
  Qed.

  Global Instance exec_equiv_ts_to_trace_incl_ts :
    subrelation (exec_equiv_ts op_step) trace_incl_ts.
  Proof.
    unfold subrelation; intros.
    unfold trace_incl_ts; intros.
    apply H in H0.
    eauto.
  Qed.

  (** Trace inclusion for a single thread *)

  Definition trace_incl_s `(s : State) tid `(p1 : proc Op T) (p2 : proc _ T) :=
    forall ts,
      trace_incl_ts_s s
                      (ts [[ tid := Proc p1 ]])
                      (ts [[ tid := Proc p2 ]]).

  Definition trace_incl {T} (p1 p2 : proc Op T) :=
    forall (ts : threads_state Op) tid,
      trace_incl_ts
        (ts [[ tid := Proc p1 ]])
        (ts [[ tid := Proc p2 ]]).

  Definition trace_incl_ts_N n (ts1 ts2 : threads_state Op) :=
    forall tr s n',
      n' <= n ->
      exec_till op_step n' s ts1 tr ->
      exec op_step s ts2 tr.

  Definition trace_incl_N n {T} (p1 p2 : proc Op T) :=
    forall (ts: threads_state Op) tid,
      trace_incl_ts_N n
                      (ts [[ tid := Proc p1 ]])
                      (ts [[ tid := Proc p2 ]]).

  Definition trace_incl_rx_N n {T} (p1 p2: proc Op T) :=
    forall TF (rx1 rx2 : _ -> proc _ TF) n0,
      n0 <= n ->
      (forall a, trace_incl_N (n0-1) (rx1 a) (rx2 a)) ->
      trace_incl_N n0 (Bind p1 rx1) (Bind p2 rx2).

  Local Definition trace_incl_rx_N' n {T} (p1 p2: proc Op T) :=
    forall TF (rx1 rx2 : _ -> proc _ TF),
      (forall a, trace_incl_N (n-1) (rx1 a) (rx2 a)) ->
      trace_incl_N n (Bind p1 rx1) (Bind p2 rx2).

  Local Theorem trace_incl_rx_N_to_N' : forall n T (p1 p2: proc Op T),
      trace_incl_rx_N n p1 p2 -> trace_incl_rx_N' n p1 p2.
  Proof.
    unfold trace_incl_rx_N, trace_incl_rx_N', trace_incl_N, trace_incl_ts_N.
    intros.
    eapply H; intros; eauto.
    eapply H0; [ | eassumption ].
    omega.
  Qed.

  Local Definition trace_incl_rx {T} (p1 p2: proc Op T) :=
    forall n, trace_incl_rx_N n p1 p2.

  (* natural definition of trace_incl_rx, defined in terms of all executions
     (that is, without requiring counters be identical) *)
  Definition trace_incl_rx' {T} (p1 p2 : proc Op T) :=
    forall TF (rx1 rx2: _ -> proc _ TF),
      (forall a, trace_incl (rx1 a) (rx2 a)) ->
      trace_incl (Bind p1 rx1) (Bind p2 rx2).

  (* unused, just a remark *)
  Local Theorem trace_incl_rx'_all_n : forall T (p1 p2: proc Op T),
      (forall n, trace_incl_rx_N n p1 p2) ->
      trace_incl_rx' p1 p2.
  Proof.
    unfold trace_incl_rx', trace_incl, trace_incl_ts, trace_incl_ts_s,
    trace_incl_rx_N, trace_incl_N, trace_incl_ts_N.

    intros.
    apply exec_to_counter in H1; propositional.
    eapply H in H1; eauto.
    intros.
    eapply H0.
    eapply exec_till_to_exec; eauto.
  Qed.

  (* unused, just a remark *)
  Local Theorem trace_incl_rx_all_n : forall T (p1 p2: proc Op T),
      (forall n, trace_incl_rx_N n p1 p2) ->
      trace_incl_rx p1 p2.
  Proof.
    unfold trace_incl_rx; eauto.
  Qed.

  (* unused, just a remark *)
  (* this is not true of trace_incl_rx' due to p1 and p2 possibly taking different
numbers of steps *)
  Local Theorem trace_incl_rx_to_N : forall T (p1 p2: proc Op T),
      trace_incl_rx p1 p2 ->
      forall n, trace_incl_rx_N n p1 p2.
  Proof.
    unfold trace_incl_rx; eauto.
  Qed.

  (* unused, just a remark *)
  Local Theorem trace_incl_all_n : forall T (p1 p2: proc Op T),
      (forall n, trace_incl_N n p1 p2) ->
      trace_incl p1 p2.
  Proof.
    unfold trace_incl_rx, trace_incl, trace_incl_ts, trace_incl_ts_s,
    trace_incl_rx_N, trace_incl_N, trace_incl_ts_N.

    intros.
    apply exec_to_counter in H0; propositional.
    eauto.
  Qed.

  Hint Constructors exec_tid.
  Hint Constructors exec_till.

  Local Theorem exec_equiv_N_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3) n,
      exec_equiv_N n (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
  Proof.
    split; intros.
    - ExecEquiv p1.
      + ExecOne tid tid'.
        destruct result; eauto.
      + ExecOne tid0 tid'.
        abstract_ts; typeclasses eauto 7 with exec.
    - ExecEquiv p1.
      + ExecOne tid tid'.
        destruct result0; eauto.
      + ExecOne tid0 tid'.
        abstract_ts; typeclasses eauto 7 with exec.
  Qed.

  Theorem trace_incl_trace_incl_s : forall T (p1 p2 : proc Op T),
      trace_incl p1 p2 <->
      (forall s tid,
          trace_incl_s s tid p1 p2).
  Proof.
    unfold trace_incl, trace_incl_s, trace_incl_ts, trace_incl_ts_s.
    split; eauto.
  Qed.

  Ltac forward_chaining :=
    repeat (hnf; intros);
    repeat match goal with
           | [ H: _ |- _ ] => apply H
           end.

  Local Obligation Tactic := try solve [ forward_chaining ].

  Global Program Instance trace_incl_s_preorder :
    PreOrder (@trace_incl_s s tid T).

  Global Program Instance trace_incl_preorder :
    PreOrder (@trace_incl T).

  Global Program Instance exec_equiv_to_trace_incl :
    subrelation (exec_equiv op_step (T:=T)) (@trace_incl T).

  Global Program Instance trace_incl_proper :
    Proper (Basics.flip (@trace_incl T) ==>
                        @trace_incl T ==>
                        Basics.impl) (@trace_incl T).

  Global Program Instance trace_incl_proper_flip :
    Proper (@trace_incl T ==>
                        Basics.flip (@trace_incl T) ==>
                        Basics.flip Basics.impl) (@trace_incl T).

  Global Program Instance trace_incl_s_proper :
    Proper (Basics.flip (@trace_incl T) ==>
                        @trace_incl T ==>
                        Basics.impl) (@trace_incl_s s tid T).

  Global Program Instance trace_incl_s_proper_flip :
    Proper (@trace_incl T ==>
                        Basics.flip (@trace_incl T) ==>
                        Basics.flip Basics.impl) (@trace_incl_s s tid T).

  Global Program Instance trace_incl_s_exec_equiv_proper :
    Proper (exec_equiv op_step ==> exec_equiv op_step ==> iff)
           (@trace_incl_s s tid T).
  Next Obligation.
    split; forward_chaining.
  Qed.

  Global Program Instance trace_incl_exec_equiv_proper :
    Proper (exec_equiv op_step ==> exec_equiv op_step ==> iff)
           (@trace_incl T).
  Next Obligation.
    split; forward_chaining.
  Qed.

  Local Lemma trace_incl_ts_s_proof_helper :
    forall `(p1 : proc Op T) (p2 : proc _ T) ts tid s,
      (forall (ts: threads_state _) tid' s0 s' result tr spawned evs,
          exec_others op_step tid s s0 ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec_tid op_step tid s0 p1 s' result spawned evs ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exec op_step s0 (ts [[tid := Proc p2]]) (prepend tid evs tr)) ->
      trace_incl_ts_s s
                      (ts [[ tid := Proc p1 ]])
                      (ts [[ tid := Proc p2 ]]).
  Proof.
    unfold trace_incl_ts_s.
    intros.
    ExecEquiv tt.
    ExecPrefix tid0 tid'.
    abstract_ts.
    eapply IHexec; intros; eauto with exec.
    auto with nocore exec.

    Grab Existential Variables.
    all: exact (Ret tt).
  Qed.

  Lemma trace_incl_proof_helper :
    forall `(p1 : proc Op T) p2,
      (forall tid tid' (ts: threads_state _) s s' result tr spawned evs,
          exec_tid op_step tid s p1 s' result spawned evs ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exec op_step s (ts [[tid := Proc p2]]) (prepend tid evs tr)) ->
      trace_incl p1 p2.
  Proof.
    unfold trace_incl, trace_incl_ts.
    intros.

    eapply trace_incl_ts_s_proof_helper; eauto.
  Qed.

  Lemma trace_incl_s_proof_helper :
    forall `(p1 : proc Op T) p2 s tid,
      (forall (ts: threads_state _) tid' s0 s' result tr spawned evs,
          exec_others op_step tid s s0 ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec_tid op_step tid s0 p1 s' result spawned evs ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exists tr',
            exec op_step s0 (ts [[tid := Proc p2]]) tr' /\
            prepend tid evs tr = tr') ->
      trace_incl_s s tid p1 p2.
  Proof.
    unfold trace_incl_s.
    intros.

    eapply trace_incl_ts_s_proof_helper.
    intros.
    eapply H in H2; eauto.
    propositional.
  Qed.

  Theorem trace_incl_op :
    forall `(p : T -> proc Op T') op,
      trace_incl
                 (Bind (Call op) p)
                 (Bind (Atomic (Call op)) p).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
    repeat exec_tid_inv.

    ExecPrefix tid tid'.
  Qed.

  Theorem trace_incl_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2',
      (forall x, trace_incl (p2 x) (p2' x)) ->
      trace_incl (Bind p p2) (Bind p p2').
  Proof.
    unfold trace_incl, trace_incl_ts, trace_incl_ts_s.
    intros.

    ExecEquiv p.
    destruct result0; guess_ExecPrefix.
  Qed.

  Theorem trace_incl_s_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2' s tid,
      (forall s' x,
          exec_any op_step tid s p x s' ->
          trace_incl_s s' tid (p2 x) (p2' x)) ->
      trace_incl_s s tid (Bind p p2) (Bind p p2').
  Proof.
    unfold trace_incl_s, trace_incl_ts_s.
    intros.

    thread_upd_ind p.

    cmp_ts tid0 tid.
    + repeat maybe_proc_inv.
      exec_tid_inv.
      destruct result0.

      * ExecPrefix tid tid'.
        eauto.
      * ExecPrefix tid tid'.
        eauto.

    + ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec; intros; eauto with exec.
      eauto with exec.
  Qed.

  Local Theorem trace_incl_N_le :
    forall T (p1 p2 : proc _ T) n1 n2,
      trace_incl_N n2 p1 p2 ->
      n1 <= n2 ->
      trace_incl_N n1 p1 p2.
  Proof.
    repeat ( hnf; intros ).
    eapply H in H2; try omega.
    eauto.
  Qed.

  Hint Extern 4 (_ <= _) => omega.

  Local Theorem trace_incl_N_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2' n,
      (forall x, trace_incl_N (n-1) (p2 x) (p2' x)) ->
      trace_incl_N n (Bind p p2) (Bind p p2').
  Proof.
    unfold trace_incl_N, trace_incl_ts_N.
    intros.
    ExecEquiv p.
    - destruct result0.
      + ExecPrefix tid tid'.
        eapply H with (n':=n0); eauto.
      + ExecPrefix tid tid'.
        eapply IHexec_till; eauto.
    - ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec_till; eauto with exec.
      auto with exec.
  Qed.

  (* NOTE: this is a specialization of trace_incl_N_bind_a, but it's all that's
  needed for the trace_incl Until proof so I've left a standalone proof *)
  Local Theorem trace_incl_N_ret_bind :
    forall `(v : T) TF (rx1 rx2 : _ -> proc _ TF) n,
      (forall a, trace_incl_N (n - 1) (rx1 a) (rx2 a)) ->
      trace_incl_N n (Bind (Ret v) rx1) (Bind (Ret v) rx2).
  Proof.
    repeat (hnf; intros).
    ExecEquiv tt.
    + ExecPrefix tid tid'.
      eapply H in H4; eauto.
    + ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec_till; eauto with exec.
      auto with exec.
  Qed.

  Global Instance trace_incl_ts_N_reflexive :
    Reflexive (@trace_incl_ts_N n) := RelInstance.
  Proof.
    unfold trace_incl_ts_N; intros.
    eapply exec_till_to_exec; eauto.
  Qed.

  Global Instance trace_incl_N_reflexive :
    Reflexive (@trace_incl_N n T) := RelInstance.

  Global Instance trace_incl_rx_preorder :
    PreOrder (@trace_incl_rx T) := RelInstance.
  Proof.
    - (* TODO: simplify this *)
      unfold trace_incl_rx in *.
      intros.
      repeat (hnf; intros).
      eapply H in H4; try omega.
      apply exec_to_counter in H4; propositional.
      eapply H0 in H4; try omega.
      eauto.
      2: intros; reflexivity.
      reflexivity. reflexivity.
      reflexivity.
      intros; eapply trace_incl_N_le; eauto.
      omega.
    - unfold trace_incl_rx, trace_incl_rx_N; intros.
      eapply trace_incl_N_bind_a.
      eauto.
  Qed.

  Global Instance Bind_trace_incl_proper_2 :
    Proper (eq ==> pointwise_relation T0 (@trace_incl T) ==>
               @trace_incl T) Bind.
  Proof.
    intros.
    intros p1a p1b H1; subst.
    intros p2a p2b H2.
    eapply trace_incl_bind_a; intros.
    eapply H2.
  Qed.

  Local Theorem trace_incl_rx_to_exec :
    forall T (p1 p2: proc _ T)
      (ts: threads_state _) s tid tr,
      trace_incl_rx p1 p2 ->
      exec op_step s (ts [[tid := Proc p1]]) tr ->
      exec op_step s (ts [[tid := Proc p2]]) tr.
  Proof.
    intros.
    eapply exec_equiv_bind_ret in H0.
    eapply exec_equiv_bind_ret.
    eapply exec_to_counter in H0; propositional.
    eapply H in H0; eauto.
    reflexivity.
  Qed.

  Local Theorem trace_incl_rx_spawn
    : forall T (p1 p2 : proc Op T),
      trace_incl_rx p1 p2 ->
      trace_incl_rx (Spawn p1) (Spawn p2).
  Proof.
    repeat (hnf; intros).
    match goal with
    | H : exec_till _ _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
        generalize dependent ts;
        induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    - repeat maybe_proc_inv.
      repeat exec_tid_inv.
      ExecPrefix tid tid'.

      eapply H1 in H6; try omega.
      rewrite thread_upd_ne_comm in H6 |- * by auto.
      eapply trace_incl_rx_to_exec; eauto.
    - ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec_till; eauto with exec; try omega.
      auto with exec.
  Qed.

  Theorem trace_incl_rx_to_trace_incl :
    forall T (p1 p2 : proc Op T),
      trace_incl_rx p1 p2 ->
      forall `(rx : _ -> proc _ TF),
        trace_incl (Bind p1 rx) (Bind p2 rx).
  Proof.
    repeat (hnf; intros).
    eapply exec_to_counter in H0; propositional.
    eapply H; eauto.
    reflexivity.
  Qed.

  Theorem trace_incl_to_trace_incl_rx :
    forall T (p1 p2 : proc Op T),
      (forall `(rx : _ -> proc _ TF),
          trace_incl (Bind p1 rx) (Bind p2 rx)) ->
      trace_incl_rx p1 p2.
  Proof.
    repeat (hnf; intros).
    assert (trace_incl_rx p1 p1) by reflexivity.
    eapply H4 in H3; [ | reflexivity | eassumption | omega ].
    eapply H; eauto.
  Qed.

  Theorem trace_incl_rx'_spawn
    : forall T (p1 p2 : proc Op T),
      trace_incl_rx' p1 p2 ->
      trace_incl_rx' (Spawn p1) (Spawn p2).
  Proof.
    intros.
    unfold trace_incl_rx'; intros.
    etransitivity.
    eapply trace_incl_rx_to_trace_incl.
    eapply trace_incl_rx_spawn.
    eapply trace_incl_to_trace_incl_rx; intros.
    eapply H.
    reflexivity.
    eapply trace_incl_bind_a; eauto.
  Qed.

  Local Theorem trace_incl_rx_N_le :
    forall T (p1 p2 : proc _ T) n1 n2,
      trace_incl_rx_N n2 p1 p2 ->
      n1 <= n2 ->
      trace_incl_rx_N n1 p1 p2.
  Proof.
    repeat ( intro; intros ).
    eapply H in H4.
    eassumption.
    3: reflexivity.
    omega.
    intros.
    eapply trace_incl_N_le; eauto.
  Qed.

  Theorem trace_incl_upto_0 : forall T (p1 p2: proc Op T),
      trace_incl_rx_N 0 p1 p2.
  Proof.
    repeat (hnf; intros).
    replace n' with 0 in * by omega.
    match goal with
    | [ H: exec_till _ _ _ _ _ |- _ ] =>
      invert H; eauto
    end.
  Qed.


  Local Theorem trace_incl_rx_until_helper :
    forall T (p1 p2 : option T -> proc Op T)
      (c : T -> bool) n v,
      (forall v', trace_incl_rx_N (n-1) (p1 v') (p2 v')) ->
      trace_incl_rx_N n (Until c p1 v) (Until c p2 v).
  Proof.
    induction n; intros.

    - apply trace_incl_upto_0.
    - assert (forall v, trace_incl_rx_N n (Until c p1 v) (Until c p2 v)) as IHn'.
      intros.
      eapply IHn; intros.
      eapply trace_incl_rx_N_le; eauto.
      clear IHn.
      replace (S n - 1) with n in * by omega.

      repeat (hnf; intros).
      match goal with
      | H : exec_till _ _ _ _ _ |- _ =>
        invert H; clear H; eauto; NoProc_upd
      end.

      cmp_ts tid0 tid.

      + repeat maybe_proc_inv.
        repeat exec_tid_inv.

        unfold until1 in *.
        lazymatch goal with
        | H : exec_till _ _ _ _ _ |- _ =>
          eapply exec_equiv_N_bind_bind in H
        end.

        match goal with
        | H : exec_till _ _ _ _ _,
              H' : forall _, trace_incl_rx_N _ _ _ |- _ =>
          eapply H' in H; try omega
        end.

        ExecPrefix tid tid'.
        unfold until1.
        rewrite exec_equiv_bind_bind.
        eassumption.
        instantiate (1 := n1); omega.

        simpl; intros.
        destruct (c a).
        * eapply trace_incl_N_ret_bind; eauto; intros.
          eapply trace_incl_N_le; eauto; omega.

        * repeat ( intro; intros ).
          eapply IHn'.
          instantiate (1 := n'); omega.
          intros; eapply trace_incl_N_le; eauto; omega.
          eauto.
          eauto.

        * auto.

      + ExecPrefix tid0 tid'.
        rewrite ConcurExec.thread_upd_abc_to_cab in * by auto.
        eapply IHn' with (n0:=n1) (n':=n1) (rx1:=rx1); intros; try omega; eauto.
        eapply trace_incl_N_le; eauto; omega.
  Qed.

  Local Theorem trace_incl_rx_until :
    forall T (p1 p2 : option T -> proc Op T)
      (c : T -> bool) v,
      (forall v', trace_incl_rx (p1 v') (p2 v')) ->
      trace_incl_rx (Until c p1 v) (Until c p2 v).
  Proof.
    repeat ( intro; intros ).
    eapply trace_incl_rx_until_helper in H3.
    5: reflexivity.
    eassumption.
    intros. eapply H.
    reflexivity.
    intros; eapply trace_incl_N_le; eauto; omega.
  Qed.

  Theorem trace_incl_rx'_until :
    forall T (p1 p2 : option T -> proc Op T)
      (c : T -> bool) v,
      (forall v', trace_incl_rx' (p1 v') (p2 v')) ->
      trace_incl_rx' (Until c p1 v) (Until c p2 v).
  Proof.
    intros.
    unfold trace_incl_rx'; intros.
    etransitivity.
    eapply trace_incl_rx_to_trace_incl.
    eapply trace_incl_rx_until; intros.
    eapply trace_incl_to_trace_incl_rx; intros.
    eapply H.
    reflexivity.
    eapply trace_incl_bind_a; intros.
    eauto.
  Qed.

  (** Reuse the complicated proof about [Until]. *)

  Theorem exec_equiv_until_body : forall `(p1 : option T -> proc Op T) p2 c v,
      (forall a, exec_equiv_rx op_step (p1 a) (p2 a)) ->
      exec_equiv_rx op_step (Until c p1 v) (Until c p2 v).
  Proof.
    split; intros.
    - eapply exec_to_counter in H0; deex.
      eapply trace_incl_rx_until; try eassumption; try reflexivity.
      intros; eapply trace_incl_to_trace_incl_rx.
      intros; eapply exec_equiv_to_trace_incl.
      eapply H.
    - eapply exec_to_counter in H0; deex.
      eapply trace_incl_rx_until; try eassumption; try reflexivity.
      intros; eapply trace_incl_to_trace_incl_rx.
      intros; eapply exec_equiv_to_trace_incl.
      symmetry.
      eapply H.
  Qed.

  Global Instance Until_exec_equiv_proper :
    Proper (eq ==>
               pointwise_relation _ (exec_equiv_rx op_step) ==>
               eq ==>
               exec_equiv_rx op_step (T:=T)) Until.
  Proof.
    unfold Proper, respectful, pointwise_relation; intros; subst.
    apply exec_equiv_until_body; eauto.
  Qed.

End OpSemantics.

(** Correspondence between different layers *)

Definition traces_match_ts {OpLo OpHi State} lo_step hi_step
           (ts1 : threads_state OpLo)
           (ts2 : threads_state OpHi) :=
  forall (s : State) tr1,
    exec lo_step s ts1 tr1 ->
    exec hi_step s ts2 tr1.

Global Instance traces_match_ts_proper :
  Proper (@trace_incl_ts OpLo State lo_step ==>
                         @exec_equiv_ts OpHi State hi_step ==>
                         Basics.flip Basics.impl)
         (@traces_match_ts OpLo OpHi State lo_step hi_step).
Proof.
  repeat (hnf; intros).
  repeat match goal with
         | [ H: _ |- _ ] => apply H
         end.
Qed.
