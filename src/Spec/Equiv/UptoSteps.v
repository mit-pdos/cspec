(* These proofs use an equivalence defined up to some number of execution steps.

   It's still not totally clear how this works, but this is used inductively to
   prove a congruence theorem about trace_incl for Until.
 *)

Require Import Spec.ConcurExec.
Require Import Spec.ThreadsState.
Require Import Spec.Equiv.Execution.
Require Import Spec.Equiv.TraceIncl.

Require Import ProofAutomation.
Require Import Helpers.Instances.
Require Import Morphisms.
Require Import Spec.Equiv.Automation.

Require Import Omega.

Set Implicit Arguments.

Section OpSemantics.

  Context {Op:Type -> Type}.
  Context {State:Type}.
  Variable op_step: OpSemantics Op State.

  Hint Constructors exec_tid.
  Hint Constructors exec_till.

  (** A stronger notion of equivalence where number of steps taken must be
    identical *)

  Local Definition exec_equiv_ts_N n (ts1 ts2: threads_state Op) :=
    forall (s: State) tr,
      exec_till op_step n s ts1 tr <->
      exec_till op_step n s ts2 tr.

  Definition exec_equiv_N n T (p1 p2: proc Op T) :=
    forall ts tid, exec_equiv_ts_N n (ts [[tid := Proc p1]]) (ts [[tid := Proc p2]]).

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

  (* unused, just a remark *)
  Local Theorem trace_incl_rx'_all_n : forall T (p1 p2: proc Op T),
      (forall n, trace_incl_rx_N n p1 p2) ->
      trace_incl_rx' op_step p1 p2.
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
      trace_incl op_step p1 p2.
  Proof.
    unfold trace_incl_rx, trace_incl, trace_incl_ts, trace_incl_ts_s,
    trace_incl_rx_N, trace_incl_N, trace_incl_ts_N.

    intros.
    apply exec_to_counter in H0; propositional.
    eauto.
  Qed.

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
    Reflexive (@trace_incl_ts_N n).
  Proof.
    RelInstance_t.
    unfold trace_incl_ts_N; intros.
    eapply exec_till_to_exec; eauto.
  Qed.

  Hint Resolve trace_incl_N_le.

  Global Instance trace_incl_N_reflexive :
    Reflexive (@trace_incl_N n T) := RelInstance.

  Global Instance trace_incl_rx_preorder :
    PreOrder (@trace_incl_rx T).
  Proof.
    RelInstance_t.
    - repeat (hnf; intros).
      eapply trace_incl_N_bind_a; typeclasses eauto with core.
    - repeat (hnf; intros).
      eapply H in H4; intros; try apply le_n; eauto.
      apply exec_to_counter in H4; propositional.
      eapply H0 in H4; try apply le_n; eauto.
      reflexivity.
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

  (* TODO: surely this can be proven without using [trace_incl_rx] (only
  [trace_incl_rx'_spawn] is needed, which uses a counter-free definition of
  trace inclusion) *)
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
        trace_incl op_step (Bind p1 rx) (Bind p2 rx).
  Proof.
    repeat (hnf; intros).
    eapply exec_to_counter in H0; propositional.
    eapply H; eauto.
    reflexivity.
  Qed.

  Theorem trace_incl_to_trace_incl_rx :
    forall T (p1 p2 : proc Op T),
      (forall `(rx : _ -> proc _ TF),
          trace_incl op_step (Bind p1 rx) (Bind p2 rx)) ->
      trace_incl_rx p1 p2.
  Proof.
    repeat (hnf; intros).
    assert (trace_incl_rx p1 p1) by reflexivity.
    eapply H4 in H3; [ | reflexivity | eassumption | omega ].
    eapply H; eauto.
  Qed.

  Theorem trace_incl_rx'_spawn
    : forall T (p1 p2 : proc Op T),
      trace_incl_rx' op_step p1 p2 ->
      trace_incl_rx' op_step (Spawn p1) (Spawn p2).
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
        * eapply trace_incl_N_ret_bind; eauto.

        * repeat ( intro; intros ).
          eapply IHn' with (n0:=n'); eauto.
        * auto.

      + ExecPrefix tid0 tid'.
        rewrite ConcurExec.thread_upd_abc_to_cab in * by auto.
        eapply IHn' with (n0:=n1) (n':=n1) (rx1:=rx1); intros; try omega; eauto.
  Qed.

  Local Theorem trace_incl_rx_until :
    forall T (p1 p2 : option T -> proc Op T)
      (c : T -> bool) v,
      (forall v', trace_incl_rx (p1 v') (p2 v')) ->
      trace_incl_rx (Until c p1 v) (Until c p2 v).
  Proof.
    repeat ( intro; intros ).
    eapply trace_incl_rx_until_helper in H3; eauto.
    intros; eapply H.
  Qed.

  Theorem trace_incl_rx'_until :
    forall T (p1 p2 : option T -> proc Op T)
      (c : T -> bool) v,
      (forall v', trace_incl_rx' op_step (p1 v') (p2 v')) ->
      trace_incl_rx' op_step (Until c p1 v) (Until c p2 v).
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
