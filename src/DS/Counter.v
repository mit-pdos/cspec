Require Import CSPEC.


Parameter extopT : Type -> Type.


Module VariableOp <: Ops.

  Inductive rpcOp : Type :=
  | Inc : rpcOp
  | Dec : rpcOp
  .

  Inductive xOp : Type -> Type :=
  | Read : xOp nat
  | Write : nat -> xOp unit

  | RpcClientPut : rpcOp -> xOp unit
  | RpcClientGet : xOp nat
  | RpcServerGet : xOp rpcOp
  | RpcServerPut : nat -> xOp unit

  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End VariableOp.


Module VariableState <: State.

  Import VariableOp.

  Definition server_tid := 0.

  Inductive req_or_res :=
  | rpcReq : rpcOp -> req_or_res
  | rpcRes : nat -> req_or_res
  .

  Record state_rec := mk_state {
    var : nat;
    rpc : option req_or_res
  }.

  Definition State := state_rec.

End VariableState.


Module VariableAPI <: Layer VariableOp VariableState.

  Import VariableOp.
  Import VariableState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepRead : forall v rpc,
    xstep Read server_tid
      (mk_state v rpc)
      v
      (mk_state v rpc)
      nil

  | StepWrite : forall v0 v rpc,
    xstep (Write v) server_tid
      (mk_state v0 rpc)
      tt
      (mk_state v rpc)
      nil

  | StepRpcClientPut : forall tid v req,
    xstep (RpcClientPut req) tid
      (mk_state v None)
      tt
      (mk_state v (Some (rpcReq req)))
      nil

  | StepRpcClientGet : forall tid v res,
    xstep RpcClientGet tid
      (mk_state v (Some (rpcRes res)))
      res
      (mk_state v None)
      nil

  | StepRpcServerGet : forall v req,
    xstep RpcServerGet server_tid
      (mk_state v (Some (rpcReq req)))
      req
      (mk_state v (Some (rpcReq req)))
      nil

  | StepRpcServerPut : forall v req res,
    xstep (RpcServerPut res) server_tid
      (mk_state v (Some (rpcReq req)))
      tt
      (mk_state v (Some (rpcRes res)))
      nil

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.
  Definition initP (s : State) := rpc s = None.

End VariableAPI.


Module CounterOp <: Ops.

  Inductive xOp : Type -> Type :=
  | RunServer : xOp unit
  | CallInc : xOp unit
  | CallDec : xOp unit
  | GetRes : xOp nat

  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End CounterOp.


Module CounterAPI <: Layer CounterOp VariableState.

  Import CounterOp.
  Import VariableState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepServerInc : forall v,
    xstep RunServer server_tid
      (mk_state v (Some (rpcReq VariableOp.Inc)))
      tt
      (mk_state (v+1) (Some (rpcRes v)))
      nil

  | StepServerDec : forall v,
    xstep RunServer server_tid
      (mk_state v (Some (rpcReq VariableOp.Dec)))
      tt
      (mk_state (v-1) (Some (rpcRes v)))
      nil

  | StepCallInc : forall tid v,
    xstep CallInc tid
      (mk_state v None)
      tt
      (mk_state v (Some (rpcReq VariableOp.Inc)))
      nil

  | StepCallDec : forall tid v,
    xstep CallDec tid
      (mk_state v None)
      tt
      (mk_state v (Some (rpcReq VariableOp.Dec)))
      nil

  | StepGetRes : forall tid v r,
    xstep GetRes tid
      (mk_state v (Some (rpcRes r)))
      r
      (mk_state v None)
      nil

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.
  Definition initP (s : State) := rpc s = None.

End CounterAPI.


Module CounterImpl <:
  LayerImplMoversT
    VariableState
    VariableOp VariableAPI
    CounterOp  CounterAPI.

  Definition server_core :=
    op <- Call (VariableOp.RpcServerGet);
    match op with
    | VariableOp.Inc =>
      v <- Call (VariableOp.Read);
      _ <- Call (VariableOp.Write (v+1));
      Call (VariableOp.RpcServerPut v)
    | VariableOp.Dec =>
      v <- Call (VariableOp.Read);
      _ <- Call (VariableOp.Write (v-1));
      Call (VariableOp.RpcServerPut v)
    end.

  Definition compile_op T (op : CounterOp.Op T) : proc _ T :=
    match op with
    | CounterOp.RunServer => server_core
    | CounterOp.CallInc => Call (VariableOp.RpcClientPut VariableOp.Inc)
    | CounterOp.CallDec => Call (VariableOp.RpcClientPut VariableOp.Dec)
    | CounterOp.GetRes => Call (VariableOp.RpcClientGet)
    | CounterOp.Ext extop => Call (VariableOp.Ext extop)
    end.

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
    econstructor; eauto.
    destruct x; eauto.
  Qed.

  Ltac step_inv :=
    match goal with
    | H : VariableAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : CounterAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (CounterAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (VariableAPI.step _ _ _ _ _ _) => econstructor.

  Theorem compile_correct :
    compile_correct compile_op VariableAPI.step CounterAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + atomic_exec_inv.
      destruct v1.
      - repeat atomic_exec_inv; repeat step_inv; eauto; simpl.
      - repeat atomic_exec_inv; repeat step_inv; eauto; simpl.
    + atomic_exec_inv; repeat step_inv; eauto.
    + atomic_exec_inv; repeat step_inv; eauto.
    + atomic_exec_inv; repeat step_inv; eauto.
    + atomic_exec_inv; repeat step_inv; eauto.
  Qed.

  Theorem server_get_right_mover :
    right_mover
      VariableAPI.step
      VariableOp.RpcServerGet.
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.
  Qed.

  Hint Resolve server_get_right_mover.

  Theorem read_right_mover :
    right_mover
      VariableAPI.step
      VariableOp.Read.
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.
  Qed.

  Hint Resolve read_right_mover.

  Theorem write_right_mover : forall v,
    right_mover
      VariableAPI.step
      (VariableOp.Write v).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto 10.
  Qed.

  Hint Resolve write_right_mover.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers VariableAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.

    econstructor; eauto.
    destruct r; eauto.
  Qed.

  Definition initP_compat :
    forall s, CounterAPI.initP s -> VariableAPI.initP s :=
    ltac:(auto).

End CounterImpl.


Module CounterAtomicOp <: Ops.

  Inductive xOp : Type -> Type :=
  | DoInc : xOp nat
  | DoDec : xOp nat

  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End CounterAtomicOp.


Module CounterAtomicAPI <: Layer CounterAtomicOp VariableState.

  Import CounterAtomicOp.
  Import VariableState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepInc : forall tid v,
    xstep DoInc tid
      (mk_state v None)
      v
      (mk_state (v+1) None)
      nil

  | StepDec : forall tid v,
    xstep DoDec tid
      (mk_state v None)
      v
      (mk_state (v-1) None)
      nil

  | StepExt : forall s tid `(extop : extopT T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.
  Definition initP (s : State) := rpc s = None.

End CounterAtomicAPI.


Module CounterAtomicLayer <:
  LayerImpl
    CounterOp       VariableState CounterAPI
    CounterAtomicOp VariableState CounterAtomicAPI.

  (**
   * CounterAtomicLayer seems impossible to prove with CSPEC movers.
   * Imagine [DoInc] as roughly [CallInc; GetRes].  The commit point
   * (non-mover) is the [CallInc], since that determines order among
   * many client threads that are calling [DoInc].  That requires
   * [GetRes] to be a left-mover.  But it cannot move left past the
   * execution of the server (on another tid) that handles the Inc
   * RPC call..
   *)

  Definition forever (_ : unit) := false.
  Definition server_core :=
    Until forever (fun _ => Call CounterOp.RunServer) None.

  Definition inc_core :=
    _ <- Call (CounterOp.CallInc);
    Call (CounterOp.GetRes).

  Definition dec_core :=
    _ <- Call (CounterOp.CallDec);
    Call (CounterOp.GetRes).

  Definition compile_op T (op : CounterAtomicOp.Op T) : proc _ T :=
    match op with
    | CounterAtomicOp.DoInc => inc_core
    | CounterAtomicOp.DoDec => dec_core
    | CounterAtomicOp.Ext extop => Call (CounterOp.Ext extop)
    end.

  (**
   * The tentative plan here is to hide the server thread.  As long
   * as the real server thread generates no events (empty trace), the
   * abstract view (as CounterAtomicAPI) can't tell what's going on
   * in the server.
   *
   * Mechnically, [compile_ts] just overwrites anything the
   * caller may have had for [tid = server_tid], and this might be
   * OK because it is possible for that thread to never run.
   *)

  Definition compile_ts (ts : threads_state CounterAtomicOp.Op) :=
    let ts' := Compile.compile_ts compile_op ts in
    thread_upd ts' VariableState.server_tid (Proc server_core).

  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
  Qed.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    intros.
    eapply no_atomics_thread_upd_Proc.
    - eapply Compile.compile_ts_no_atomics; eauto.
      intros; eapply compile_op_no_atomics.
    - compute; eauto.
  Qed.

  (**
   * Boilerplate.
   *)

  Definition absR (s0 s1 : VariableState.State) := s0 = s1.

  Theorem absInitP :
    forall s1,
      CounterAPI.initP s1 ->
      exists s2, absR s1 s2 /\
            CounterAtomicAPI.initP s2.
  Proof.
    unfold absR; eauto.
  Qed.

  (**
   * As a proof technique, our existing [Atomic] might not be sufficient
   * because we want atomicity with respect to everything _except_ for
   * the server thread.  And it's OK to ignore the server thread because
   * the higher level (CounterAtomicAPI) can't tell -- the server thread
   * is not exposed because it gets overwritten by [compile_ts].
   *
   * This means we need some more fine-grained notion of atomization to
   * push through a proof similar to [Compile.v] but in the presence of
   * the hidden [server_tid] thread.
   *)

  Ltac step_inv :=
    match goal with
    | H : CounterAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.

  Theorem compile_traces_match_helper :
    forall s tr tsc,
      exec CounterAPI.step s tsc tr ->
      forall ts,
        no_atomics_ts ts ->
        (
          VariableState.rpc s = None /\
          tsc = Compile.compile_ts compile_op ts
            [[ VariableState.server_tid := Proc (until1 forever (fun _ => Call CounterOp.RunServer) None) ]]
        ) ->
        exec CounterAtomicAPI.step s ts tr.
  Proof.
    induction 1; intros; eauto; intuition idtac; subst.
    - (* Case 1: clean state *)
      destruct (tid == VariableState.server_tid); subst.
      + (* Server TID: should be impossible *)
        autorewrite with t in *.
        maybe_proc_inv; subst; repeat sigT_eq.
        repeat exec_tid_inv.
        step_inv; simpl in *; congruence.
      + (* Client TID *)
        autorewrite with t in *.
        unfold Compile.compile_ts in H.
        rewrite thread_map_get_match in H.
        destruct (ts0 tid) eqn:Heq.
  Admitted.

  Theorem compile_traces_match :
    forall ts,
      no_atomics_ts ts ->
      traces_match_abs absR
        CounterAPI.initP CounterAtomicAPI.initP
        CounterAPI.step CounterAtomicAPI.step (compile_ts ts) ts.
  Proof.
    unfold traces_match_abs.
    unfold CounterAPI.initP, CounterAtomicAPI.initP; intros.
    eexists; split; [ reflexivity | ].
    split; eauto.

    eapply compile_traces_match_helper; eauto.
  Qed.

End CounterAtomicLayer.
