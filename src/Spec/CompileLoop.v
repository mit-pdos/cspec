Require Import ConcurExec.
Require Import Equiv ProcMatch.
Require Import Helpers.Helpers.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import List.
Require Import Compile.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Compiler.

  Variable opLoT : Type -> Type.
  Variable opMidT : Type -> Type.

  Variable compile_op : forall T, opMidT T -> ((option T -> opLoT T) * (T -> bool) * option T).

  Fixpoint compile T (p : proc opMidT T) : proc opLoT T :=
    match p with
    | Ret t => Ret t
    | Prim op =>
      let '(body, cond, iv) := compile_op op in
      Until cond (fun x => Prim (body x)) iv
    | Bind p1 p2 => Bind (compile p1) (fun r => compile (p2 r))
    | Atomic p => Atomic (compile p)
    | Until c p v => Until c (fun r => compile (p r)) v
    | Spawn p => Spawn (compile p)
    end.

  Inductive compile_ok : forall T (p1 : proc opLoT T) (p2 : proc opMidT T), Prop :=
  | CompileOp : forall `(op : opMidT T) body cond iv v,
    compile_op op = (body, cond, iv) ->
    compile_ok (Until cond (fun x => Prim (body x)) v) (Prim op)
  | CompileOp1 : forall `(op : opMidT T) body cond iv v,
    compile_op op = (body, cond, iv) ->
    compile_ok (until1 cond (fun x => Prim (body x)) v) (Prim op)
  | CompileRet : forall `(x : T),
    compile_ok (Ret x) (Ret x)
  | CompileExtraRet : forall `(x : T) `(p1 : T -> proc opLoT TF) p2,
    compile_ok (p1 x) (p2 x) ->
    compile_ok (Bind (Ret x) p1) (p2 x)
  | CompileBind : forall `(p1a : proc opLoT T1) (p2a : proc opMidT T1)
                         `(p1b : T1 -> proc _ T2) (p2b : T1 -> proc _ T2),
    compile_ok p1a p2a ->
    (forall x, compile_ok (p1b x) (p2b x)) ->
    compile_ok (Bind p1a p1b) (Bind p2a p2b)
  | CompileUntil : forall `(p1 : option T -> proc opLoT T) (p2 : option T -> proc opMidT T) (c : T -> bool) v,
    (forall v', compile_ok (p1 v') (p2 v')) ->
    compile_ok (Until c p1 v) (Until c p2 v)
  | CompileSpawn : forall T (p1: proc opLoT T) (p2: proc opMidT T),
      compile_ok p1 p2 ->
      compile_ok (Spawn p1) (Spawn p2)
  .

  Hint Constructors compile_ok.

  Theorem compile_ok_compile :
    forall `(p : proc _ T),
      no_atomics p ->
      compile_ok (compile p) p.
  Proof.
    induction p; simpl; intros; eauto.
    - destruct (compile_op op) as [x iv] eqn:He1.
      destruct x as [body cond] eqn:He2.
      eauto.
    - invert H0; eauto.
    - invert H0; eauto.
    - invert H.
    - invert H; eauto.
  Qed.

  Theorem compile_no_atomics :
    forall `(p : proc _ T),
      no_atomics p ->
      no_atomics (compile p).
  Proof.
    induction p; simpl; intros; eauto.
    - destruct (compile_op op) as [x iv] eqn:He1.
      destruct x as [body cond] eqn:He2.
      eauto.
    - invert H0; eauto.
    - invert H0; eauto.
    - invert H.
    - invert H; eauto.
  Qed.

  Definition compile_ts ts :=
    thread_map compile ts.

  Hint Resolve compile_ok_compile.

  Theorem compile_ts_ok :
    forall ts,
      no_atomics_ts ts ->
      proc_match compile_ok (compile_ts ts) ts.
  Proof.
    intros.
    apply proc_match_sym.
    unfold proc_match; intros.
    unfold compile_ts.
    destruct_with_eqn (ts tid).
    rewrite thread_map_get.
    destruct_with_eqn (ts tid); try congruence.
    invert Heqm; eauto.
    rewrite thread_map_get.
    simpl_match; auto.
  Qed.

  Hint Resolve compile_no_atomics.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    unfold no_atomics_ts, compile_ts; intros.
    eapply thread_map_Forall; eauto.
  Qed.

  Variable State : Type.
  Variable lo_step : OpSemantics opLoT State.
  Variable hi_step : OpSemantics opMidT State.

  Definition noop_or_success :=
    forall T (opM : opMidT T) opL cond iv tid s r s',
      (opL, cond, iv) = compile_op opM ->
      forall v evs,
        lo_step (opL v) tid s r s' evs ->
          cond r = false /\ s = s' /\ evs = nil \/
          cond r = true /\ hi_step opM tid s r s' evs.

  Variable is_noop_or_success : noop_or_success.


  Lemma compile_ok_exec_tid : forall T (p1 : proc _ T) p2,
    compile_ok p1 p2 ->
    forall tid s s' result spawned evs,
      exec_tid lo_step tid s p1 s' result spawned evs ->
      (exists p1',
        s' = s /\
        result = inr p1' /\
        compile_ok p1' p2 /\
        spawned = NoProc /\
        evs = nil) \/
      (exists spawned' result',
        exec_tid hi_step tid s p2 s' result' spawned' evs /\
        proc_optR compile_ok spawned spawned' /\
        match result with
        | inl v => match result' with
          | inl v' => v = v'
          | inr _ => False
          end
        | inr p' => match result' with
          | inl v' => p' = Ret v'
          | inr p'' => compile_ok p' p''
          end
        end).
  Proof.
    induction 1; intros.
    - left.
      exec_tid_inv.
      eexists; intuition idtac.
      eauto.
    - repeat exec_tid_inv.
      eapply is_noop_or_success in H6; eauto.
      intuition idtac; subst.
      + left.
        descend; intuition idtac.
        rewrite H1.
        destruct (Bool.bool_dec false true); try congruence.
        eauto.
      + right.
        descend; intuition idtac.
        eauto.
        eauto.
        simpl.
        rewrite H1.
        destruct (Bool.bool_dec true true); try congruence.
    - right.
      exec_tid_inv.
      descend; intuition idtac.
      eauto.
      eauto.
      simpl; eauto.
    - left.
      repeat exec_tid_inv.
      eexists; intuition idtac.
    - exec_tid_inv.
      edestruct IHcompile_ok; eauto; intuition idtac.
      + repeat deex; subst.
        left.
        eexists; intuition idtac.
        eauto.
      + repeat deex; subst.
        right.
        descend; intuition idtac.
        eauto.
        eauto.
        destruct result0; destruct result'; subst; eauto;
          try solve [ exfalso; eauto ].
    - right.
      exec_tid_inv.
      descend; intuition idtac.
      eauto.
      simpl; eauto.
      constructor; eauto; intros.
      destruct (Bool.bool_dec (c x) true); eauto.
    - right.
      exec_tid_inv.
      descend; intuition eauto.
  Qed.

  Theorem compile_traces_match_ts :
    forall ts1 ts2,
      proc_match compile_ok ts1 ts2 ->
      traces_match_ts lo_step hi_step ts1 ts2.
  Proof.
    unfold traces_match_ts; intros.
    generalize dependent ts2.
    destruct H0.
    induction H; eauto; intros.

    eapply proc_match_pick with (tid := tid) in H3 as H2'.
    intuition idtac; try congruence.
    repeat deex.
    rewrite H in H4; invert H4.

    eapply compile_ok_exec_tid in H1; eauto.
    (intuition eauto); propositional.

    - simpl.
      rewrite thread_upd_same_eq with (tid:=tid') in * by auto.
      eapply IHexec.
      erewrite <- thread_upd_same_eq with (ts := ts2) (tid := tid) by eassumption.
      apply proc_match_upd; eauto.
    - assert (ts2 tid' = NoProc) by eauto using proc_match_none.
      destruct result.
      + epose_proof IHexec.
        eapply proc_match_del; eauto.
        apply proc_match_upd_opt; eauto.
        ExecPrefix tid tid'.
        destruct result'; propositional; eauto.

      + destruct result'; propositional.
        * epose_proof IHexec.
            eapply proc_match_upd; eauto.
            apply proc_match_upd_opt; eauto.

          rewrite exec_equiv_ret_None in H8.

          abstract_tr.
          ExecPrefix tid tid'.
          reflexivity.

        * epose_proof IHexec.
            eapply proc_match_upd; eauto.
            apply proc_match_upd_opt; eauto.
          ExecPrefix tid tid'.
  Qed.

End Compiler.

Arguments compile_ts {opLoT opMidT}.
