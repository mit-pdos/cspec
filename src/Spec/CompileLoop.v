Require Import ConcurProc.
Require Import Equiv.
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

  Variable compile_op : forall T, opMidT T -> ((T -> opLoT T) * (T -> bool) * T).

  Fixpoint compile T (p : proc opMidT T) : proc opLoT T :=
    match p with
    | Ret t => Ret t
    | Op op =>
      let '(body, cond, iv) := compile_op op in
      Until cond (fun x => Op (body x)) iv
    | Bind p1 p2 => Bind (compile p1) (fun r => compile (p2 r))
    | Log v => Log v
    | Atomic p => Atomic (compile p)
    | Until c p v => Until c (fun r => compile (p r)) v
    end.

  Inductive compile_ok : forall T (p1 : proc opLoT T) (p2 : proc opMidT T), Prop :=
  | CompileOp : forall `(op : opMidT T) body cond iv v,
    compile_op op = (body, cond, iv) ->
    compile_ok (Until cond (fun x => Op (body x)) v) (Op op)
  | CompileOp1 : forall `(op : opMidT T) body cond iv v,
    compile_op op = (body, cond, iv) ->
    compile_ok (until1 cond (fun x => Op (body x)) v) (Op op)
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
  | CompileUntil : forall `(p1 : T -> proc opLoT T) (p2 : T -> proc opMidT T) (c : T -> bool) v,
    (forall v', compile_ok (p1 v') (p2 v')) ->
    compile_ok (Until c p1 v) (Until c p2 v)
  | CompileLog : forall `(v : T),
    compile_ok (Log v) (Log v).

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
    - inversion H0; clear H0; repeat sigT_eq.
      eauto.
    - inversion H0; clear H0; repeat sigT_eq.
      eauto.
    - inversion H.
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
    - inversion H0; clear H0; repeat sigT_eq. eauto.
    - inversion H0; clear H0; repeat sigT_eq. eauto.
    - inversion H.
  Qed.

  Fixpoint compile_ts (ts : threads_state) : threads_state :=
    match ts with
    | nil => nil
    | t :: ts' =>
      match t with
      | NoProc => NoProc
      | Proc p => Proc (compile p)
      end :: compile_ts ts'
    end.

  Theorem compile_ts_ok :
    forall ts,
      no_atomics_ts ts ->
      proc_match compile_ok (compile_ts ts) ts.
  Proof.
    induction ts; intros.
    - unfold proc_match; simpl; intuition eauto.
      left.
      repeat rewrite thread_get_nil; eauto.
    - apply no_atomics_ts_cons in H; intuition idtac.
      unfold proc_match in *; cbn; intuition eauto.
      destruct tid; subst.
      + repeat rewrite thread_get_0.
        destruct a.
        * simpl in *.
          right.
          do 3 eexists; intuition eauto.
          eapply compile_ok_compile; eauto.
        * left; eauto.
      + repeat rewrite thread_get_S.
        eapply H3.
  Qed.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    induction ts; intros.
    - constructor.
    - simpl.
      apply no_atomics_ts_cons in H; intuition idtac.
      constructor; [ | assumption ].
      destruct a; eauto.
      simpl.
      eapply compile_no_atomics; eauto.
  Qed.


  Variable State : Type.
  Variable lo_step : OpSemantics opLoT State.
  Variable hi_step : OpSemantics opMidT State.

  Definition noop_or_success :=
    forall `(opM : opMidT T) opL cond iv tid s r s',
      (opL, cond, iv) = compile_op opM ->
      forall v,
        lo_step (opL v) tid s r s' ->
          cond r = false /\ s = s' \/
          cond r = true /\ hi_step opM tid s r s'.

  Variable is_noop_or_success : noop_or_success.


  Lemma compile_ok_exec_tid : forall T (p1 : proc _ T) p2,
    compile_ok p1 p2 ->
    forall tid s s' result evs,
      exec_tid lo_step tid s p1 s' result evs ->
      (exists p1',
        s' = s /\
        result = inr p1' /\
        compile_ok p1' p2 /\
        evs = nil) \/
      (exists result',
        exec_tid hi_step tid s p2 s' result' evs /\
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
        eexists; intuition idtac.
        rewrite H1.
        destruct (Bool.bool_dec false true); try congruence.
        eauto.
      + right.
        eexists; intuition idtac.
        eauto.
        simpl.
        rewrite H1.
        destruct (Bool.bool_dec true true); try congruence.
    - right.
      exec_tid_inv.
      eexists; intuition idtac.
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
        eexists; intuition idtac.
        eauto.
        destruct result0; destruct result'; subst; eauto;
          try solve [ exfalso; eauto ].
    - right.
      exec_tid_inv.
      eexists; intuition idtac.
      eauto.
      simpl; eauto.
      constructor; eauto; intros.
      destruct (Bool.bool_dec (c x) true); eauto.
    - right.
      exec_tid_inv.
      eexists; intuition idtac.
      eauto.
      simpl; eauto.
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

    eapply proc_match_pick with (tid := tid) in H2 as H2'.
    intuition idtac; try congruence.
    repeat deex.
    rewrite H in H3; inversion H3; clear H3; subst; repeat sigT_eq.

    edestruct compile_ok_exec_tid; eauto;
      repeat deex.

    - simpl.
      eapply IHexec.
      erewrite <- thread_upd_same with (ts := ts2).
      eapply proc_match_upd; eauto.
      eauto.

    - destruct result.
      + edestruct IHexec.
          eapply proc_match_del; eauto.
        eexists; intuition idtac.
        eapply ExecPrefixOne with (tid := tid).
          eauto.
          eauto.
          destruct result'; eauto; exfalso; eauto.
        eauto.

      + destruct result'; subst.
        * edestruct IHexec.
            eapply proc_match_upd; eauto.
          eexists; intuition idtac.

          rewrite exec_equiv_ret_None in H7.

          eapply ExecPrefixOne with (tid := tid).
            eauto.
            eauto.
            eauto.
          eauto.

        * edestruct IHexec.
            eapply proc_match_upd; eauto.
          eexists; intuition idtac.
          eapply ExecPrefixOne with (tid := tid).
            eauto.
            eauto.
            eauto.
          eauto.
  Qed.

End Compiler.

Arguments compile_ts {opLoT opMidT}.
