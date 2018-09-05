Require Import Spec.Proc.
Require Import Spec.ThreadsState.
Require Import Spec.Automation.

Require Import Helpers.TransitionSystem.
Require Import Helpers.ProofAutomation.
Require Import Helpers.RecordSet.
Require Import Helpers.Instances.

Require Import Morphisms.
Require Import List.

Notation "ts [[ tid  :=  p ]]" := (thread_upd ts tid (Some p))
                                    (at level 12, left associativity).
Notation "ts [[ - tid ]]" := (thread_upd ts tid None)
                               (at level 12, left associativity).

Definition TID := nat.
Implicit Types (tid:TID).

Inductive event :=
| Event T (x:T).

Definition trace := list (TID * event).
Definition add_id tid (evs: list event) : trace := map (pair tid) evs.

Definition etrace {A B} (x: A * B * trace) : trace := let '(_, _, tr) := x in tr.

Instance Set_etrace A B : Setter (etrace (A:=A) (B:=B)).
Proof.
  refine {| set := fun f '(a, b, tr) => (a, b, f tr); |};
    intros;
    destruct matches.
Defined.

Section Execution.
  Variable Op:Type.
  Variable State:Type.
  Definition InstStep := Op -> State -> State -> list event -> Prop.
  Variable step: InstStep.
  Implicit Types (op:Op) (p: proc Op) (s:State) (tr:trace).

  Inductive proc_step tid : Relation (proc Op * State * trace) :=
  | exec_op : forall op s s' evs,
      step op s s' evs ->
      forall p' tr, proc_step tid
                         (Exec (Call op) p', s, tr)
                         (p', s', tr ++ add_id tid evs)
  .

  Notation threads := (threads_state (proc Op)).
  Implicit Types (ts:threads).

  Inductive exec_at tid : Relation (threads * State * trace) :=
  | exec_proc : forall ts p p',
      ts tid = Some p ->
      forall s s' tr tr',
        proc_step tid (p, s, tr) (p', s', tr') ->
        exec_at tid (ts, s, tr) (ts [[tid := p']], s', tr')
  | exec_atomic : forall ts p p',
      ts tid = Some (Exec (Atomic p) p') ->
      forall s s' tr tr',
        kleene_star (proc_step tid) (p, s, tr) (Ret, s', tr') ->
        exec_at tid (ts, s, tr) (ts [[tid := p']], s', tr')
  | exec_spawn : forall ts p p',
      ts tid = Some (Exec (Spawn p) p') ->
      forall tid',
        tid <> tid' ->
        ts tid' = None ->
        forall s tr, exec_at tid (ts, s, tr) (ts [[tid := p']] [[tid' := p]], s, tr)
  | exec_terminate : forall ts op p,
      ts tid = Some (Ret) ->
      forall s tr, exec_at tid (ts, s, tr) (ts [[-tid]], s, tr)
  .

  Definition exec_step : Relation (threads * State * trace) :=
    fun '(ts, s, tr) '(ts', s', tr') =>
      exists tid, exec_at tid (ts, s, tr) (ts', s', tr').

  Theorem thread_upd_aba_ba : forall ts tid tid' p1 p2 p3,
      ts [[tid := p1]] [[tid' := p2]] [[tid := p3]] =
      ts [[tid' := p2]] [[tid := p3]].
  Proof.
    intros.
    cmp_ts tid tid'.
    rewrite thread_upd_ne_comm with (tid:=tid) (tid':=tid') by auto;
      autorewrite with t;
      auto.
  Qed.

  Theorem thread_upd_aba : forall ts tid tid' p1 p2 p3,
      tid <> tid' ->
      ts [[tid := p1]] [[tid' := p2]] [[tid := p3]] =
      ts [[tid := p3]] [[tid' := p2]].
  Proof.
    intros.
    rewrite thread_upd_aba_ba.
    rewrite thread_upd_ne_comm; auto.
  Qed.

  Hint Rewrite thread_upd_aba using solve [ auto ] : t.

  Hint Constructors exec_at.

  Theorem exec_step_inv : forall ts tid p s tr ts' s' tr',
      exec_step (ts [[tid := p]], s, tr) (ts', s', tr') ->
      exec_at tid (ts [[tid := p]], s, tr) (ts', s', tr') \/
      ts' tid = Some p.
  Proof.
    intros.
    intuition eauto.
    unfold exec_step in H; propositional.
    cmp_ts tid tid0; eauto.
    right.
    invert H; autorewrite with t in *; eauto.
    cmp_ts tid tid'.
  Qed.

  Theorem exec_step_inv' : forall ts tid p s tr ts' s' tr',
      exec_step (ts [[tid := p]], s, tr) (ts', s', tr') ->
      exec_at tid (ts [[tid := p]], s, tr) (ts', s', tr') \/
      exists tid', tid <> tid' /\
              exec_at tid' (ts [[tid := p]], s, tr) (ts' [[tid := p]], s', tr').
  Proof.
    intros.
    intuition eauto.
    unfold exec_step in H; propositional.
    cmp_ts tid tid0; eauto.
    right; exists tid0; intuition eauto.
    invert H; autorewrite with t in *; eauto.
    - cmp_ts tid tid'.
      rewrite thread_upd_same_eq with
        (ts:=ts [[tid := p]] [[tid0 := p']] [[tid' := p0]]);
        autorewrite with t;
        auto.
    - rewrite thread_upd_ne_comm with (tid := tid0) (tid' := tid) by auto;
        autorewrite with t;
        eauto.
  Qed.

  Definition exec := kleene_star exec_step.

  Theorem proc_step_prepend : forall tid tr0,
      Proper (proc_step tid ==> proc_step tid) (set etrace (app tr0)).
  Proof.
    unfold Proper, "==>"; intros.
    cbv [set Set_etrace]; destruct matches; subst.
    invert H.
    rewrite app_assoc; eauto using proc_step.
  Qed.

  Theorem kleene_star_proper : forall A (R: Relation A) (f: A -> A),
      Proper (R ==> R) f ->
      Proper (kleene_star R ==> kleene_star R) f.
  Proof.
    unfold Proper, "==>"; intros.
    induction H0; eauto using kleene_star.
  Qed.

  Theorem proc_step_star_prepend : forall tid tr0,
      Proper (kleene_star (proc_step tid) ==> kleene_star (proc_step tid))
             (set etrace (app tr0)).
  Proof.
    intros.
    apply kleene_star_proper.
    apply proc_step_prepend.
  Qed.

  Theorem exec_tr_prepend : forall tr0,
      Proper (exec_step ==> exec_step) (set etrace (app tr0)).
  Proof.
    unfold Proper, "==>"; intros.
    cbv [set Set_etrace]; destruct matches; subst.
    unfold exec_step in *; propositional.
    exists tid.
    invert H; eauto using exec_at.
    eapply exec_proc; eauto.
    apply (proc_step_prepend tr0) in H7; simpl in *; eauto.
    apply (proc_step_star_prepend tr0) in H7; simpl in *; eauto.
  Qed.

  Open Scope rel.

  Ltac destruct_ss x :=
    let ts := fresh "ts" in
    let s := fresh "s" in
    let tr := fresh "tr" in
    destruct x as ((ts & s) & tr).

  Definition exec_not_at tid :=
    fun ss ss' => exists tid', tid <> tid' /\ exec_at tid' ss ss'.

  Lemma exec_not_at_exec_step : forall tid,
      exec_not_at tid ---> exec_step.
  Proof.
    unfold exec_not_at, exec_step, "--->"; propositional.
    destruct_ss x.
    destruct_ss y.
    eauto.
  Qed.

  Lemma exec_at_exec_step : forall tid,
      exec_at tid ---> exec_step.
  Proof.
    unfold exec_step, "--->"; intros.
    destruct matches; subst; eauto.
  Qed.

  Lemma exec_step_split : forall tid,
      exec_step ---> exec_at tid +++ exec_not_at tid.
  Proof.
    unfold exec_step, exec_not_at, "--->", "+++"; propositional.
    destruct_ss x.
    destruct_ss y.
    propositional.
    cmp_ts tid tid0; eauto.
  Qed.

  Theorem exec_split_tid' : forall tid,
      kleene_star (exec_not_at tid) ?>
                  exec_at tid >>
                  kleene_star exec_step --->
                  kleene_star exec_step.
  Proof.
    intros.
    rewrite exec_not_at_exec_step.
    rewrite exec_at_exec_step.
    rewrite (kleene_star_one exec_step) at 2.
    setoid_rewrite kleene_star_dup_next at 4.
    apply next_cancel_l.
    setoid_rewrite kleene_star_dup at 3.
    reflexivity.
  Qed.

  Theorem exec_split_tid : forall tid,
      kleene_star exec_step --->
           kleene_star (exec_not_at tid) ?>
           exec_at tid >>
           kleene_star exec_step.
  Proof.
    unfold exec; intros.
    apply star_ind.
    - rewrite <- next_intro1.
      rewrite star_intro1.
      reflexivity.
    - rewrite (exec_step_split tid) at 1.
      rewrite <- ?rel_plus_distr_app, <- ?rel_plus_distr_next.
      apply rel_plus_elim.
      + rewrite exec_split_tid' at 1.
        rewrite <- next_intro2.
        setoid_rewrite <- star_intro1 at 2.
        rewrite noop_seq_l.
        reflexivity.
      + rewrite app_next_assoc.
        rewrite star_intro2.
        reflexivity.
  Qed.

  Theorem exec_not_proc : forall tid p,
      invariant
        (fun '(ts, _, _) => thread_get ts tid = Some p)
        (kleene_star (exec_not_at tid)).
  Proof.
    intros.
    apply invariant_star.
    unfold invariant, exec_not_at; intros.
    destruct_ss x1.
    destruct_ss x2.
    propositional.
    invert H1; autorewrite with t; eauto.
    cmp_ts tid tid'0; congruence.
  Qed.

  Definition add_proc tid p (ss: threads * State * trace) : threads * State * trace :=
    let '(ts, s, tr) := ss in (ts [[tid := p]], s, tr).

  Ltac cleanup_ts :=
    repeat match goal with
           | [ H: match _ with
                  | Build_threads_state get _ _ => get
                  end = match _ with
                        | Build_threads_state get' _ _ => get'
                        end |- _ ] =>
             apply thread_get_eq in H
           | [ H: match _ with
                  | @Build_threads_state _ _ m _ _ => m
                  end = match _ with
                        | @Build_threads_state _ _ m' _ _ => m'
                        end |- _ ] =>
             clear H
           end.

  Lemma equal_ts tid : forall ts ts',
      ts = ts' ->
      thread_get ts tid = thread_get ts' tid.
  Proof.
    congruence.
  Qed.

  Lemma thread_change_upd:
    forall (ts ts' : threads) tid p p' tid',
      tid <> tid' ->
      forall p2 : proc Op,
        ts [[tid := p]] [[tid' := p2]] = ts' [[tid := p]] ->
        ts' [[tid := p']] = ts [[tid := p']] [[tid' := p2]].
  Proof.
    intros.
    symmetry.
    eapply thread_ext_eq; intros.
    apply (equal_ts tid0) in H0.
    cmp_ts tid' tid0.
    cmp_ts tid tid0.
  Qed.

  Lemma thread_spawn_change_upd:
    forall (ts ts' : threads) tid p p' tid' tid'',
      tid <> tid' ->
      tid <> tid'' ->
      forall p2 p3 : proc Op,
        ts [[tid := p]] [[tid' := p2]] [[tid'' := p3]] = ts' [[tid := p]] ->
        ts' [[tid := p']] = ts [[tid := p']] [[tid' := p2]] [[tid'' := p3]].
  Proof.
    intros.
    symmetry.
    eapply thread_ext_eq; intros.
    apply (equal_ts tid0) in H1.
    cmp_ts tid'' tid0.
    cmp_ts tid' tid0.
    cmp_ts tid tid0.
  Qed.

  Theorem exec_not : forall tid p p',
      rel_apply (exec_not_at tid)
                (add_proc tid p)
                (add_proc tid p) --->
                rel_apply (exec_not_at tid)
                (add_proc tid p')
                (add_proc tid p').
  Proof.
    intros.
    unfold rel_apply, "--->", exec_not_at; propositional.
    exists tid'; intuition eauto.
    destruct_ss x.
    destruct_ss y.
    cbn [add_proc] in *.

    invert H0; cleanup_ts; autorewrite with t in *.
    - erewrite (thread_change_upd _ ltac:(eauto) H5).
      eapply exec_proc; autorewrite with t; eauto.
    - erewrite (thread_change_upd _ ltac:(eauto) H5).
      eapply exec_atomic; autorewrite with t; eauto.
    - cmp_ts tid tid'0.
      erewrite (thread_spawn_change_upd _ _ _ H4).
      eapply exec_spawn; autorewrite with t; eauto.
    - admit.
  Admitted.

End Execution.

Local Notation proc_step_pat := (proc_step _ _ _ _).

Tactic Notation "check_pat" uconstr(pat) :=
  let x := constr:(ltac:(tryif assert_succeeds refine pat
                          then exact True
                          else refine pat) : Prop) in idtac.

Goal True. check_pat proc_step_pat. Abort.

Ltac inv_proc_step :=
  match goal with
  | [ H: proc_step_pat |- _ ] =>
    invert H
  end.
