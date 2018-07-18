Require Import Spec.ConcurExec.
Require Import Spec.Equiv.
Require Import ProofAutomation.
Require Import Helpers.Instances.
Require Import Helpers.FinMap.

Require Import Omega.

(** Helpers for connecting different [threads_state]s *)

Definition proc_match `(R : forall T, proc Op T -> proc Op' T -> Prop)
                      `(ts1 : threads_state Op)
                      `(ts2 : threads_state Op') :=
  forall tid,
    match ts1 tid with
    | Proc p1 =>
      (* needs to be an exists since need type of ts2 tid to be T *)
      exists p2, ts2 tid = Proc p2 /\
            R _ p1 p2
    | NoProc => ts2 tid = NoProc
    end.

Theorem proc_match_sym : forall `(R : forall T, proc Op T -> proc Op' T -> Prop)
                           ts1 ts2,
    proc_match R ts1 ts2 ->
    proc_match (fun T x y => R T y x) ts2 ts1.
Proof.
  unfold proc_match; intros.
  specialize (H tid).
  destruct_with_eqn (ts1 tid); propositional;
    replace (ts2 tid);
    eauto.
Qed.

Theorem proc_match_subrelation : forall Op Op'
                                   (R1 R2: forall T, proc Op T -> proc Op' T -> Prop)
                                   ts1 ts2,
    proc_match R1 ts1 ts2 ->
    (forall T p1 p2, R1 T p1 p2 -> R2 T p1 p2) ->
    proc_match R2 ts1 ts2.
Proof.
  unfold proc_match; intros.
  specialize (H tid); destruct matches in *; propositional; eauto.
Qed.

Theorem proc_match_max_eq : forall `(R : forall T, proc Op T -> proc Op' T -> Prop)
                           ts1 ts2,
    proc_match R ts1 ts2 ->
    thread_max ts1 = thread_max ts2.
Proof.
  intros.
  apply thread_max_eq; intros.
  specialize (H tid).
  destruct_with_eqn (ts1 tid); propositional;
    (intuition auto);
    congruence.
Qed.

Lemma proc_match_del : forall `(ts1 : threads_state Op)
                              `(ts2 : threads_state Op') R tid,
  proc_match R ts1 ts2 ->
  proc_match R (ts1 [[ tid := NoProc ]]) (ts2 [[ tid := NoProc ]]).
Proof.
  unfold proc_match; intros.
  specialize (H tid0).
  destruct (tid == tid0); subst;
    autorewrite with t; eauto.
Qed.

Lemma proc_match_upd : forall `(ts1 : threads_state Op)
                              `(ts2 : threads_state Op') R tid
                              T (p1 : proc _ T) p2,
  proc_match R ts1 ts2 ->
  R _ p1 p2 ->
  proc_match R (ts1 [[ tid := Proc p1 ]]) (ts2 [[ tid := Proc p2 ]]).
Proof.
  unfold proc_match; intros.
  specialize (H tid0).
  destruct (tid == tid0); subst;
    autorewrite with t;
    eauto.
Qed.

Lemma proc_match_nil : forall `(R : forall T, proc Op T -> proc Op' T -> Prop),
  proc_match R thread_empty thread_empty.
Proof.
  unfold proc_match; intros.
  rewrite ?empty_is_empty; eauto.
Qed.

Theorem proc_match_pick : forall tid `(ts1 : threads_state Op)
                                     `(ts2 : threads_state Op') R,
  proc_match R ts1 ts2 ->
    (ts1 [[ tid ]] = NoProc /\ ts2 [[ tid ]] = NoProc) \/
    exists T (p1 : proc _ T) p2,
    ts1 [[ tid ]] = Proc p1 /\ ts2 [[ tid ]] = Proc p2 /\ R T p1 p2.
Proof.
  unfold proc_match; intros.
  specialize (H tid).
  destruct_with_eqn (ts1 tid); propositional; eauto 10.
Qed.

Theorem proc_match_trans : forall `(ts1: threads_state Op)
                            `(ts2: threads_state Op') R1
                            `(ts3: threads_state Op'') R2,
  proc_match R1 ts1 ts2 ->
  proc_match R2 ts2 ts3 ->
  proc_match (fun T x z => exists y, R1 T x y /\ R2 T y z)  ts1 ts3.
Proof.
  unfold proc_match; intros.
  specialize (H tid).
  specialize (H0 tid).
  destruct matches in *;
    propositional;
    repeat simpl_match; repeat maybe_proc_inv; eauto 10.
Qed.

Theorem proc_match_map : forall `(ts1: threads_state Op)
                           `(f: forall T, proc Op T -> proc Op' T),
    proc_match (fun T p1 p2 => p2 = f T p1) ts1 (thread_map f ts1).
Proof.
  unfold proc_match; intros.
  rewrite thread_map_get_match.
  destruct matches; propositional; repeat simpl_match; eauto.
Qed.

Theorem proc_match_map1 : forall `(ts1: threads_state Op)
                            `(f: forall T, proc Op T -> proc Op' T)
                            `(ts2: threads_state Op'') R,
    proc_match (fun T p1 p2 => R T (f T p1) p2) ts1 ts2 ->
    proc_match R (thread_map f ts1) ts2.
Proof.
  intros.
  unfold proc_match; intros.
  rewrite thread_map_get_match.
  specialize (H tid).
  destruct matches; propositional; repeat simpl_match; eauto.
Qed.

Theorem proc_match_map2 : forall `(ts1: threads_state Op)
                            `(f: forall T, proc Op' T -> proc Op'' T)
                            `(ts2: threads_state Op') R,
    proc_match (fun T p1 p2 => R T p1 (f T p2)) ts1 ts2 ->
    proc_match R ts1 (thread_map f ts2).
Proof.
  intros.
  unfold proc_match; intros.
  rewrite thread_map_get_match.
  specialize (H tid).
  destruct_with_eqn (ts1 tid); propositional; repeat simpl_match; eauto.
Qed.

(** proving equivalence based on per-process equivalence *)

Fixpoint take_threads Op (src: threads_state Op) n (dst: threads_state Op) :=
  match n with
  | 0 => dst
  | S n => (take_threads src n dst) [[ n := src n ]]
  end.

Lemma take_threads_complete_helper : forall Op (src dst: threads_state Op) n tid,
    tid < n ->
    take_threads src n dst tid = src tid.
Proof.
  induction n; simpl; intros.
  - exfalso; omega.
  - destruct (tid == n); subst;
      autorewrite with t;
      eauto.
    apply IHn; omega.
Qed.

Lemma take_threads_unchanged_helper : forall Op (src dst: threads_state Op) n tid,
    tid >= n ->
    take_threads src n dst tid = dst tid.
Proof.
  induction n; simpl; intros; auto.
  destruct (tid == n); subst;
    autorewrite with t.
  exfalso; omega.
  apply IHn; omega.
Qed.

Theorem take_threads_max : forall Op (src dst: threads_state Op) n,
    n <= thread_max dst ->
    thread_max (take_threads src n dst) <= thread_max dst.
Proof.
  induction n; simpl; intros.
  auto.
  specialize (IHn ltac:(omega)).
  destruct (le_dec n (thread_max (take_threads src n dst))).
  rewrite thread_upd_thread_max_bound; auto.
  rewrite thread_upd_thread_max_extend_bound; omega.
Qed.

Lemma take_threads_complete_general : forall Op (src dst: threads_state Op) n,
    n > thread_max src ->
    thread_max dst <= thread_max src ->
    take_threads src n dst = src.
Proof.
  intros.
  apply thread_ext_eq; intros.
  destruct (lt_dec tid n).
  apply take_threads_complete_helper; auto.
  rewrite take_threads_unchanged_helper by omega.
  rewrite ?mapping_finite by omega.
  reflexivity.
Qed.

Theorem take_threads_complete : forall Op (src dst: threads_state Op),
    thread_max src = thread_max dst ->
    src = take_threads src (1 + thread_max src) dst.
Proof.
  intros.
  rewrite take_threads_complete_general; auto; omega.
Qed.

Lemma take_threads_none : forall Op (src dst: threads_state Op),
    dst = take_threads src 0 dst.
Proof.
  reflexivity.
Qed.

Theorem trace_incl_ts_general : forall Op State (op_step: OpSemantics Op State) (ts1 ts2: threads_state _),
    (forall tid ts,
        trace_incl_ts op_step
                      (ts [[ tid := ts1 tid ]])
                      (ts [[ tid := ts2 tid ]])) ->
    thread_max ts1 = thread_max ts2 ->
    trace_incl_ts op_step ts1 ts2.
Proof.
  intros.
  rewrite (take_threads_complete ts2 ts1) by auto.
  generalize dependent (1 + thread_max ts2).
  induction n; simpl.
  reflexivity.
  etransitivity; eauto.
  replace (take_threads ts2 n ts1) with
      ((take_threads ts2 n ts1) [[n := ts1 n]]) at 1;
    swap 1 2.
  rewrite thread_upd_same_eq; auto.
  rewrite take_threads_unchanged_helper; auto.
  generalize dependent (take_threads ts2 n ts1); intros ts' **.
  apply H.
Qed.

Theorem trace_incl_ts_proc_match : forall Op State (op_step: OpSemantics Op State) ts1 ts2,
    proc_match (fun T => trace_incl op_step (T:=T)) ts1 ts2 ->
    trace_incl_ts op_step ts1 ts2.
Proof.
  intros.
  apply trace_incl_ts_general.
  - intros.
    unfold trace_incl in *.
    specialize (H tid).
    destruct_with_eqn (ts1 tid); propositional; try congruence.
    rewrite H in *; auto.
  - eauto using proc_match_max_eq.
Qed.

Inductive proc_optR Op Op' (R: forall T, proc Op T -> proc Op' T -> Prop) :
  maybe_proc Op -> maybe_proc Op' -> Prop :=
| ProcOptR : forall T p1 p2, R T p1 p2 -> proc_optR R (Proc p1) (Proc p2)
| ProcOptR_NoProc : proc_optR R NoProc NoProc.

Hint Constructors proc_optR.

Theorem proc_match_upd_opt : forall `(ts1: threads_state Op) `(ts2: threads_state Op')
                               R tid p1 p2,
    proc_match R ts1 ts2 ->
    proc_optR R p1 p2 ->
    proc_match R (ts1 [[tid := p1]]) (ts2 [[tid := p2]]).
Proof.
  intros.
  invert H0.
  auto using proc_match_upd.
  auto using proc_match_del.
Qed.
