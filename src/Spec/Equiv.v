Require Import ConcurProc.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import List.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Matching traces *)

Inductive traces_match {opLoT opMidT opHiT} :
  forall (t1 : trace opLoT opMidT)
         (t2 : trace opMidT opHiT), Prop :=

| MatchLo : forall t1 t2 tid e,
  traces_match t1 t2 ->
  traces_match (TraceEvent tid (EvLow e) t1) t2

| MatchInvokeMid : forall t1 t2 tid e,
  traces_match t1 t2 ->
  traces_match (TraceEvent tid (EvHigh e) t1)
               (TraceEvent tid (EvLow e) t2)

| MatchInvokeHi : forall t1 t2 tid e,
  traces_match t1 t2 ->
  traces_match t1 (TraceEvent tid (EvHigh e) t2)

| MatchEmpty :
  traces_match TraceEmpty TraceEmpty.

Hint Constructors traces_match.


Fixpoint trace_filter_hi `(t : trace opLoT opHiT) : trace opLoT opHiT :=
  match t with
  | TraceEmpty => TraceEmpty
  | TraceEvent tid e t' =>
    match e with
    | EvLow _ => trace_filter_hi t'
    | EvHigh _ => TraceEvent tid e (trace_filter_hi t')
    end
  end.

Definition trace_match_hi {opLoT opHiT} (t1 t2 : trace opLoT opHiT) :=
  trace_filter_hi t1 = trace_filter_hi t2.

Instance trace_match_hi_equiv :
  Equivalence (@trace_match_hi opLoT opHiT).
Proof.
  split.
  - firstorder.
  - unfold trace_match_hi, Symmetric; intros.
    symmetry; eauto.
  - unfold trace_match_hi, Transitive; intros.
    congruence.
Qed.

Lemma trace_match_hi_prepend : forall `(evs : list (event opT opHiT)) tr0 tr1 tid,
  trace_match_hi tr0 tr1 ->
  trace_match_hi (prepend tid evs tr0) (prepend tid evs tr1).
Proof.
  unfold trace_match_hi.
  induction evs; simpl; intros; eauto.
  destruct a; eauto.
  erewrite IHevs; eauto.
Qed.

Hint Resolve trace_match_hi_prepend.


Lemma trace_match_hi_drop_lo_l : forall opT opHiT e (tr1 tr2 : trace opT opHiT) tid,
  trace_match_hi tr1 tr2 ->
  trace_match_hi (TraceEvent tid (EvLow e) tr1) tr2.
Proof.
  unfold trace_match_hi; simpl; eauto.
Qed.

Lemma trace_match_hi_drop_lo_r : forall opLoT opHiT e (tr1 tr2 : trace opLoT opHiT) tid,
  trace_match_hi tr1 tr2 ->
  trace_match_hi tr1 (TraceEvent tid (EvLow e) tr2).
Proof.
  unfold trace_match_hi; simpl; eauto.
Qed.

Lemma trace_match_hi_refl : forall `(tr : trace opT opHiT),
  trace_match_hi tr tr.
Proof.
  reflexivity.
Qed.

Hint Resolve trace_match_hi_drop_lo_l.
Hint Resolve trace_match_hi_drop_lo_r.
Hint Resolve trace_match_hi_refl.

Instance traces_match_proper :
  Proper (trace_match_hi ==> eq ==> iff) (@traces_match opLoT opMidT opHiT).
Proof.
  intros.
  intros t1 t2 H12.
  intros t3' t3 H; subst.
  split; intros.
  - generalize dependent t2.
    induction H; simpl; intros; eauto.
    + induction t0; simpl; intros.
      * destruct ev.
        constructor. eauto.
        inversion H12; subst.
        constructor. eauto.
      * inversion H12.
    + induction t2; simpl; intros; eauto.
      destruct ev.
      constructor. eauto.
      inversion H12.
  - generalize dependent t1.
    induction H; simpl; intros; eauto.
    + induction t0; simpl; intros.
      * destruct ev.
        constructor. eauto.
        inversion H12; subst.
        constructor. eauto.
      * inversion H12.
    + induction t1; simpl; intros; eauto.
      destruct ev.
      constructor. eauto.
      inversion H12.
Qed.


(** A strong notion of execution equivalence, independent of semantics *)

Definition exec_equiv_ts {opT opHiT} (ts1 ts2 : @threads_state opT opHiT) :=
  forall State op_step (s : State) tr,
    exec op_step s ts1 tr <->
    exec op_step s ts2 tr.

Definition exec_equiv_opt `(p1 : maybe_proc opT opHiT) p2 :=
  forall (ts : threads_state) tid,
    exec_equiv_ts (ts [[ tid := p1 ]]) (ts [[ tid := p2 ]]).

Definition exec_equiv `(p1 : proc opT opHiT T) (p2 : proc _ _ T) :=
  exec_equiv_opt (Proc p1) (Proc p2).

Instance exec_equiv_ts_equivalence :
  Equivalence (@exec_equiv_ts opLoT opHiT).
Proof.
  split.
  - firstorder.
  - unfold Symmetric, exec_equiv_ts; intros.
    split; intros; apply H; eauto.
  - unfold Transitive, exec_equiv_ts; intros.
    split; intros.
    + apply H0. apply H. eauto.
    + apply H. apply H0. eauto.
Qed.

Theorem exec_equiv_ts_app_None : forall `(ts : @threads_state opT opHiT),
  exec_equiv_ts ts (ts ++ [NoProc]).
Proof.
  split; intros.
  - induction H.
    + eapply ExecOne with (tid := tid); eauto.
      eapply thread_get_app_NoProc in H; eauto.
      erewrite <- thread_upd_app_NoProc; eauto.
    + eapply ExecEmpty.
      eapply no_runnable_threads_app_NoProc in H; eauto.
  - remember (ts ++ [NoProc]); generalize dependent ts;
      induction H; intros; subst.
    + eapply ExecOne with (tid := tid); eauto.
      eapply thread_get_app_NoProc; eauto.
      eapply IHexec.
      erewrite thread_upd_app_NoProc; eauto.
      eapply thread_get_app_NoProc in H. eauto.
    + eapply ExecEmpty.
      eapply no_runnable_threads_app_NoProc; eauto.
Qed.

Theorem exec_equiv_ts_pad : forall n `(ts : @threads_state opT opHiT),
  exec_equiv_ts ts (pad ts n NoProc).
Proof.
  intros.
  rewrite pad_is_append.
  generalize (n - length ts); intros.
  rewrite <- rev_repeat.
  induction n0; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc.
    etransitivity.
    2: eapply exec_equiv_ts_app_None.
    eauto.
Qed.

Instance exec_equiv_opt_equivalence :
  Equivalence (@exec_equiv_opt opLoT opHiT).
Proof.
  split.
  - unfold exec_equiv_opt, Reflexive; intros.
    reflexivity.
  - unfold exec_equiv_opt, Symmetric; intros.
    symmetry. eauto.
  - intros t1 t2 t3.
    unfold exec_equiv; split; intros.
    + eapply H in H1; eauto.
      eapply H0 in H1.
      eauto.
    + eapply H; eauto.
      eapply H0; eauto.
Qed.

Instance exec_equiv_equivalence :
  Equivalence (@exec_equiv opLoT opHiT T).
Proof.
  unfold exec_equiv.
  split.
  - intro t.
    reflexivity.
  - unfold Symmetric, exec_equiv_opt; intros.
    symmetry. eauto.
  - unfold Transitive; intros.
    etransitivity; eauto.
Qed.

Instance thread_upd_exec_equiv_proper :
  Proper (eq ==> eq ==> exec_equiv_opt ==> exec_equiv_ts) (@thread_upd opT opHiT).
Proof.
  intros.
  intros ts0 ts1 H; subst.
  intros tid tid' H'; subst.
  intros o0 o1 H'.

  unfold exec_equiv_ts; split; intros.
  - apply H'; eauto.
  - apply H'; eauto.
Qed.

Instance Proc_exec_equiv_proper :
  Proper (exec_equiv ==> exec_equiv_opt) (@Proc opT opHiT T).
Proof.
  intros.
  unfold exec_equiv.
  intros ts0 ts1 H; subst.
  eauto.
Qed.

Theorem exec_equiv_ret_bind : forall `(v : T) `(p : T -> proc opT opHiT T'),
  exec_equiv (Bind (Ret v) p) (p v).
Proof.
  split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst; autorewrite with t in *.
      * repeat maybe_proc_inv; repeat exec_tid_inv.
        simpl. eauto.

      * eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by eauto.
        eapply IHexec.
        rewrite thread_upd_upd_ne; eauto.
    + exfalso; eapply thread_upd_not_empty; eauto.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * autorewrite with t in *.
        repeat maybe_proc_inv.
        rewrite <- app_nil_l with (l := evs).
        rewrite prepend_app.
        eapply ExecOne with (tid := tid).
          autorewrite with t; eauto.
          eauto.
          autorewrite with t.
        eapply ExecOne with (tid := tid).
          autorewrite with t; eauto.
          eauto.
          autorewrite with t.
        eauto.

      * eapply ExecOne with (tid := tid0).
          autorewrite with t in *; eauto.
          eauto.
          rewrite thread_upd_upd_ne by eauto.
        eapply IHexec.
        rewrite thread_upd_upd_ne by auto.
        eauto.

    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.
Qed.

Theorem exec_equiv_ret_None : forall opT opHiT `(v : T),
  @exec_equiv_opt opT opHiT (Proc (Ret v)) NoProc.
Proof.
  split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * autorewrite with t in *.
        repeat maybe_proc_inv.
        repeat exec_tid_inv.
        simpl. eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.

  - replace tr with (prepend tid nil tr) by reflexivity.
    eapply ExecOne with (tid := tid).
      rewrite thread_upd_eq. eauto.
      eauto.
    autorewrite with t.
    eauto.
Qed.

Theorem exec_equiv_bind_ret : forall `(p : proc opT opHiT T),
  exec_equiv (Bind p Ret) p.
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * autorewrite with t in *.
        repeat maybe_proc_inv.
        exec_tid_inv.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq in * by auto. eauto.
          eauto.
        autorewrite with t.

        destruct result0; eauto.

        eapply exec_equiv_ret_None in H1.
        eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * autorewrite with t in *.
        repeat maybe_proc_inv.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t in *.
        destruct result; eauto.
        apply exec_equiv_ret_None; eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.
Qed.

Theorem exec_equiv_bind_bind : forall `(p1 : proc opT opHiT T1) `(p2 : T1 -> proc opT opHiT T2) `(p3 : T2 -> proc opT opHiT T3),
  exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * autorewrite with t in *.
        repeat maybe_proc_inv.
        exec_tid_inv.
        exec_tid_inv.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.

        destruct result; eauto.

      * eapply ExecOne with (tid := tid0).
          autorewrite with t in *; eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eapply IHexec.
        rewrite thread_upd_upd_ne; eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * autorewrite with t in *.
        repeat maybe_proc_inv.
        exec_tid_inv.

        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.

        destruct result0; eauto.

      * rewrite thread_upd_upd_ne in * by eauto.
        eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eauto.
    + specialize (H tid).
      rewrite thread_upd_eq in H.
      congruence.
Qed.

Theorem exec_equiv_bind_a : forall `(p : proc opT opHiT T) `(p1 : T -> proc _ _ T') p2,
  (forall x, exec_equiv (p1 x) (p2 x)) ->
  exec_equiv (Bind p p1) (Bind p p2).
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * autorewrite with t in *.
        repeat maybe_proc_inv.
        exec_tid_inv.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.

        destruct result0; eauto.
        eapply H in H2; eauto.

      * eapply ExecOne with (tid := tid0).
          autorewrite with t in *; eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eapply IHexec.
        rewrite thread_upd_upd_ne; eauto.
    + exfalso; eauto.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst.
      * autorewrite with t in *.
        repeat maybe_proc_inv.
        exec_tid_inv.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.

        destruct result0; eauto.
        eapply H in H2; eauto.

      * eapply ExecOne with (tid := tid0).
          autorewrite with t in *; eauto.
          eauto.
        rewrite thread_upd_upd_ne by auto.
        eapply IHexec.
        rewrite thread_upd_upd_ne; eauto.
    + exfalso; eauto.
Qed.

Theorem exec_equiv_bind_bind' : forall `(p1 : proc opT opHiT T1) `(p2 : T1 -> proc _ _ T2) `(p3 : T1 -> T2 -> proc _ _ T3),
  exec_equiv (Bind p1 (fun x => Bind (p2 x) (p3 x)))
             (Bind (Bind p1 (fun x => Bind (p2 x) (fun y => Ret (x, y))))
                   (fun p => p3 (fst p) (snd p))).
Proof.
  intros.
  rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  rewrite exec_equiv_ret_bind; simpl.
  reflexivity.
Qed.

Instance Bind_exec_equiv_proper_2 :
  Proper (eq ==>
          pointwise_relation T0 exec_equiv ==>
          @exec_equiv opT opHiT T) Bind.
Proof.
  intros.
  intros p1a p1b H1; subst.
  intros p2a p2b H2.
  eapply exec_equiv_bind_a; intros.
  eapply H2.
Qed.


(** Trace inclusion for an entire threads_state *)

Definition hitrace_incl_ts_s {opLo opHi State} op_step (s s' : State) (ts1 ts2 : @threads_state opLo opHi) :=
  forall tr,
    exec op_step s ts1 tr ->
    exists tr', exec op_step s' ts2 tr' /\
      trace_match_hi tr tr'.

Definition hitrace_incl_ts {opLo opHi State} op_step (s : State) (ts1 ts2 : @threads_state opLo opHi) :=
  hitrace_incl_ts_s op_step s s ts1 ts2.

Instance hitrace_incl_ts_preorder {opT opHiT State op_step s} :
  PreOrder (@hitrace_incl_ts opT opHiT State op_step s).
Proof.
  split.
  - unfold Reflexive.
    unfold hitrace_incl_ts, hitrace_incl_ts_s; intros.
    eexists; intuition eauto.
  - unfold Transitive.
    unfold hitrace_incl_ts, hitrace_incl_ts_s; intros.
    eapply H in H1. deex.
    eapply H0 in H1. deex.
    eexists; intuition eauto.
    etransitivity; eauto.
Qed.


(** Trace inclusion for a single thread *)

Definition hitrace_incl_s `(s : State) s' tid `(op_step : OpSemantics opT State) `(p1 : proc opT opHiT T) (p2 : proc _ _ T) :=
  forall ts,
    hitrace_incl_ts_s op_step s s'
      (ts [[ tid := Proc p1 ]])
      (ts [[ tid := Proc p2 ]]).

Definition hitrace_incl_opt {opT opHiT} `(op_step : OpSemantics opT State) p1 p2 :=
  forall (ts : @threads_state opT opHiT) s tid,
    hitrace_incl_ts op_step s
      (ts [[ tid := p1 ]])
      (ts [[ tid := p2 ]]).

Definition hitrace_incl {opT opHiT T} `(op_step : OpSemantics opT State) (p1 p2 : proc opT opHiT T) :=
  hitrace_incl_opt op_step (Proc p1) (Proc p2).


Instance hitrace_incl_opt_preorder :
  PreOrder (@hitrace_incl_opt opT opHiT State op_step).
Proof.
  split.
  - unfold Reflexive; intros.
    unfold hitrace_incl_opt; intros.
    reflexivity.
  - unfold Transitive; intros.
    unfold hitrace_incl_opt; intros.
    etransitivity; eauto.
Qed.

Instance hitrace_incl_preorder :
  PreOrder (@hitrace_incl opT opHiT T State op_step).
Proof.
  split.
  - unfold Reflexive; intros.
    unfold hitrace_incl; intros.
    reflexivity.
  - unfold Transitive; intros.
    unfold hitrace_incl; intros.
    etransitivity; eauto.
Qed.

Instance hitrace_incl_proper :
  Proper (Basics.flip (@hitrace_incl opT opHiT T State op_step) ==>
          @hitrace_incl opT opHiT T State op_step ==>
          Basics.impl) (@hitrace_incl opT opHiT T State op_step).
Proof.
  intros.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  repeat (etransitivity; eauto).
Qed.

Instance hitrace_incl_proper_flip :
  Proper (@hitrace_incl opT opHiT T State op_step ==>
          Basics.flip (@hitrace_incl opT opHiT T State op_step) ==>
          Basics.flip Basics.impl) (@hitrace_incl opT opHiT T State op_step).
Proof.
  intros.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  repeat (etransitivity; eauto).
Qed.

Instance hitrace_incl_s_proper :
  Proper (Basics.flip (@hitrace_incl opT opHiT T State op_step) ==>
          @hitrace_incl opT opHiT T State op_step ==>
          Basics.impl) (@hitrace_incl_s State s s' tid opT op_step opHiT T).
Proof.
  intros.
  intros p1 p2 H12 p3 p4 H34 H; subst.
  unfold hitrace_incl_s, hitrace_incl_ts_s; intros.
  apply H12 in H0. deex.
  apply H in H0. deex.
  apply H34 in H0. deex.
  eexists; split.
  eauto.
  repeat ( etransitivity; eauto ).
Qed.

Instance hitrace_incl_s_proper_flip :
  Proper (@hitrace_incl opT opHiT T State op_step ==>
          Basics.flip (@hitrace_incl opT opHiT T State op_step) ==>
          Basics.flip Basics.impl) (@hitrace_incl_s State s s' tid opT op_step opHiT T).
Proof.
  intros.
  intros p1 p2 H12 p3 p4 H34 H; subst.
  unfold hitrace_incl_s, hitrace_incl_ts_s; intros.
  apply H12 in H0. deex.
  apply H in H0. deex.
  apply H34 in H0. deex.
  eexists; split.
  eauto.
  repeat ( etransitivity; eauto ).
Qed.

Instance hitrace_incl_exec_equiv_proper :
  Proper (exec_equiv ==> exec_equiv ==> iff)
         (@hitrace_incl opT opHiT T State op_step).
Proof.
  intros p1 p1' ?.
  intros p2 p2' ?.
  split; intros.
  - unfold hitrace_incl, hitrace_incl_opt,
           hitrace_incl_ts, hitrace_incl_ts_s; intros.
    apply H in H2.
    apply H1 in H2.
    deex.
    apply H0 in H2.
    eauto.
  - unfold hitrace_incl, hitrace_incl_opt,
           hitrace_incl_ts, hitrace_incl_ts_s; intros.
    apply H in H2.
    apply H1 in H2.
    deex.
    apply H0 in H2.
    eauto.
Qed.

Instance hitrace_incl_s_exec_equiv_proper :
  Proper (exec_equiv ==> exec_equiv ==> iff)
         (@hitrace_incl_s State s s' tid opT op_step opHiT T).
Proof.
  intros.
  intros p1 p1' ?.
  intros p2 p2' ?.
  split; intros.
  - unfold hitrace_incl_s, hitrace_incl_ts_s; intros.
    apply H in H2.
    apply H1 in H2.
    deex.
    apply H0 in H2.
    eauto.
  - unfold hitrace_incl_s, hitrace_incl_ts_s; intros.
    apply H in H2.
    apply H1 in H2.
    deex.
    apply H0 in H2.
    eauto.
Qed.

Instance Proc_hitrace_incl_proper :
  Proper (@hitrace_incl opT opHiT T State op_step ==>
          @hitrace_incl_opt opT opHiT State op_step) (@Proc opT opHiT T).
Proof.
  intros.
  unfold exec_equiv.
  intros ts0 ts1 H; subst.
  eauto.
Qed.

Instance thread_upd_hitrace_incl_proper :
  Proper (eq ==> eq ==>
          @hitrace_incl_opt opT opHiT State op_step ==>
          hitrace_incl_ts op_step s) (@thread_upd opT opHiT).
Proof.
  intros.
  intros ts0 ts1 H; subst.
  intros tid tid' H; subst.
  intros p1 p2 H.

  unfold hitrace_incl_opt in H.
  eauto.
Qed.

Lemma hitrace_incl_opret :
  forall `(p : T -> proc opT opHiT T') (v : T) `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (OpRet v) p)
    (p v).
Proof.
  unfold hitrace_incl, hitrace_incl_opt,
         hitrace_incl_ts, hitrace_incl_ts_s.
  intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
    remember (thread_upd ts tid p);
    generalize dependent ts;
    induction H; intros; subst
  end.

  - destruct (tid == tid0); subst.
    + autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.

      eexists; split.
      eauto.
      constructor.

    + edestruct IHexec; intuition idtac.
      rewrite thread_upd_upd_ne; eauto.

      autorewrite with t in *.
      eexists; split.

      eapply ExecOne with (tid := tid0).
        autorewrite with t; eauto.
        eauto.
        rewrite thread_upd_upd_ne by assumption; eauto.
      eauto.

  - exfalso; eauto.
Qed.

Lemma hitrace_incl_opcall :
  forall `(p : unit -> proc opT opHiT T') `(op : opT T) `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (OpCall op) p)
    (p tt).
Proof.
  unfold hitrace_incl, hitrace_incl_opt,
         hitrace_incl_ts, hitrace_incl_ts_s.
  intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
    remember (thread_upd ts tid p);
    generalize dependent ts;
    induction H; intros; subst
  end.

  - destruct (tid == tid0); subst.
    + autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.

      eexists; intuition eauto.
      constructor.

    + edestruct IHexec; intuition idtac.
      rewrite thread_upd_upd_ne; eauto.

      autorewrite with t in *.
      eexists; split.

      eapply ExecOne with (tid := tid0).
        autorewrite with t; eauto.
        eauto.
        rewrite thread_upd_upd_ne; eauto.
      eauto.

  - exfalso; eauto.
Qed.

Theorem hitrace_incl_opexec :
  forall `(p : T -> proc opT opHiT T') op `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (OpExec op) p)
    (Bind (Atomic (Op op)) p).
Proof.
  unfold hitrace_incl, hitrace_incl_opt,
         hitrace_incl_ts, hitrace_incl_ts_s.
  intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
    remember (thread_upd ts tid p);
    generalize dependent ts;
    induction H; intros; subst
  end.

  - destruct (tid == tid0); subst.
    + autorewrite with t in *.
      repeat maybe_proc_inv.
      repeat exec_tid_inv.

      eexists; split.

      eapply ExecOne with (tid := tid0).
        autorewrite with t; eauto.
        eauto 20.
        autorewrite with t; eauto.

      simpl; eauto.

    + edestruct IHexec; intuition idtac.
      rewrite thread_upd_upd_ne; eauto.

      autorewrite with t in *.
      eexists; split.

      eapply ExecOne with (tid := tid0).
        autorewrite with t; eauto.
        eauto.
        rewrite thread_upd_upd_ne; eauto.
      eauto.

  - exfalso; eauto.
Qed.

Theorem hitrace_incl_bind_a : forall `(p : proc opT opHiT T) `(p2 : T -> proc _ _ T') p2' `(op_step : OpSemantics opT State),
  (forall x, hitrace_incl op_step (p2 x) (p2' x)) ->
  hitrace_incl op_step (Bind p p2) (Bind p p2').
Proof.
  unfold hitrace_incl, hitrace_incl_opt,
         hitrace_incl_ts, hitrace_incl_ts_s.
  intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?pp) _ |- _ =>
    remember (thread_upd ts tid pp);
    generalize dependent ts;
    generalize dependent p;
    induction H; intros; subst
  end.

  - destruct (tid0 == tid); subst.
    + autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      destruct result0.

      * edestruct H; eauto.
        intuition idtac.

        eexists; split.
        eapply ExecOne with (tid := tid).
          autorewrite with t; eauto.
          eauto.
          autorewrite with t; eauto.
        eauto.

      * edestruct IHexec; eauto.
        intuition idtac.

        eexists; split.
        eapply ExecOne with (tid := tid).
          autorewrite with t; eauto.
          eauto.
          autorewrite with t; eauto.
        eauto.

    + edestruct IHexec.
      rewrite thread_upd_upd_ne; eauto.
      intuition idtac.

      autorewrite with t in *.
      eexists; split.
      eapply ExecOne with (tid := tid0).
        autorewrite with t; eauto.
        eauto.
        rewrite thread_upd_upd_ne; eauto.
      eauto.
  - exfalso; eauto.
Qed.

Theorem hitrace_incl_bind : forall `(p1 : proc opT opHiT T1) p1' `(p2 : T1 -> proc _ _ T2) p2' `(op_step : OpSemantics opT State),
  (forall `(rx : _ -> proc _ _ T),
    hitrace_incl op_step (Bind p1 rx) (Bind p1' rx)) ->
  (forall `(rx : _ -> proc _ _ T) x,
    hitrace_incl op_step (Bind (p2 x) rx) (Bind (p2' x) rx)) ->
  forall `(rx : _ -> proc _ _ T),
    hitrace_incl op_step (Bind (Bind p1 p2) rx) (Bind (Bind p1' p2') rx).
Proof.
  intros.
  repeat rewrite exec_equiv_bind_bind.
  rewrite H.
  eapply hitrace_incl_bind_a.
  eauto.
Qed.

Instance Bind_hitrace_incl_proper_2 :
  Proper (eq ==>
          pointwise_relation T0 (@hitrace_incl opT opHiT T State op_step) ==>
          @hitrace_incl opT opHiT T State op_step) Bind.
Proof.
  intros.
  intros p1a p1b H1; subst.
  intros p2a p2b H2.
  eapply hitrace_incl_bind_a; intros.
  eapply H2.
Qed.

Theorem hitrace_incl_op :
  forall `(p : T -> proc opT opHiT T') op `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (Op op) p)
    (Bind (Atomic (Op op)) p).
Proof.
  intros.
  unfold Op at 1.
  rewrite exec_equiv_bind_bind.
  rewrite hitrace_incl_opcall.
  rewrite exec_equiv_bind_bind.
  rewrite hitrace_incl_opexec.
  eapply hitrace_incl_bind_a; intros.
  rewrite hitrace_incl_opret.
  reflexivity.
Qed.
