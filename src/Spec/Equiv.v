Require Import ConcurProc.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import List.
Require Import Omega.

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


Lemma traces_match_prepend : forall `(tr1 : trace opLoT opMidT) `(tr2 : trace opMidT opHiT) evs evs' tid,
  traces_match tr1 tr2 ->
  traces_match (prepend tid evs TraceEmpty) (prepend tid evs' TraceEmpty) ->
  traces_match (prepend tid evs tr1) (prepend tid evs' tr2).
Proof.
  intros.
  remember (prepend tid evs TraceEmpty).
  remember (prepend tid evs' TraceEmpty).
  generalize dependent evs'.
  generalize dependent evs.
  induction H0; intros.
  all: destruct evs; simpl in *.
  all: try inversion Heqt; subst.
  all: try constructor; eauto.

  all: destruct evs'; simpl in *.
  all: try inversion Heqt0; subst.
  all: try constructor; eauto.

  specialize (IHtraces_match nil); simpl in *; eauto.
  specialize (IHtraces_match ([e0] ++ evs)); simpl in *; eauto.
Qed.

Lemma trace_match_hi_prepend_empty : forall tid `(evs : list (event opT opHiT)) tr,
  trace_match_hi (prepend tid evs tr) TraceEmpty ->
  trace_match_hi (prepend tid evs TraceEmpty) TraceEmpty /\
  trace_match_hi tr TraceEmpty.
Proof.
  unfold trace_match_hi; induction evs; simpl in *; intros.
  - split; eauto.
  - destruct a.
    + specialize (IHevs tr). intuition.
    + inversion H.
Qed.


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

Definition exec_equiv_rx `(p1 : proc opT opHiT T) (p2 : proc _ _ T) :=
  forall TR (rx : T -> proc _ _ TR),
    exec_equiv (Bind p1 rx) (Bind p2 rx).

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

Instance exec_equiv_rx_equivalence :
  Equivalence (@exec_equiv_rx opLoT opHiT T).
Proof.
  unfold exec_equiv_rx.
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

Instance exec_equiv_rx_to_exec_equiv :
  subrelation (@exec_equiv_rx opT opHiT T) exec_equiv.
Proof.
  unfold subrelation, exec_equiv_rx; intros.
  rewrite <- exec_equiv_bind_ret with (p := x).
  rewrite <- exec_equiv_bind_ret with (p := y).
  eauto.
Qed.

Theorem exec_equiv_rx_proof_helper : forall `(p1 : proc opT opHiT T) p2,
  (forall tid `(s : State) s' op_step ts tr evs `(rx : _ -> proc _ _ TR) result,
    exec_tid op_step tid s (Bind p1 rx) s' result evs ->
    exec op_step s' (ts [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
    exec op_step s (ts [[tid := Proc (Bind p2 rx)]]) (prepend tid evs tr)) ->
  (forall tid `(s : State) s' op_step ts tr evs `(rx : _ -> proc _ _ TR) result,
    exec_tid op_step tid s (Bind p2 rx) s' result evs ->
    exec op_step s' (ts [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
    exec op_step s (ts [[tid := Proc (Bind p1 rx)]]) (prepend tid evs tr)) ->
  exec_equiv_rx p1 p2.
Proof.
  split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst; autorewrite with t in *.
      * repeat maybe_proc_inv. eauto.
      * eapply ExecOne with (tid := tid0).
          rewrite thread_upd_ne in * by auto. eauto.
          eauto.
        rewrite thread_upd_upd_ne by eauto.
        eapply IHexec.
        rewrite thread_upd_upd_ne; eauto.
    + exfalso; eauto.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      induction H; intros; subst
    end.
    + destruct (tid0 == tid); subst; autorewrite with t in *.
      * repeat maybe_proc_inv. eauto.
      * eapply ExecOne with (tid := tid0).
          autorewrite with t in *; eauto.
          eauto.
          rewrite thread_upd_upd_ne by eauto.
        eapply IHexec.
        rewrite thread_upd_upd_ne; auto.
    + exfalso; eauto.
Qed.

Theorem exec_equiv_ret_bind : forall `(v : T) `(p : T -> proc opT opHiT T'),
  exec_equiv_rx (Bind (Ret v) p) (p v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv; eauto.
  - rewrite <- app_nil_l with (l := evs).
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
Qed.

Theorem exec_equiv_atomicret_bind : forall `(v : T) `(p : T -> proc opT opHiT T'),
  exec_equiv_rx (Bind (Atomic (Ret v)) p) (p v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv.
    repeat atomic_exec_inv.
    eauto.
  - rewrite <- app_nil_l with (l := evs).
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
Qed.

Theorem exec_equiv_bind_bind : forall `(p1 : proc opT opHiT T1) `(p2 : T1 -> proc opT opHiT T2) `(p3 : T2 -> proc opT opHiT T3),
  exec_equiv_rx (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
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
        exec_tid_inv.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.

        destruct result0; eauto.

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
        exec_tid_inv.

        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t.

        destruct result; eauto.

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

Theorem exec_equiv_norx_bind_bind : forall `(p1 : proc opT opHiT T1) `(p2 : T1 -> proc opT opHiT T2) `(p3 : T2 -> proc opT opHiT T3),
  exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  intros.
  rewrite exec_equiv_bind_bind.
  reflexivity.
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
  exec_equiv_rx (Bind p1 (fun x => Bind (p2 x) (p3 x)))
             (Bind (Bind p1 (fun x => Bind (p2 x) (fun y => Ret (x, y))))
                   (fun p => p3 (fst p) (snd p))).
Proof.
  unfold exec_equiv_rx; intros.
  repeat rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  repeat rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  rewrite exec_equiv_ret_bind; simpl.
  reflexivity.
Qed.

Instance Bind_exec_equiv_proper :
  Proper (exec_equiv_rx ==>
          pointwise_relation T exec_equiv_rx ==>
          @exec_equiv_rx opT opHiT TR) Bind.
Proof.
  unfold exec_equiv_rx; intros.
  intros p1a p1b H1; intros.
  intros p2a p2b H2; intros.
  repeat rewrite exec_equiv_bind_bind.
  etransitivity.
  eapply H1.
  eapply exec_equiv_bind_a; intros.
  eapply H2.
Qed.

Theorem exec_equiv_ts_upd_same : forall `(ts : @threads_state opT opHiT) p tid,
  ts [[ tid ]] = p ->
  exec_equiv_ts ts (ts [[ tid := p ]]).
Proof.
  destruct p; intros.
  - rewrite thread_upd_same by eauto. reflexivity.
  - destruct (lt_dec tid (length ts)).
    + rewrite thread_upd_same' by eauto. reflexivity.
    + rewrite thread_upd_same'' by omega.
      eapply exec_equiv_ts_pad.
Qed.


(** A strong notion of equivalence for programs inside atomic sections.
    Basically the same as above, but defined as an underlying [atomic_exec]
    rather than [exec]. *)

Definition atomic_equiv `(p1 : proc opT opHiT T) p2 :=
  forall State op_step (s s' : State) r tid evs,
    atomic_exec op_step p1 tid s r s' evs <->
    atomic_exec op_step p2 tid s r s' evs.

Instance atomic_equiv_equivalence :
  Equivalence (@atomic_equiv opLoT opHiT T).
Proof.
  split.
  - firstorder.
  - unfold Symmetric, atomic_equiv; intros.
    split; intros; apply H; eauto.
  - unfold Transitive, exec_equiv_ts; intros.
    split; intros.
    + apply H0. apply H. eauto.
    + apply H. apply H0. eauto.
Qed.

Theorem atomic_equiv_ret_bind : forall `(v : T) `(p : T -> proc opT opHiT T'),
  atomic_equiv (Bind (Ret v) p) (p v).
Proof.
  split; intros.
  - atomic_exec_inv.
    inversion H9; clear H9; subst; repeat sigT_eq.
    eauto.
  - rewrite <- app_nil_l.
    eauto.
Qed.

Theorem atomic_equiv_bind_ret : forall `(p : proc opT opHiT T),
  atomic_equiv (Bind p Ret) p.
Proof.
  split; intros.
  - atomic_exec_inv.
    inversion H10; clear H10; subst; repeat sigT_eq.
    rewrite app_nil_r.
    eauto.
  - rewrite <- app_nil_r.
    eauto.
Qed.

Theorem atomic_equiv_bind_bind : forall `(p1 : proc opT opHiT T1) `(p2 : T1 -> proc opT opHiT T2) `(p3 : T2 -> proc opT opHiT T3),
  atomic_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  split; intros.
  - atomic_exec_inv.
    inversion H9; clear H9; subst; repeat sigT_eq.
    rewrite <- app_assoc.
    eauto.
  - atomic_exec_inv.
    inversion H10; clear H10; subst; repeat sigT_eq.
    rewrite app_assoc.
    eauto.
Qed.

Instance Atomic_proper_atomic_equiv :
  Proper (atomic_equiv ==> @exec_equiv_rx opT opHiT T) Atomic.
Proof.
  intros.
  intros p1 p2 H.
  eapply exec_equiv_rx_proof_helper; intros;
    repeat exec_tid_inv.
  - apply H in H7.
    eapply ExecOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t. eauto.
  - apply H in H7.
    eapply ExecOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t. eauto.
Qed.

Instance Bind_proper_atomic_equiv :
  Proper (atomic_equiv ==>
          pointwise_relation T atomic_equiv ==>
          @atomic_equiv opT opHiT TR) Bind.
Proof.
  intros.
  intros p1a p1b H1.
  intros p2a p2b H2.
  split; intros; atomic_exec_inv.
  - apply H1 in H11.
    apply H2 in H12.
    eauto.
  - apply H1 in H11.
    apply H2 in H12.
    eauto.
Qed.


(** Trace inclusion for an entire threads_state *)

Definition hitrace_incl_ts_s {opLo opHi State} op_step (s s' : State) (ts1 ts2 : @threads_state opLo opHi) :=
  forall tr,
    exec op_step s ts1 tr ->
    exists tr', exec op_step s' ts2 tr' /\
      trace_match_hi tr tr'.

Definition hitrace_incl_ts {opLo opHi State} op_step (ts1 ts2 : @threads_state opLo opHi) :=
  forall (s : State),
    hitrace_incl_ts_s op_step s s ts1 ts2.

Instance hitrace_incl_ts_s_preorder :
  PreOrder (@hitrace_incl_ts_s opT opHiT State op_step s s).
Proof.
  split.
  - unfold Reflexive.
    unfold hitrace_incl_ts_s; intros.
    eexists; intuition eauto.
  - unfold Transitive.
    unfold hitrace_incl_ts_s; intros.
    eapply H in H1. deex.
    eapply H0 in H1. deex.
    eexists; intuition eauto.
    etransitivity; eauto.
Qed.

Instance hitrace_incl_ts_preorder :
  PreOrder (@hitrace_incl_ts opT opHiT State op_step).
Proof.
  split.
  - unfold Reflexive, hitrace_incl_ts; intros.
    reflexivity.
  - unfold Transitive, hitrace_incl_ts; intros.
    etransitivity; eauto.
Qed.

Instance exec_equiv_ts_to_hitrace_incl_ts :
  subrelation (@exec_equiv_ts opT opHiT) (@hitrace_incl_ts opT opHiT State op_step).
Proof.
  unfold subrelation; intros.
  unfold hitrace_incl_ts, hitrace_incl_ts_s; intros.
  apply H in H0.
  eauto.
Qed.

Theorem hitrace_incl_ts_s_trans : forall `(s0 : State) s1 s2 `(op_step : OpSemantics opT State) `(ts1 : @threads_state opT opHiT) ts2 ts3,
  hitrace_incl_ts_s op_step s0 s1 ts1 ts2 ->
  hitrace_incl_ts_s op_step s1 s2 ts2 ts3 ->
  hitrace_incl_ts_s op_step s0 s2 ts1 ts3.
Proof.
  unfold hitrace_incl_ts_s; intros.
  apply H in H1. deex.
  apply H0 in H1. deex.
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
  forall (ts : @threads_state opT opHiT) tid,
    hitrace_incl_ts op_step
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

Instance hitrace_incl_s_preorder :
  PreOrder (@hitrace_incl_s State s s tid opT op_step opHiT T).
Proof.
  split.
  - unfold Reflexive; intros.
    unfold hitrace_incl_s; intros.
    reflexivity.
  - unfold Transitive; intros.
    unfold hitrace_incl_s; intros.
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

Instance exec_equiv_opt_to_hitrace_incl_opt :
  subrelation (@exec_equiv_opt opT opHiT) (@hitrace_incl_opt opT opHiT State op_step).
Proof.
  unfold subrelation; intros.
  unfold hitrace_incl_opt, hitrace_incl_ts, hitrace_incl_ts_s; intros.
  apply H in H0.
  eauto.
Qed.

Instance exec_equiv_to_hitrace_incl :
  subrelation (@exec_equiv opT opHiT T) (@hitrace_incl opT opHiT T State op_step).
Proof.
  unfold subrelation; intros.
  unfold hitrace_incl, hitrace_incl_opt, hitrace_incl_ts, hitrace_incl_ts_s; intros.
  apply H in H0.
  eauto.
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
          hitrace_incl_ts op_step) (@thread_upd opT opHiT).
Proof.
  intros.
  intros ts0 ts1 H; subst.
  intros tid tid' H; subst.
  intros p1 p2 H.

  unfold hitrace_incl_opt in H.
  eauto.
Qed.

Theorem hitrace_incl_s_trans : forall `(s0 : State) s1 s2 tid `(op_step : OpSemantics opT State) `(p1 : proc opT opHiT T) p2 p3,
  hitrace_incl_s s0 s1 tid op_step p1 p2 ->
  hitrace_incl_s s1 s2 tid op_step p2 p3 ->
  hitrace_incl_s s0 s2 tid op_step p1 p3.
Proof.
  unfold hitrace_incl_s; intros.
  eapply hitrace_incl_ts_s_trans; eauto.
Qed.

Lemma hitrace_incl_ts_proof_helper :
  forall `(p1 : proc opT opHiT T) (p2 : proc _ _ T) ts tid `(op_step : OpSemantics opT State),
  (forall ts s s' result tr evs,
    exec_tid op_step tid s p1 s' result evs ->
    exec op_step s' (ts [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
    exists tr',
      exec op_step s ts [[tid := Proc p2]] tr' /\
      trace_match_hi (prepend tid evs tr) tr') ->
  hitrace_incl_ts op_step
    (ts [[ tid := Proc p1 ]])
    (ts [[ tid := Proc p2 ]]).
Proof.
  unfold hitrace_incl_ts, hitrace_incl_ts_s.
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
      eauto.

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

Lemma hitrace_incl_proof_helper :
  forall `(p1 : proc opT opHiT T) p2 `(op_step : OpSemantics opT State),
  (forall tid ts s s' result tr evs,
    exec_tid op_step tid s p1 s' result evs ->
    exec op_step s' (ts [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
    exists tr',
      exec op_step s ts [[tid := Proc p2]] tr' /\
      trace_match_hi (prepend tid evs tr) tr') ->
  hitrace_incl op_step
    p1 p2.
Proof.
  unfold hitrace_incl, hitrace_incl_opt.
  intros.

  eapply hitrace_incl_ts_proof_helper.
  eauto.
Qed.

Lemma hitrace_incl_opret :
  forall `(p : T -> proc opT opHiT T') (v : T) `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (OpRet v) p)
    (p v).
Proof.
  intros.
  eapply hitrace_incl_proof_helper; intros.
  repeat exec_tid_inv.

  eexists; split.
  eauto.
  constructor.
Qed.

Lemma hitrace_incl_opcall :
  forall `(p : unit -> proc opT opHiT T') `(op : opT T) `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (OpCall op) p)
    (p tt).
Proof.
  intros.
  eapply hitrace_incl_proof_helper; intros.
  repeat exec_tid_inv.

  eexists; intuition eauto.
  constructor.
Qed.

Theorem hitrace_incl_opexec :
  forall `(p : T -> proc opT opHiT T') op `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (OpExec op) p)
    (Bind (Atomic (Op op)) p).
Proof.
  intros.
  eapply hitrace_incl_proof_helper; intros.
  repeat exec_tid_inv.

  eexists; split.

  eapply ExecOne with (tid := tid).
    autorewrite with t; eauto.
    eauto 20.
    autorewrite with t; eauto.

  simpl; eauto.
Qed.

Theorem hitrace_incl_atomize_opcall :
  forall `(op : opT T)
         `(p : _ -> proc opT opHiT TP)
         `(rx : _ -> proc opT opHiT TF)
         `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (Bind (OpCall op) (fun r => (Atomic (p r)))) rx)
    (Bind (Atomic (Bind (OpCall op) p)) rx).
Proof.
  intros.
  eapply hitrace_incl_proof_helper; intros.
  repeat exec_tid_inv.

  eapply hitrace_incl_ts_proof_helper in H0.
  deex.
  eexists; split.
  eassumption.
  eauto.

  intros.
  repeat exec_tid_inv.

  eexists; split.
  eapply ExecOne with (tid := tid).
    autorewrite with t; eauto.
    eauto.
    simpl. autorewrite with t. eauto.
  simpl; eauto.
Qed.

Theorem hitrace_incl_atomize_opret :
  forall `(v : T)
         `(p : _ -> proc opT opHiT TP)
         `(rx : _ -> proc opT opHiT TF)
         `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (Bind (OpRet v) (fun r => (Atomic (p r)))) rx)
    (Bind (Atomic (Bind (OpRet v) p)) rx).
Proof.
  intros.
  eapply hitrace_incl_proof_helper; intros.
  repeat exec_tid_inv.

  eapply hitrace_incl_ts_proof_helper in H0.
  deex.
  eexists; split.
  eassumption.
  eauto.

  intros.
  repeat exec_tid_inv.

  eexists; split.
  eapply ExecOne with (tid := tid).
    autorewrite with t; eauto.
    eauto.
    simpl. autorewrite with t. eauto.
  simpl; eauto.
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

Lemma hitrace_incl_atomic_bind :
  forall `(p1 : proc opT opHiT T)
         `(p2 : T -> proc opT opHiT T2)
         `(p3 : T2 -> proc opT opHiT T3)
         `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (Atomic (Bind p1 p2)) p3)
    (Bind (Bind (Atomic p1) (fun r => Atomic (p2 r))) p3).
Proof.
  intros.
  eapply hitrace_incl_proof_helper; intros.
  repeat exec_tid_inv.
  atomic_exec_inv.

  eexists; intuition eauto.
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
Qed.

Lemma hitrace_incl_atomic :
  forall `(p1 : proc opT opHiT T)
         `(p2 : T -> proc opT opHiT T2)
         `(op_step : OpSemantics opT State),
  hitrace_incl op_step
    (Bind (Atomic p1) p2)
    (Bind p1 p2).
Proof.
  intros.
  eapply hitrace_incl_proof_helper; intros.
  repeat exec_tid_inv.

  eexists; intuition eauto.

  generalize dependent p2.
  generalize dependent tr.

  match goal with
  | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
    induction H; intros; subst
  end.

  all: try solve [ eapply ExecOne with (tid := tid);
      [ autorewrite with t; eauto
      | eauto
      | autorewrite with t; eauto ] ].

  rewrite prepend_app.
  apply exec_equiv_norx_bind_bind.
  eauto.
Qed.


(** Correspondence between different layers *)

Definition traces_match_ts {opLoT opMidT opHiT State} lo_step hi_step
                           (ts1 : @threads_state opLoT opMidT)
                           (ts2 : @threads_state opMidT opHiT) :=
  forall (s : State) tr1,
    exec lo_step s ts1 tr1 ->
    exists tr2,
      exec hi_step s ts2 tr2 /\
      traces_match tr1 tr2.

Instance traces_match_ts_proper :
  Proper (@hitrace_incl_ts opLoT opMidT State lo_step ==>
          exec_equiv_ts ==>
          Basics.flip Basics.impl)
         (@traces_match_ts opLoT opMidT opHiT State lo_step hi_step).
Proof.
  intros.
  intros ts1 ts1' H1.
  intros ts2 ts2' H2.
  unfold Basics.flip, Basics.impl.
  unfold traces_match_ts; intros.
  apply H1 in H0. deex.
  apply H in H0. deex.
  apply H2 in H0.
  eexists; split. eauto.
  rewrite H3. eauto.
Qed.

Definition traces_match_one_thread opLoT opMidT opHiT State T
    (lo_step : OpSemantics opLoT State)
    (hi_step : OpSemantics opMidT State)
    (p1 : proc opLoT opMidT T)
    (p2 : proc opMidT opHiT T) :=
  traces_match_ts lo_step hi_step
    (threads_empty [[ 1 := Proc p1 ]])
    (threads_empty [[ 1 := Proc p2 ]]).

Instance traces_match_one_thread_proper :
  Proper (@hitrace_incl opLoT opMidT T State lo_step ==>
          @exec_equiv opMidT opHiT T ==>
          Basics.flip Basics.impl)
         (@traces_match_one_thread opLoT opMidT opHiT State T lo_step hi_step).
Proof.
  intros.
  intros p1 p1'; intros.
  intros p2 p2'; intros.
  unfold Basics.flip, Basics.impl; intros.
  unfold traces_match_one_thread in *; intros.
  rewrite H.
  rewrite H0.
  eauto.
Qed.

Instance traces_match_one_thread_proper_flip :
  Proper (Basics.flip (@hitrace_incl opLoT opMidT T State lo_step) ==>
          @exec_equiv opMidT opHiT T ==>
          Basics.impl)
         (@traces_match_one_thread opLoT opMidT opHiT State T lo_step hi_step).
Proof.
  intros.
  intros p1 p1'; intros.
  intros p2 p2'; intros.
  unfold Basics.flip, Basics.impl; intros.
  unfold traces_match_one_thread in *; intros.
  rewrite <- H.
  rewrite <- H0.
  eauto.
Qed.


(** Helpers for connecting different [threads_state]s *)

Definition proc_match `(R : forall T, proc opT opHiT T -> proc opT' opHiT' T -> Prop)
                      `(ts1 : @threads_state opT opHiT)
                      `(ts2 : @threads_state opT' opHiT') :=
  length ts1 = length ts2 /\
  forall tid,
    (ts1 [[ tid ]] = NoProc /\ ts2 [[ tid ]] = NoProc) \/
    exists T (p1 : proc _ _ T) p2,
    ts1 [[ tid ]] = Proc p1 /\ ts2 [[ tid ]] = Proc p2 /\ R T p1 p2.

Lemma proc_match_del : forall `(ts1 : @threads_state opT opHiT)
                              `(ts2 : @threads_state opT' opHiT') R tid,
  proc_match R ts1 ts2 ->
  proc_match R (ts1 [[ tid := NoProc ]]) (ts2 [[ tid := NoProc ]]).
Proof.
  unfold proc_match; intros.
  intuition idtac.
  - repeat rewrite length_thread_upd.
    congruence.
  - specialize (H1 tid0).
    destruct (tid == tid0); subst.
    + repeat rewrite thread_upd_eq; intuition eauto.
    + repeat rewrite thread_upd_ne by auto. intuition eauto.
Qed.

Lemma proc_match_upd : forall `(ts1 : @threads_state opT opHiT)
                              `(ts2 : @threads_state opT' opHiT') R tid
                              T (p1 : proc _ _ T) p2,
  proc_match R ts1 ts2 ->
  R _ p1 p2 ->
  proc_match R (ts1 [[ tid := Proc p1 ]]) (ts2 [[ tid := Proc p2 ]]).
Proof.
  unfold proc_match; intros.
  intuition idtac.
  - repeat rewrite length_thread_upd.
    congruence.
  - specialize (H2 tid0).
    destruct (tid == tid0); subst.
    + repeat rewrite thread_upd_eq.
      right.
      do 3 eexists.
      intuition eauto.
    + repeat rewrite thread_upd_ne by auto. intuition eauto.
Qed.

Lemma proc_match_nil : forall `(R : forall T, proc opT opHiT T -> proc opT' opHiT' T -> Prop),
  proc_match R nil nil.
Proof.
  unfold proc_match; intros.
  intuition eauto.
  left.
  repeat rewrite thread_get_nil; eauto.
Qed.

Lemma proc_match_cons_Proc : forall `(ts1 : @threads_state opT opHiT)
                                    `(ts2 : @threads_state opT' opHiT') R
                                    T (p1 : proc _ _ T) p2,
  proc_match R ts1 ts2 ->
  R _ p1 p2 ->
  proc_match R (Proc p1 :: ts1) (Proc p2 :: ts2).
Proof.
  unfold proc_match; intros.
  intuition idtac.
  - simpl; omega.
  - destruct tid.
    + right. do 3 eexists. intuition eauto.
    + repeat rewrite thread_get_S. eauto.
Qed.

Lemma proc_match_cons_NoProc : forall `(ts1 : @threads_state opT opHiT)
                                      `(ts2 : @threads_state opT' opHiT') R,
  proc_match R ts1 ts2 ->
  proc_match R (NoProc :: ts1) (NoProc :: ts2).
Proof.
  unfold proc_match; intros.
  intuition idtac.
  - simpl; omega.
  - destruct tid.
    + left. intuition eauto.
    + repeat rewrite thread_get_S. eauto.
Qed.

Lemma proc_match_cons_inv : forall `(ts1 : @threads_state opT opHiT)
                                   `(ts2 : @threads_state opT' opHiT') R
                                   v1 v2,
  proc_match R (v1 :: ts1) (v2 :: ts2) ->
  proc_match R ts1 ts2 /\
  (v1 = NoProc /\ v2 = NoProc \/
   exists T (p1 : proc _ _ T) p2,
   v1 = Proc p1 /\ v2 = Proc p2 /\ R T p1 p2).
Proof.
  unfold proc_match; simpl; intros.
  intuition idtac; try omega.
  - specialize (H1 (S tid)).
    repeat rewrite thread_get_S in H1.
    eauto.
  - specialize (H1 0).
    repeat rewrite thread_get_0 in H1.
    eauto.
Qed.

Definition proc_match_upto n `(R : forall T, proc opT opHiT T -> proc opT opHiT T -> Prop)
                             (ts1 ts2 : @threads_state opT opHiT) :=
  length ts1 = length ts2 /\
  forall tid,
    (tid < n ->
     (ts1 [[ tid ]] = NoProc /\ ts2 [[ tid ]] = NoProc) \/
     exists T (p1 : proc _ _ T) p2,
     ts1 [[ tid ]] = Proc p1 /\ ts2 [[ tid ]] = Proc p2 /\ R T p1 p2) /\
    (tid >= n ->
     ts1 [[ tid ]] = ts2 [[ tid ]]).

Theorem proc_match_upto_0_eq : forall `(ts1 : @threads_state opT opHiT) ts2 R,
  proc_match_upto 0 R ts1 ts2 ->
  ts1 = ts2.
Proof.
  unfold proc_match_upto;
    induction ts1.
  - destruct ts2; simpl in *; intuition eauto. congruence.
  - destruct ts2; simpl in *; intuition eauto. congruence.
    f_equal.
    + specialize (H1 0); intuition idtac.
      rewrite thread_get_0 in H2.
      rewrite thread_get_0 in H2.
      eauto.
    + apply IHts1 with (R := R); intuition.
      specialize (H1 (S tid)); intuition idtac.
      apply H3. eauto.
Qed.

Theorem proc_match_upto_0 : forall `(ts : @threads_state opT opHiT) R,
  proc_match_upto 0 R ts ts.
Proof.
  unfold proc_match_upto; intros.
  intuition idtac.
  omega.
Qed.

Theorem proc_match_upto_all : forall `(ts : @threads_state opT opHiT) ts' R,
  proc_match_upto (length ts) R ts ts' <->
  proc_match R ts ts'.
Proof.
  unfold proc_match_upto, proc_match; split; intros.
  - intuition idtac.
    specialize (H1 tid); intuition idtac.
    destruct (lt_dec tid (length ts)); intuition eauto.
    left; split.
    apply thread_get_oob. omega.
    apply thread_get_oob. omega.
  - intuition idtac.
    specialize (H1 tid); intuition idtac.
    repeat rewrite thread_get_oob by omega.
    eauto.
Qed.

Lemma proc_match_upto_Sn : forall `(ts : @threads_state opT opHiT) ts' R n,
  n < length ts ->
  proc_match_upto (S n) R ts ts' ->
  proc_match_upto n R ts (ts' [[ n := ts [[ n ]] ]]).
Proof.
  unfold proc_match_upto; intuition idtac.
  - rewrite H1 in *. rewrite length_thread_upd.
    edestruct Nat.max_spec; intuition eauto. omega.
  - specialize (H2 tid). destruct H2. destruct H2.
    omega.
    left. intuition idtac. destruct (n == tid); subst; autorewrite with t; eauto.
    repeat deex. right. do 3 eexists. intuition eauto.
    destruct (n == tid); try omega; subst; autorewrite with t; eauto.
  - destruct (n == tid); subst; autorewrite with t; eauto.
    specialize (H2 tid). intuition idtac.
    eapply H4. omega.
Qed.

Lemma proc_match_upto_Sn' : forall `(ts : @threads_state opT opHiT) ts' R n,
  n >= length ts ->
  proc_match_upto (S n) R ts ts' ->
  proc_match_upto n R ts ts'.
Proof.
  unfold proc_match_upto; intuition idtac.
  - specialize (H2 tid). destruct H2. destruct H2. omega.
    eauto. eauto.
  - repeat rewrite thread_get_oob by omega.
    eauto.
Qed.

Theorem proc_match_pick : forall tid `(ts1 : @threads_state opT opHiT)
                                     `(ts2 : @threads_state opT' opHiT') R,
  proc_match R ts1 ts2 ->
    (ts1 [[ tid ]] = NoProc /\ ts2 [[ tid ]] = NoProc) \/
    exists T (p1 : proc _ _ T) p2,
    ts1 [[ tid ]] = Proc p1 /\ ts2 [[ tid ]] = Proc p2 /\ R T p1 p2.
Proof.
  unfold proc_match; intuition eauto.
Qed.

Theorem proc_match_upto_pick : forall tid n
                                     `(ts1 : @threads_state opT opHiT) ts2 R,
  proc_match_upto n R ts1 ts2 ->
    (tid < n ->
     (ts1 [[ tid ]] = NoProc /\ ts2 [[ tid ]] = NoProc) \/
     exists T (p1 : proc _ _ T) p2,
     ts1 [[ tid ]] = Proc p1 /\ ts2 [[ tid ]] = Proc p2 /\ R T p1 p2) /\
    (tid >= n ->
     ts1 [[ tid ]] = ts2 [[ tid ]]).
Proof.
  unfold proc_match_upto; intuition idtac.
  - specialize (H1 tid). intuition eauto.
  - specialize (H1 tid). intuition eauto.
Qed.

Theorem proc_match_len : forall `(ts1 : @threads_state opT opHiT)
                                `(ts2 : @threads_state opT' opHiT') R,
  proc_match R ts1 ts2 ->
  length ts1 = length ts2.
Proof.
  unfold proc_match; intuition eauto.
Qed.

Theorem no_runnable_threads_proc_match : forall `(ts1 : @threads_state opT opHiT)
                                                `(ts2 : @threads_state opT' opHiT') R,
  no_runnable_threads ts1 ->
  proc_match R ts1 ts2 ->
  no_runnable_threads ts2.
Proof.
  unfold no_runnable_threads, proc_match; intuition idtac.
  specialize (H tid).
  specialize (H2 tid).
  intuition eauto.
  repeat deex; congruence.
Qed.

Hint Resolve no_runnable_threads_proc_match.
